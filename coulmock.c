/* coulmock.c - MOCK_LADDER support.
 *
 * Companion to lib/Calibrate/{Dickman,Ladder}.pm - C-side port used to
 * replace the WHOLE tau_multi_run() call (not individual tmfa[]
 * dispatches - see history below) with a cost-model lookup, so a
 * walk_v() call that would need real QS or many real deep-ECM
 * attempts can be simulated in a tiny fraction of the real time.
 *
 * DESIGN (revised - the first version of this file sampled a
 * probabilistic outcome per rung and fell through to the REAL
 * (*tmfa[i])(tm) call on a sampled success. hvds pointed out why
 * that's wrong: a probability isn't an actual outcome, and letting a
 * random sample decide whether to go and discover the REAL,
 * deterministic mathematical answer means the search's results would
 * depend on a coin flip rather than n's real properties - broken in a
 * way that corrupts more than just timing. Fixed by computing a
 * DETERMINISTIC expected cost for a whole tau_multi_run() call and
 * always returning "no candidate found" (0) - never discovering a
 * real candidate this way. That's fine: what this exists to validate
 * is aggregate TIMING behaviour, not to find real answers in a
 * mocked run - real runs still exist for that.):
 *
 *   1. For each of the `count` taum[] entries, walk the SAME
 *      rung-priority order (index order via tm->bits' bitmask,
 *      TM_INIT..TM_MAX) that the real tau_multi_run() would use.
 *   2. At each enabled rung, add (probability of REACHING this rung,
 *      i.e. having failed every earlier enabled rung) * (modelled
 *      cost of attempting this rung) to a running total - the same
 *      short-circuit-chain arithmetic Calibrate::Ladder.pm's
 *      expected_cost() does, just walked across the WHOLE bitmask
 *      instead of one named rung.
 *   3. Charge the summed total into g_mock_spent_s.
 *   4. Return 0 unconditionally - mock_tau_multi_run() never reports
 *      a candidate found, regardless of what the model's success
 *      probabilities were. A mocked run's *results* are therefore
 *      meaningless (it will never find real solutions); only its
 *      reported TIMING is meant to be trustworthy.
 *
 * KNOWN APPROXIMATION (this matters more than anything else here):
 * the real success probability for ECM/P-1 depends on the SMALLEST
 * FACTOR's size, which - unlike in rungbench, where we constructed
 * n=p*q ourselves - is genuinely unknown for a real candidate; that's
 * what factoring would tell us. This mock assumes the smallest factor
 * is uniform over [8, bits/2] as a placeholder - not derived from
 * Buchstab-function-style typical-smallest-factor theory, which would
 * be the principled thing to use instead. Until that's done, treat
 * MOCK_LADDER's aggregate predictions as a rough stand-in, not a
 * validated replacement for real escalation timing.
 *
 * Family boost constants and the two fitted cost curves are copied
 * from lib/Calibrate/Ladder.pm's %FAMILY_BOOST / %RUNGS by hand -
 * keep them in sync if that module gets recalibrated. See that
 * module's "known gaps" for the boost-constant caveats, which apply
 * here identically. QS (index 24) uses a small hardcoded chart
 * roughly matching WalkCost.pm's cost_simpqs_seconds() shape - not
 * copied precisely, since that module's chart wasn't reproduced here
 * byte-for-byte; treat this specifically as a rough placeholder even
 * relative to everything else in this file.
 */
#include <stdlib.h>
#include <stdio.h>
#include <math.h>
#include <gmp.h>
#include "coul.h"
#include "coultau.h"

#define MOCK_TM_INIT 2
#define MOCK_TM_MAX 43   /* matches coultau.c's TM_MAX (tmfa[] has
                             indices 0..42) - kept as a literal since
                             TM_MAX itself is a file-local macro in
                             coultau.c, not exported */

extern double g_mock_spent_s;

/* ---------------------------------------------------------------------
 * Dickman's rho function - see Calibrate::Dickman.pm for the reference
 * implementation and validation notes (matches published values to
 * 4+ significant figures). Same RK4-on-a-fixed-grid approach, computed
 * once at first use.
 * ------------------------------------------------------------------ */
#define RHO_STEP 0.001
#define RHO_MAXU 20.0
#define RHO_NMAX 20002   /* (int)(RHO_MAXU/RHO_STEP) + 2, as a literal -
                             the cast expression isn't a valid file-
                             scope array-size constant */
static double rho_grid[RHO_NMAX];
static int rho_n;
static bool rho_ready = 0;

static double rho_at(double u) {
    if (u <= 0) return 1.0;
    double idx = u / RHO_STEP;
    int i0 = (int)idx;
    if (i0 >= rho_n - 1) return rho_grid[rho_n - 1];
    double frac = idx - i0;
    return rho_grid[i0] * (1 - frac) + rho_grid[i0 + 1] * frac;
}

static void rho_init(void) {
    rho_n = (int)(RHO_MAXU / RHO_STEP) + 1;
    for (int i = 0; i < rho_n; ++i) {
        double u = i * RHO_STEP;
        rho_grid[i] = (u <= 1.0) ? 1.0 : 0.0;
    }
    for (int i = 1; i < rho_n; ++i) {
        double u = i * RHO_STEP;
        if (u <= 1.0) continue;
        double u_prev = (i - 1) * RHO_STEP;
        double k1 = -rho_at(u_prev - 1) / u_prev;
        double k2 = -rho_at(u_prev + RHO_STEP/2 - 1) / (u_prev + RHO_STEP/2);
        double k3 = k2;
        double k4 = -rho_at(u_prev + RHO_STEP - 1) / (u_prev + RHO_STEP);
        rho_grid[i] = rho_grid[i-1] + (RHO_STEP/6) * (k1 + 2*k2 + 2*k3 + k4);
        if (rho_grid[i] < 0) rho_grid[i] = 0.0;
    }
    rho_ready = 1;
}

static double dickman_rho(double u) {
    if (!rho_ready) rho_init();
    return rho_at(u);
}

/* ---------------------------------------------------------------------
 * Buchstab's omega function: omega(u) = 1/u for 1<=u<=2, and
 * (u*omega(u))' = omega(u-1) for u>2. Characterizes the density of
 * ROUGH numbers (no small prime factors) - the dual of Dickman's rho,
 * which characterizes SMOOTH numbers (no large prime factors). See
 * https://mathworld.wolfram.com/BuchstabFunction.html
 *
 * Relevant here because a residual reaching the escalation ladder
 * isn't a random integer - it's conditioned on having already
 * survived trial division up to tlim, i.e. it IS a tlim-rough number
 * by construction. Buchstab's function (via the sieve/Buchstab
 * identity Phi(x,y) = Phi(x,z) - sum_{y<=p<z} Phi(x/p,p)) gives the
 * honest distribution of such a number's smallest remaining prime
 * factor, in place of the uniform-over-[8,bits/2] placeholder this
 * file used before - see sample_factor_bits() below.
 *
 * Solved the same way as rho: RK4 on a fixed grid, computed once.
 * omega(u) oscillates and converges rapidly to exp(-gamma) as u
 * grows (gamma = Euler-Mascheroni, ~0.5772), which is a reasonable
 * sanity check on the numerics (matched to within 1% by u~15 in
 * testing this file's own grid).
 * ------------------------------------------------------------------ */
static double omega_grid[RHO_NMAX];
static int omega_n;
static bool omega_ready = 0;

static double omega_at(double u) {
    if (u <= 0) return 0.0;      /* omega is only defined for u>=1;
                                     callers only ever query u>=1 in
                                     practice, but 0 is a safe fallback
                                     rather than reading garbage */
    if (u < 1.0) return 1.0 / (u > 0.1 ? u : 0.1);
    double idx = u / RHO_STEP;
    int i0 = (int)idx;
    if (i0 >= omega_n - 1) return omega_grid[omega_n - 1];
    double frac = idx - i0;
    return omega_grid[i0] * (1 - frac) + omega_grid[i0 + 1] * frac;
}

static void omega_init(void) {
    omega_n = (int)(RHO_MAXU / RHO_STEP) + 1;
    for (int i = 0; i < omega_n; ++i) {
        double u = i * RHO_STEP;
        /* omega(u) = 1/u for 1<=u<=2; leave u<1 at 0 (unused, see
         * omega_at's u<1 fallback above) and u in (0,1) as a
         * placeholder since the DDE below only integrates from u=2 */
        omega_grid[i] = (u >= 1.0 && u <= 2.0) ? 1.0 / u : 0.0;
    }
    /* Integrate omega'(u) = (omega(u-1) - omega(u))/u forward from
     * u=2, via standard RK4 treating omega(u) as the evolving
     * solution (NOT a grid lookup mid-step, unlike rho's DDE above -
     * Buchstab's equation has omega(u) itself on the right-hand
     * side, so the k2/k3 stages need the RK4-estimated value at the
     * midpoint, not an interpolated lookup into a not-yet-computed
     * part of the grid). omega(u-1) is always a safe grid lookup,
     * since u-1 is a full unit behind and already computed. */
    for (int i = 1; i < omega_n; ++i) {
        double u = i * RHO_STEP;
        if (u <= 2.0) continue;
        double u_prev = (i - 1) * RHO_STEP;
        double y_prev = omega_grid[i - 1];
        double h = RHO_STEP;
        double k1 = (omega_at(u_prev - 1) - y_prev) / u_prev;
        double um = u_prev + h / 2;
        double k2 = (omega_at(um - 1) - (y_prev + h/2 * k1)) / um;
        double k3 = (omega_at(um - 1) - (y_prev + h/2 * k2)) / um;
        double ue = u_prev + h;
        double k4 = (omega_at(ue - 1) - (y_prev + h * k3)) / ue;
        omega_grid[i] = y_prev + (h / 6) * (k1 + 2*k2 + 2*k3 + k4);
    }
    omega_ready = 1;
}

static double buchstab_omega(double u) {
    if (!omega_ready) omega_init();
    return omega_at(u);
}

/* ---------------------------------------------------------------------
 * Private random source, used ONLY to sample a stand-in factor size
 * (see "known approximation" above) - never to decide an outcome. No
 * outcome in this file is ever sampled; every probability computed
 * here feeds into a deterministic expected-value sum instead.
 * ------------------------------------------------------------------ */
static unsigned long mock_rand_state = 0x853c49e6748fea9bUL;
static double mock_rand_uniform(void) {
    mock_rand_state ^= mock_rand_state << 13;
    mock_rand_state ^= mock_rand_state >> 7;
    mock_rand_state ^= mock_rand_state << 17;
    return (double)(mock_rand_state >> 11) / (double)(1UL << 53);
}

#define BOOST_ECM 27.3
#define BOOST_P1  25.8
#define SHARED_COST_K 0.9253

static double p_success_ecm_or_p1(ulong B1, uint curves, double factor_bits,
        bool is_p1) {
    double boost = is_p1 ? BOOST_P1 : BOOST_ECM;
    double u = (factor_bits * log(2)) / log((double)B1 * boost);
    double single = dickman_rho(u);
    return 1.0 - pow(1.0 - single, curves);
}

static double cost_A_for(ulong B1, uint curves, bool is_p1) {
    if (is_p1 && B1 == 5000000) return 0.0109464;
    if (!is_p1 && B1 == 200 && curves == 4)
        return 4394034e-9 / pow(200, SHARED_COST_K);
    if (!is_p1 && B1 == 5000 && curves == 20)
        return 322022370e-9 / pow(300, SHARED_COST_K);
    if (!is_p1 && B1 == 40000 && curves == 40)
        return 4317003004e-9 / pow(300, SHARED_COST_K);
    return (322022370e-9 / pow(300, SHARED_COST_K)) * curves / 20.0;
}

/* Roughness threshold used by tau_multi_prep()'s trial division under
 * MPUG_054 (tlim = 64007^2, so primes are tested up to 64007 ~ 2^16 -
 * see coultau.c). A residual reaching this rung is, by construction,
 * this-rough: it has already survived trial division up to here. */
#define ROUGH_Y_BITS 16.0

/* Buchstab-weighted sample of the smallest remaining prime factor's
 * bit-size, replacing the old uniform-over-[8,bits/2] placeholder.
 * Via the Buchstab sieve identity (Phi(x,y) = Phi(x,z) -
 * sum_{y<=p<z} Phi(x/p,p)), the density of a y-rough n<=x having
 * smallest factor near p is proportional to Phi(x/p,p), and
 * Phi(x/p,p) ~ (x/p)*omega(v)/log(p) with v = log(x/p)/log(p). In
 * bit-size terms (p_bits = log2(p), bits = log2(x)), that density
 * (up to normalization, and treating the 1/log(p) term as roughly
 * constant across the discretization step used here) is weighted by
 * omega(v) with v = (bits - p_bits)/p_bits. Discretized over
 * candidate p_bits from ROUGH_Y_BITS to bits/2 and sampled via
 * inverse-CDF - simpler than a fully continuous treatment, and
 * doesn't carry the exact 1/log(p) Jacobian factor, but captures the
 * qualitatively important shift (smallest factor concentrated nearer
 * the roughness threshold, not spread uniformly across the whole
 * range) that the uniform placeholder was missing entirely. */
#define FACTOR_BITS_BUCKETS 64
static double sample_factor_bits(uint n_bits) {
    double lo = ROUGH_Y_BITS, hi = n_bits / 2.0;
    if (hi <= lo) return lo;
    double weights[FACTOR_BITS_BUCKETS];
    double total = 0;
    double step = (hi - lo) / FACTOR_BITS_BUCKETS;
    for (int i = 0; i < FACTOR_BITS_BUCKETS; ++i) {
        double p_bits = lo + (i + 0.5) * step;
        double v = (n_bits - p_bits) / p_bits;
        weights[i] = buchstab_omega(v);
        total += weights[i];
    }
    double r = mock_rand_uniform() * total;
    for (int i = 0; i < FACTOR_BITS_BUCKETS; ++i) {
        r -= weights[i];
        if (r <= 0)
            return lo + (i + 0.5) * step;
    }
    return hi;   /* fallback for floating-point edge cases */
}

struct fixed_method { double mean_ns; double p_success; uint cutoff_bits; };
static const struct fixed_method FIXED_METHODS[MOCK_TM_MAX] = {
    [2]  = { 450,       0.0,  70 },
    [4]  = { 20000000,  0.5,  150 },
    [5]  = { 3500000,   0.0,  100 },
    [10] = { 500,       0.0,  100 },
    [26] = { 120000000, 0.0,  0   },
    [29] = { 100000000, 0.0,  0   },
    [30] = { 16000000,  0.03, 0   },
};

struct ecm_p1_params { ulong B1; uint curves; bool is_p1; uint B1_mult; bool sets_b1; };
static const struct ecm_p1_params ECM_P1[MOCK_TM_MAX] = {
    [3]  = {5000, 5, 1, 0, 0},        [6]  = {1000, 10, 1, 0, 0},
    [7]  = {2000, 20, 1, 0, 0},       [8]  = {4000, 40, 1, 0, 0},
    [9]  = {10000, 100, 1, 0, 0},     [11] = {20000, 200, 1, 0, 0},
    [12] = {200, 4, 0, 0, 0},         [13] = {600, 20, 0, 0, 0},
    [14] = {2000, 10, 0, 0, 0},       [15] = {200000, 3000000, 1, 0, 0},
    [16] = {5000, 20, 0, 0, 1},       [17] = {10000, 2, 0, 0, 1},
    [18] = {20000, 2, 0, 0, 1},       [19] = {30000, 20, 0, 0, 1},
    [20] = {40000, 40, 0, 0, 1},      [21] = {80000, 40, 0, 0, 1},
    [22] = {160000, 80, 0, 0, 1},     [23] = {320000, 160, 0, 0, 1},
    [25] = {0, 20, 0, 2, 0},          [27] = {0, 20, 0, 4, 0},
    [28] = {0, 40, 0, 8, 0},          [31] = {5000000, 100000000, 1, 0, 0},
    [32] = {0, 40, 0, 32, 0},
};

/* Rough QS chart, v0.54-ish cpu_scale already folded in - NOT copied
 * precisely from WalkCost.pm's cost_simpqs_seconds(); see file header. */
static double qs_cost_seconds(uint bits) {
    static const uint chart_bits[] = {100, 160, 200, 220};
    static const double chart_s[]  = {0.06, 0.30, 5.0, 27.0};
    int n = sizeof(chart_bits) / sizeof(chart_bits[0]);
    if (bits <= chart_bits[0]) return chart_s[0];
    if (bits >= chart_bits[n-1]) return chart_s[n-1];
    for (int i = 1; i < n; ++i) {
        if (bits <= chart_bits[i]) {
            double frac = (double)(bits - chart_bits[i-1])
                / (chart_bits[i] - chart_bits[i-1]);
            return chart_s[i-1] + frac * (chart_s[i] - chart_s[i-1]);
        }
    }
    return chart_s[n-1];
}

/* Cost and success probability for ONE attempt at rung i, on a
 * candidate of the given bits and (for ECM/P-1) a freshly-sampled
 * stand-in factor size. tm->B1 is read/written here exactly as the
 * real tmf_16..23/25/27/28/32 functions would, so the relative-B1
 * chain stays correct across successive rungs within one candidate. */
/* Diagnostic per-family accumulators, to isolate which model
 * component actually dominates g_mock_spent_s - added specifically to
 * find the source of the ~11x aggregate overestimate found via the
 * windowed real-vs-mock comparison (family index: 0=ecm, 1=p1,
 * 2=qs, 3=fixed-empirical). */
double g_mock_family_s[4];

/* ---------------------------------------------------------------------
 * Bracket lookup - needed to determine which rungs are enabled for a
 * candidate's bit-size after a shape reduction recurses into a new,
 * smaller residual. Uses coultau.c's own tmfbl[] table via a
 * safety-checked accessor (get_tmfbl) rather than a hand-copied
 * duplicate - a first version of this file DID duplicate the table
 * locally, which hvds pointed out was both a staleness risk and, it
 * turned out, actually WRONG: it missed the "flake" masking
 * init_tmfbl() can apply (stripping high-numbered rungs like QS above
 * a threshold), which the real table's tmfbl[]/tmfb_lim already
 * account for. */
extern const ulong *get_tmfbl(uint *out_maxb, ulong *out_lim);

static ulong mock_find_tmfb(uint bits) {
    static const ulong *tmfbl_ptr = NULL;
    static uint maxb;
    static ulong lim;
    if (!tmfbl_ptr)
        tmfbl_ptr = get_tmfbl(&maxb, &lim);
    return (bits <= maxb) ? tmfbl_ptr[bits] : lim;
}

/* Divisors of t, needed for the compatibility split below. Small t
 * values only (tau targets are never huge), simple O(sqrt(t)) is
 * plenty. */
#define MAX_DIVISORS 64
static int divisors_of(uint t, uint *divs) {
    int n = 0;
    for (uint d = 1; (ulong)d * d <= t; ++d) {
        if (t % d) continue;
        if (n < MAX_DIVISORS) divs[n++] = d;
        uint d2 = t / d;
        if (d2 != d && n < MAX_DIVISORS) divs[n++] = d2;
    }
    return n;
}

/* Given a prime of size 2^p_bits was just found (rung succeeded),
 * split into P(incompatible - triggers a whole-batch abort) and, for
 * each divisor j>=2 of t, P(compatible via multiplicity j-1). Exact
 * geometric law: for tm->e==1 (not tracking tm->e's own effect on e
 * here - see caveat below), e = mult+1, P(mult=k) = (1/p)^(k-1)*(1-1/p).
 * hvds (chat): "we should have a uniform distribution over values mod
 * p and over values mod p^2 etc, for every p not in our list of
 * allocations" - for nqc==0 this is exact, not a heuristic (ati sweeps
 * uniformly and qq[vi] is coprime to any such p). NOT verified for
 * nqc>0 (have_square/Pell branch) - flagged as open, per hvds.
 *
 * CAVEAT: ignores tm->e (the running power-found exponent from earlier
 * need_square resolution) - assumes e=mult+1 rather than the general
 * e=mult*tm->e+1. Only matters for candidates that already went
 * through a square-power step before reaching here; not modelled yet. */
struct compat_result {
    double p_incompatible;
    int n_compat;
    uint compat_j[MAX_DIVISORS];
    double compat_p[MAX_DIVISORS];
};

static void compatibility_split(double p_bits, uint t, struct compat_result *out) {
    double p = pow(2.0, p_bits);
    double q = 1.0 - 1.0 / p;   /* P(mult exactly k) = (1/p)^(k-1) * q */
    uint divs[MAX_DIVISORS];
    int ndivs = divisors_of(t, divs);
    out->n_compat = 0;
    double p_compat_total = 0;
    for (int i = 0; i < ndivs; ++i) {
        uint j = divs[i];
        if (j < 2) continue;   /* j=1 (mult=0, i.e. no factor at all)
                                   isn't a valid outcome here - we're
                                   already conditioning on a factor
                                   having been found */
        int mult = j - 1;
        double p_this = pow(1.0 / p, mult - 1) * q;
        if (out->n_compat < MAX_DIVISORS) {
            out->compat_j[out->n_compat] = j;
            out->compat_p[out->n_compat] = p_this;
            ++out->n_compat;
        }
        p_compat_total += p_this;
    }
    out->p_incompatible = 1.0 - p_compat_total;
    if (out->p_incompatible < 0) out->p_incompatible = 0;   /* numerical
        safety - shouldn't go negative, but t itself being very smooth
        (many small divisors) pushes p_compat_total close to 1 */
}

static void rung_model(uint i, t_tm *tm, uint bits, double factor_bits,
        double *cost_s, double *p_succ, int *family) {
    if (i < MOCK_TM_MAX && ECM_P1[i].curves) {
        const struct ecm_p1_params *p = &ECM_P1[i];
        ulong B1 = p->B1_mult ? tm->B1 * p->B1_mult : p->B1;
        if (p->sets_b1)
            tm->B1 = B1;
        *p_succ = p_success_ecm_or_p1(B1, p->curves, factor_bits, p->is_p1);
        *cost_s = cost_A_for(B1, p->curves, p->is_p1) * pow(bits, SHARED_COST_K);
        *family = p->is_p1 ? 1 : 0;
        return;
    }
    if (i == 24) {
        *cost_s = qs_cost_seconds(bits);
        *p_succ = 1.0;   /* QS is general-purpose - treat as reliable
                             once reached, ending the chain here */
        *family = 2;
        return;
    }
    if (i < MOCK_TM_MAX && FIXED_METHODS[i].mean_ns > 0) {
        const struct fixed_method *f = &FIXED_METHODS[i];
        *family = 3;
        if (f->cutoff_bits && bits > f->cutoff_bits) {
            *cost_s = 0;
            *p_succ = 0;
            return;
        }
        *cost_s = f->mean_ns / 1e9;
        *p_succ = f->p_success;
        return;
    }
    *family = 3;
    /* no model for this index - treat as free/no-op rather than
     * silently wrong. Only reachable for indices this table doesn't
     * cover at all (e.g. TRY_HARDER-only tmf_33..42, or anything
     * added to coultau.c since this was written). */
    *cost_s = 0;
    *p_succ = 0;
}

static void report_family_breakdown(void) {
    fprintf(stderr, "MOCK_FAMILY_BREAKDOWN ecm=%.6f p1=%.6f qs=%.6f fixed=%.6f total=%.6f\n",
        g_mock_family_s[0], g_mock_family_s[1], g_mock_family_s[2],
        g_mock_family_s[3], g_mock_spent_s);
}

#define MAX_RECURSE_DEPTH 20

struct outcome_result {
    double cost;             /* expected total cost for one full pass
                                 of this candidate's chain, INCLUDING
                                 any recursive shape-reduction steps */
    double p_causes_abort;   /* probability this candidate eventually
                                 triggers a whole-batch incompatible-
                                 success abort, at some point in its
                                 own chain (including recursive steps) */
};

/* Recursive per-candidate expected cost, following tau_multi_run()'s
 * OWN behaviour precisely: a compatible-but-not-fully-resolved success
 * (t reduces to something other than 1 or 2) restarts the WHOLE ladder
 * from the cheapest rung with the new, smaller shape (t/j, reduced
 * bits) - exactly matching the real goto tmr_retry.
 *
 * KNOWN GAPS in this recursive step (beyond the ones already flagged
 * on compatibility_split() and sample_factor_bits()):
 *   - tm->B1 chaining is NOT preserved across a recursive re-entry - a
 *     fresh candidate_outcome() call starts as if B1 had never been
 *     set, same as a genuinely fresh residual would, which is only
 *     approximately right (the real code's tm->B1 persists across the
 *     goto tmr_retry, so relative-B1 rungs early in the NEW pass could
 *     in principle inherit a stale large B1 from the PREVIOUS pass -
 *     not modelled).
 *   - t==1 (need n==1 exactly) and t==2 (need remaining n prime)
 *     resolution are both treated as free/certain rather than costed -
 *     the real ct_prime() check has some real (probably small) cost
 *     this doesn't charge for.
 *   - only verified theoretically for nqc==0 (see compatibility_split);
 *     not extended to the have_square/Pell branch.
 */
static struct outcome_result candidate_outcome(uint t, uint bits, int depth) {
    struct outcome_result result = {0.0, 0.0};
    if (depth > MAX_RECURSE_DEPTH || t <= 2)
        return result;   /* t==1/2 resolution cost not modelled - see
                             "known gaps"; depth cutoff is a safety net,
                             not expected to bind in practice */

    ulong bitmask = mock_find_tmfb(bits);
    double reach_prob = 1.0;
    t_tm dummy_tm;
    dummy_tm.B1 = 0;   /* fresh state each call - see "known gaps" on
                           B1 chaining across recursive re-entry */

    for (uint i = MOCK_TM_INIT; i < MOCK_TM_MAX; ++i) {
        if (!(bitmask & (1UL << i)))
            continue;
        double bits_d = bits;
        double factor_bits = sample_factor_bits(bits);
        double cost_s, p_succ;
        int family;
        rung_model(i, &dummy_tm, bits, factor_bits, &cost_s, &p_succ, &family);

        double contribution = reach_prob * cost_s;
        result.cost += contribution;
        g_mock_family_s[family] += contribution;

        if (p_succ > 0) {
            struct compat_result cr;
            compatibility_split(factor_bits, t, &cr);

            result.p_causes_abort += reach_prob * p_succ * cr.p_incompatible;

            for (int k = 0; k < cr.n_compat; ++k) {
                uint j = cr.compat_j[k];
                double p_this = reach_prob * p_succ * cr.compat_p[k];
                uint new_t = t / j;
                double reduced = bits_d - (j - 1) * factor_bits;
                uint new_bits = (reduced > 8) ? (uint)reduced : 8;
                if (new_t <= 2) {
                    /* fully resolved (or needs only a primality check) -
                       see "known gaps": treated as free/certain */
                    continue;
                }
                struct outcome_result sub =
                    candidate_outcome(new_t, new_bits, depth + 1);
                result.cost += p_this * sub.cost;
                result.p_causes_abort += p_this * sub.p_causes_abort;
            }
        }
        reach_prob *= (1.0 - p_succ);
        if (reach_prob <= 1e-12)
            break;
    }
    return result;
}

uint mock_tau_multi_run(uint count, tau_failure_handler tfh) {
    static bool registered = 0;
    if (!registered) {
        atexit(report_family_breakdown);
        registered = 1;
    }
    (void)tfh;   /* never invoked - see file header: this never
                    reports a real failure/candidate outcome, and
                    never needs the failure handler either */

    /* Cross-candidate joint survival: tau_multi_run() processes every
     * candidate in the SAME batch rung-major, and the moment ANY one
     * of them hits an incompatible success, the WHOLE batch aborts
     * (return count) - hvds (chat): "we should not reach [an expensive
     * rung] unless *all* the numbers have either failed all previous
     * rungs or have been found to match the required tau." Modelled
     * here as the product, across all candidates, of "this candidate
     * never causes an abort" - an approximation (it ignores the exact
     * rung-major interleaving order, treating each candidate's own
     * abort probability as independent of when in the sequence other
     * candidates are processed), but a large improvement over the
     * previous per-candidate-independent model, which didn't apply
     * this filter at all. */
    double total_s = 0;
    double batch_survival = 1.0;
    for (uint j = 0; j < count; ++j) {
        t_tm *tm = &taum[j];
        uint bits = mpz_sizeinbase(tm->n, 2);
        struct outcome_result r = candidate_outcome(tm->t, bits, 0);
        total_s += r.cost;
        batch_survival *= (1.0 - r.p_causes_abort);
    }
    g_mock_spent_s += total_s * batch_survival;
    /* IMPORTANT: 0 means "every entry validated successfully" in this
     * codebase's convention (tau_multi_run() only returns 0 when
     * count has been decremented to 0 via successful splices, or
     * trivially when there was nothing to check at all) - the
     * opposite of what it looks like at first glance. Returning
     * count directly handles both cases correctly: count==0 (nothing
     * was ever passed in - a genuine, correct vacuous success, not
     * the bug) returns 0 exactly as the real function would; count>0
     * (there ARE real entries this mock is simulating rather than
     * validating) returns nonzero, correctly signalling rejection
     * rather than the unconditional false success the first working
     * version of this function produced - which is how it produced a
     * "solution" where 2 of the 5 required positions didn't actually
     * have the right tau. */
    return count;
}
