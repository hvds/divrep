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
 * always reporting rejection - never discovering a real candidate
 * this way. That's fine: what this exists to validate
 * is aggregate TIMING behaviour, not to find real answers in a
 * mocked run - real runs still exist for that.):
 *
 *   1. Skip entries tau_multi_prep() already resolved (state == 0),
 *      as the real code does; if none remain, return 0 as it does.
 *   2. Expand each remaining entry's chain (see candidate_chain())
 *      into events tagged with their rung-major slot: expected
 *      attempts, cost, and probability of aborting the whole batch,
 *      each conditioned on the entry's own history.
 *   3. Walk the events in rung-major order (slot, then the real
 *      qsort order of entries), weighting each by the probability
 *      that no OTHER entry has aborted the batch yet, and charge the
 *      sum into g_mock_spent_s. An aborted batch still costs what was
 *      spent before the abort - an earlier version multiplied the
 *      whole un-truncated cost by P(no abort), charging aborted
 *      batches nothing, which collapsed the total towards 0.
 *   4. Return count (rejection). A mocked run's *results* are
 *      therefore meaningless; only its TIMING is modelled.
 *
 * Validation: build the real binary with LADDER_STATS=1 and compare
 * its LADDER_STATS/LADDER_BUCKET lines with this file's
 * MOCK_LADDER_STATS/MOCK_LADDER_BUCKET lines for the same run.
 *
 * The smallest factor's size is sampled from the Buchstab-weighted
 * distribution of a y-rough number (see sample_factor_bits()).
 *
 * Family boost constants and the two fitted cost curves are copied
 * from lib/Calibrate/Ladder.pm's %FAMILY_BOOST / %RUNGS by hand -
 * keep them in sync if that module gets recalibrated. See that
 * module's "known gaps" for the boost-constant caveats, which apply
 * here identically. The P-1 cost, brent63 and tinyqs models are
 * fitted separately, from rungbench - see their own comments.
 * QS (index 24) uses a small hardcoded chart
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

#ifndef M_PI
#   define M_PI 3.14159265358979323846
#endif

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

static double p_success_ecm(ulong B1, uint curves, double factor_bits) {
    double u = (factor_bits * log(2)) / log((double)B1 * BOOST_ECM);
    double single = dickman_rho(u);
    return 1.0 - pow(1.0 - single, curves);
}

/* P-1 is a single deterministic attempt, not repeated curves:
 * Ladder.pm models it with curves => 1 (an earlier version of this
 * file put B2 - or for some rungs B2/1000 - in the curves slot, making
 * 1-(1-rho)^curves ~ 1 for every P-1 rung, and the cost fallback
 * B2/20 times an ECM anchor). The boost stands in for stage 2's
 * extension of the smoothness bound and was fitted only at
 * B2/B1 = 20 (p1_5M_100M); scale it by (B2/B1)/20, floored at 1
 * (B2 == B1 means no stage 2 at all). PLACEHOLDER beyond that one
 * fitted point. */
static double p_success_p1(ulong B1, ulong B2, double factor_bits) {
    double boost = BOOST_P1 * ((double)B2 / (double)B1) / 20.0;
    if (boost < 1.0)
        boost = 1.0;
    double u = (factor_bits * log(2)) / log((double)B1 * boost);
    return dickman_rho(u);
}

/* ECM cost ~ B1 * curves, scaled from whichever Ladder.pm anchor is
 * nearest in log(B1). The previous fallback scaled by curves only, so
 * e.g. B1=320000 was costed as if B1=5000. */
struct ecm_anchor { ulong B1; uint curves; double s; uint at_bits; };
static const struct ecm_anchor ECM_ANCHOR[] = {
    {   200,  4,    4394034e-9, 200 },
    {  5000, 20,  322022370e-9, 300 },
    { 40000, 40, 4317003004e-9, 300 },
};
static double cost_ecm_s(ulong B1, uint curves, uint bits) {
    const struct ecm_anchor *best = &ECM_ANCHOR[0];
    double bd = 1e300;
    for (uint k = 0; k < sizeof(ECM_ANCHOR) / sizeof(ECM_ANCHOR[0]); ++k) {
        double d = fabs(log((double)B1 / ECM_ANCHOR[k].B1));
        if (d < bd) {
            bd = d;
            best = &ECM_ANCHOR[k];
        }
    }
    return best->s * ((double)B1 * curves) / ((double)best->B1 * best->curves)
        * pow((double)bits / best->at_bits, SHARED_COST_K);
}

/* P-1 full-attempt (failure) cost, fitted to rungbench rand-mode
 * mean_ns_fail for tmf_3/6/7/8/9/11/15 at 64-192 bits (2026-09-24,
 * MPUGMP 2389dcbc44): cost = (32.8ns * B1 + 6.77ns * B2) at 128 bits,
 * within ~15% for all seven rungs; bits scaling matches the shared
 * 0.9253 exponent between 96 and 192 bits. The same formula predicts
 * 0.84s for 5M/100M at 128 bits vs Ladder.pm's separately fitted
 * 0.97s. Replaces an ECM-anchor fallback that scaled by B2/20. */
static double cost_p1_s(ulong B1, ulong B2, uint bits) {
    return (32.8e-9 * B1 + 6.77e-9 * B2) * pow(bits / 128.0, SHARED_COST_K);
}

/* A success costs much less than a full failed attempt: rungbench
 * shows P-1 successes at ~0.05-0.1 of the failure cost (factors are
 * mostly found by early stage-1 gcds). ECM keeps Ladder.pm's first-
 * pass 0.5 (hvds: "an initial estimate of success cost as half of
 * failure cost"). */
#define SUCCESS_FRAC_P1  0.1
#define SUCCESS_FRAC_ECM 0.5

/* brent63 (tmf_2, 400000 rounds): only runs for n <= 63 bits (returns
 * immediately otherwise - pbrent63.c). Rho needs ~sqrt(pi*p/2)
 * iterations for smallest factor p; ~10ns/iteration is consistent
 * with LADDER_STATS (~50-70us mean at 48-63 bits, where the
 * Buchstab-sampled factor is ~2^24). */
#define BRENT63_ROUNDS 400000.0
#define BRENT63_ITER_S 10e-9
static void model_brent63(uint bits, double factor_bits,
        double *cost_s, double *p_succ) {
    if (bits > 63) {
        *cost_s = 0.5e-6;
        *p_succ = 0;
        return;
    }
    double need = sqrt(M_PI / 2 * pow(2.0, factor_bits));
    double x = BRENT63_ROUNDS * BRENT63_ROUNDS / (2 * pow(2.0, factor_bits));
    *p_succ = 1.0 - exp(-x);
    *cost_s = 1e-6 + BRENT63_ITER_S
        * ((need < BRENT63_ROUNDS) ? need : BRENT63_ROUNDS);
}

/* tinyqs (tmf_4): cost and success by bits from rungbench rand mode
 * (mean_ns_all, n=30 per point); its config table caps at 116 bits,
 * beyond which success collapses. Interpolated in log(cost). */
static void model_tinyqs(uint bits, double *cost_s, double *p_succ) {
    static const uint   tb[] = { 64,   72,   80,   88,   96,   104,  112,  116,  124 };
    static const double tc[] = { 0.57, 0.64, 0.95, 1.70, 4.20, 5.95, 9.76, 16.8, 20.5 };
    static const double tp[] = { 0.95, 0.95, 0.95, 0.95, 0.97, 0.97, 0.93, 0.77, 0.2 };
    const int n = sizeof(tb) / sizeof(tb[0]);
    if (bits >= tb[n - 1] + 8) {
        *cost_s = tc[n - 1] * 1e-3;
        *p_succ = 0;
        return;
    }
    if (bits <= tb[0]) {
        *cost_s = tc[0] * 1e-3;
        *p_succ = tp[0];
        return;
    }
    int k = 1;
    while (k < n - 1 && bits > tb[k])
        ++k;
    if (bits > tb[k]) {     /* between tb[n-1] and tb[n-1]+8 */
        *cost_s = tc[k] * 1e-3;
        *p_succ = tp[k];
        return;
    }
    double f = (double)(bits - tb[k - 1]) / (tb[k] - tb[k - 1]);
    *cost_s = exp(log(tc[k - 1]) + f * (log(tc[k]) - log(tc[k - 1]))) * 1e-3;
    *p_succ = tp[k - 1] + f * (tp[k] - tp[k - 1]);
}

/* Roughness bound y (in bits) that tau_multi_prep()'s trial division
 * guarantees for a residual reaching the ladder: primes are tested up
 * to sqrt(tlim), i.e. 64007 under MPUG_054, otherwise 4001 for
 * nbits > 80 and 16001 below (see coultau.c). Previously hardcoded to
 * the MPUG_054 value regardless of build. Uses the residual's bits in
 * place of prep's original nbits, and ignores test_rough. */
static double rough_y_bits(uint n_bits) {
#ifdef MPUG_054
    (void)n_bits;
    return 15.97;
#else
    return (n_bits > 80) ? 11.97 : 13.97;
#endif
}

/* P(a y-rough composite-free cofactor of n_bits is prime): by Mertens,
 * P(y-rough) ~ e^-gamma / ln y, so P(prime | y-rough) ~ e^gamma *
 * ln(y) / ln(n) = e^gamma * y_bits / n_bits. Capped below 1. */
static double p_cofactor_prime(uint n_bits) {
    double p = 1.7810724 * rough_y_bits(n_bits) / (n_bits ? n_bits : 1);
    return (p > 0.95) ? 0.95 : p;
}

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
 * candidate p_bits from rough_y_bits() to bits/2 and sampled via
 * inverse-CDF - simpler than a fully continuous treatment, and
 * doesn't carry the exact 1/log(p) Jacobian factor, but captures the
 * qualitatively important shift (smallest factor concentrated nearer
 * the roughness threshold, not spread uniformly across the whole
 * range) that the uniform placeholder was missing entirely. */
#define FACTOR_BITS_BUCKETS 64
static double sample_factor_bits(uint n_bits) {
    double lo = rough_y_bits(n_bits), hi = n_bits / 2.0;
    if (hi <= lo) return lo;
    double weights[FACTOR_BITS_BUCKETS];
    double total = 0;
    double step = (hi - lo) / FACTOR_BITS_BUCKETS;
    for (int i = 0; i < FACTOR_BITS_BUCKETS; ++i) {
        double p_bits = lo + (i + 0.5) * step;
        double v = (n_bits - p_bits) / p_bits;
        /* per-bit density of the smallest factor of a y-rough n:
         * (#primes per bit ~ 2^b/b) * (Phi(x/p,p) ~ (x/p)*omega(v)/b)
         * gives omega(v)/b^2. The 1/b^2 was previously dropped, which
         * spread the smallest factor ~uniformly over [y, bits/2] -
         * far too large (by Mertens, P(smallest > z bits) ~ y/z). */
        weights[i] = buchstab_omega(v) / (p_bits * p_bits);
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
    /* [2] brent63 and [4] tinyqs: see model_brent63()/model_tinyqs() */
    [5]  = { 3500000,   0.0,  100 },
    [10] = { 500,       0.0,  100 },
    [26] = { 120000000, 0.0,  0   },
    [29] = { 100000000, 0.0,  0   },
    [30] = { 16000000,  0.03, 0   },
};

/* For P-1 rungs curves is always 1 and B2 is the real stage 2 bound
 * (matching the tmf_N definitions in coultau.c); B2 is unused for
 * ECM rungs. */
struct ecm_p1_params {
    ulong B1; uint curves; bool is_p1; uint B1_mult; bool sets_b1; ulong B2;
};
static const struct ecm_p1_params ECM_P1[MOCK_TM_MAX] = {
    [3]  = {5000, 1, 1, 0, 0, 5000},       [6]  = {1000, 1, 1, 0, 0, 10000},
    [7]  = {2000, 1, 1, 0, 0, 20000},      [8]  = {4000, 1, 1, 0, 0, 40000},
    [9]  = {10000, 1, 1, 0, 0, 100000},    [11] = {20000, 1, 1, 0, 0, 200000},
    [12] = {200, 4, 0, 0, 0, 0},           [13] = {600, 20, 0, 0, 0, 0},
    [14] = {2000, 10, 0, 0, 0, 0},         [15] = {200000, 1, 1, 0, 0, 3000000},
    [16] = {5000, 20, 0, 0, 1, 0},         [17] = {10000, 2, 0, 0, 1, 0},
    [18] = {20000, 2, 0, 0, 1, 0},         [19] = {30000, 20, 0, 0, 1, 0},
    [20] = {40000, 40, 0, 0, 1, 0},        [21] = {80000, 40, 0, 0, 1, 0},
    [22] = {160000, 80, 0, 0, 1, 0},       [23] = {320000, 160, 0, 0, 1, 0},
    [25] = {0, 20, 0, 2, 0, 0},            [27] = {0, 20, 0, 4, 0, 0},
    [28] = {0, 40, 0, 8, 0, 0},            [31] = {5000000, 1, 1, 0, 0, 100000000},
    [32] = {0, 40, 0, 32, 0, 0},
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
 * 2=qs, 3=fixed-empirical, 4=the ct_prime()/is_taux() checks that
 * follow every success). Weighted by cross-candidate survival, so the
 * families sum to g_mock_spent_s. */
#define MOCK_NFAM 5   /* 0=ecm 1=p1 2=qs 3=fixed 4=post-success checks */
double g_mock_family_s[MOCK_NFAM];

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

/* Given a prime of size 2^p_bits was just found (rung succeeded),
 * split into P(incompatible - triggers a whole-batch abort) and, for
 * each multiplicity k >= 1 whose resulting exponent j = k*E + 1
 * divides t, P(compatible via multiplicity k). This mirrors the real
 * e = e * tm->e + 1 test in tau_multi_run(); an earlier version assumed
 * E == 1 throughout. Exact geometric law P(mult = k) =
 * (1/p)^(k-1) * (1-1/p): hvds (chat): "we should have a uniform
 * distribution over values mod p and over values mod p^2 etc, for
 * every p not in our list of allocations" - for nqc==0 this is exact,
 * not a heuristic (ati sweeps uniformly and qq[vi] is coprime to any
 * such p). NOT verified for nqc>0 (have_square/Pell branch) - flagged
 * as open, per hvds. */
#define MAX_COMPAT 64
struct compat_result {
    double p_incompatible;
    int n_compat;
    uint compat_j[MAX_COMPAT];    /* exponent-plus-one, divides t */
    uint compat_k[MAX_COMPAT];    /* multiplicity of the found prime */
    double compat_p[MAX_COMPAT];
};

static void compatibility_split(double p_bits, uint t, uint E,
        struct compat_result *out) {
    double inv_p = pow(2.0, -p_bits);
    double q = 1.0 - inv_p;
    double pk = q;              /* P(mult == k), starting at k = 1 */
    double p_compat_total = 0;
    out->n_compat = 0;
    for (uint k = 1; (ulong)k * E + 1 <= t; ++k, pk *= inv_p) {
        uint j = k * E + 1;
        if (t % j)
            continue;
        if (out->n_compat < MAX_COMPAT) {
            out->compat_j[out->n_compat] = j;
            out->compat_k[out->n_compat] = k;
            out->compat_p[out->n_compat] = pk;
            ++out->n_compat;
        }
        p_compat_total += pk;
        if (pk < 1e-18)
            break;
    }
    out->p_incompatible = 1.0 - p_compat_total;
    if (out->p_incompatible < 0)
        out->p_incompatible = 0;
}

static void rung_model(uint i, t_tm *tm, uint bits, double factor_bits,
        double *cost_s, double *p_succ, int *family) {
    if (i < MOCK_TM_MAX && ECM_P1[i].curves) {
        const struct ecm_p1_params *p = &ECM_P1[i];
        if (p->is_p1) {
            *p_succ = p_success_p1(p->B1, p->B2, factor_bits);
            *cost_s = cost_p1_s(p->B1, p->B2, bits)
                * (1.0 - (1.0 - SUCCESS_FRAC_P1) * *p_succ);
            *family = 1;
            return;
        }
        ulong B1 = p->B1_mult ? tm->B1 * p->B1_mult : p->B1;
        if (p->sets_b1)
            tm->B1 = B1;
        *family = 0;
        if (B1 == 0) {
            /* relative-B1 rung with no earlier B1-setting rung enabled
             * in this pass; the real code would use a stale or zero
             * tm->B1 here. Treated as a no-op - see B1 chaining gap. */
            *cost_s = 0;
            *p_succ = 0;
            return;
        }
        *p_succ = p_success_ecm(B1, p->curves, factor_bits);
        *cost_s = cost_ecm_s(B1, p->curves, bits)
            * (1.0 - (1.0 - SUCCESS_FRAC_ECM) * *p_succ);
        return;
    }
    if (i == 24) {
        *cost_s = qs_cost_seconds(bits);
        *p_succ = 1.0;   /* QS is general-purpose - treat as reliable
                             once reached, ending the chain here */
        *family = 2;
        return;
    }
    if (i == 2) {
        model_brent63(bits, factor_bits, cost_s, p_succ);
        *family = 3;
        return;
    }
    if (i == 4) {
        model_tinyqs(bits, cost_s, p_succ);
        *family = 3;
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

/* PLACEHOLDER costs for the checks tau_multi_run() does after every
 * success: tm_factor()'s ct_prime() on the found factor, then either
 * ct_prime() on the cofactor (even t) or is_taux() (odd t, normally
 * just a perfect-power test for a residual that isn't one). Not yet
 * measured - LADDER_STATS lumps them into total_s - rung_s. */
#define CT_PRIME_S  3e-6
#define IS_TAUX_S   3e-6

/* ---------------------------------------------------------------------
 * Event list. Each candidate's chain is expanded into events tagged
 * with the rung-major "slot" at which they happen in the real
 * tau_multi_run(), so that cross-candidate whole-batch aborts can be
 * applied in the right order (see mock_tau_multi_run()). Weights are
 * already conditioned on the candidate's OWN history (not having
 * aborted or resolved earlier); only the other candidates' survival
 * is applied later.
 * ------------------------------------------------------------------ */
#define MOCK_CHECK_RUNG MOCK_TM_MAX   /* pseudo-rung for post-success checks */
#define MOCK_NSLOT (MOCK_TM_MAX + 1)
#define MOCK_NBUCKET 64

struct mock_event {
    uint slot, rung, fam, cand, bits;
    double tries;     /* expected attempts */
    double hits;      /* expected successes (tries * p_succ) */
    double cost;      /* expected seconds */
    double abort_p;   /* P(this candidate aborts the batch here) */
};
static struct mock_event *g_ev;
static uint g_ev_n, g_ev_cap;

static void ev_add(uint slot, uint rung, uint fam, uint cand, uint bits,
        double tries, double hits, double cost, double abort_p) {
    if (g_ev_n == g_ev_cap) {
        g_ev_cap = g_ev_cap ? g_ev_cap * 2 : 1024;
        g_ev = realloc(g_ev, g_ev_cap * sizeof(struct mock_event));
        if (!g_ev)
            fail("coulmock: out of memory for events");
    }
    g_ev[g_ev_n++] = (struct mock_event){
        slot, rung, fam, cand, bits, tries, hits, cost, abort_p
    };
}

/* Stats, survival-weighted, printed at exit in the same shape as
 * coultau.c's LADDER_STATS so the two can be compared directly. */
static double g_ms_tries[MOCK_NSLOT], g_ms_hits[MOCK_NSLOT], g_ms_s[MOCK_NSLOT];
static double g_mb_tries[MOCK_NSLOT][MOCK_NBUCKET];
static double g_mb_hits[MOCK_NSLOT][MOCK_NBUCKET];
static double g_mb_s[MOCK_NSLOT][MOCK_NBUCKET];
static ulong g_mt_calls, g_mt_entries, g_mt_prep_passes;
static double g_mt_aborts, g_mt_raw_s;

static void report_family_breakdown(void) {
    for (uint i = 0; i < MOCK_NSLOT; ++i) {
        if (g_ms_tries[i] <= 0)
            continue;
        fprintf(stderr, "MOCK_LADDER_STATS rung=%u%s tries=%.2f hits=%.2f s=%.6f\n",
                i, (i == MOCK_CHECK_RUNG) ? "(checks)" : "",
                g_ms_tries[i], g_ms_hits[i], g_ms_s[i]);
        for (uint b = 0; b < MOCK_NBUCKET; ++b)
            if (g_mb_tries[i][b] > 0)
                fprintf(stderr, "MOCK_LADDER_BUCKET rung=%u bits=%u-%u tries=%.2f"
                        " hits=%.2f s=%.6f\n", i, b * 8, b * 8 + 7,
                        g_mb_tries[i][b], g_mb_hits[i][b], g_mb_s[i][b]);
    }
    fprintf(stderr, "MOCK_LADDER_TOTAL calls=%lu entries=%lu aborts=%.2f"
            " prep_passes=%lu total_s=%.6f raw_s=%.6f\n", g_mt_calls,
            g_mt_entries, g_mt_aborts, g_mt_prep_passes, g_mock_spent_s,
            g_mt_raw_s);
    fprintf(stderr, "MOCK_FAMILY_BREAKDOWN ecm=%.6f p1=%.6f qs=%.6f fixed=%.6f"
            " checks=%.6f total=%.6f\n",
        g_mock_family_s[0], g_mock_family_s[1], g_mock_family_s[2],
        g_mock_family_s[3], g_mock_family_s[4], g_mock_spent_s);
}

#define MAX_RECURSE_DEPTH 20

/* Expand one candidate's chain into events, following tau_multi_run()'s
 * own behaviour after each success:
 *   - incompatible exponent: abort;
 *   - t -> 1: needs n == 1, treated as abort (a residual that reached
 *     the ladder is essentially never a pure prime power);
 *   - t -> 2: ct_prime() on the cofactor, abort unless prime;
 *   - t -> odd > 1: immediate is_taux() full check, treated as abort
 *     (previously recursed into the full ladder, charging ladder cost
 *     for what is really one cheap check);
 *   - t -> even > 2: abort if the cofactor is prime, else restart the
 *     ladder from TM_INIT on the cofactor (goto tmr_retry).
 * A restarted chain's rungs happen immediately, before the other
 * candidates continue at the current rung, but its later rungs then
 * interleave normally - so its events go to slot max(rung, floor_slot).
 *
 * The smallest factor size is sampled ONCE per residual (previously
 * resampled per rung, contradicting the design and letting each rung
 * roll its own dice). A restarted chain samples afresh, being a new
 * residual.
 *
 * KNOWN GAPS: tm->B1 is not carried into a restarted chain; t==1/2
 * outcomes and the checks use crude placeholders (CT_PRIME_S,
 * IS_TAUX_S, p_cofactor_prime()); nqc>0 not verified. */
static void candidate_chain(uint cand, uint t, uint E, uint bits,
        uint floor_slot, double weight, int depth) {
    if (depth > MAX_RECURSE_DEPTH || weight < 1e-12)
        return;
    ulong bitmask = mock_find_tmfb(bits);
    double factor_bits = sample_factor_bits(bits);
    double reach = weight;
    t_tm dummy_tm;
    dummy_tm.B1 = 0;

    for (uint i = MOCK_TM_INIT; i < MOCK_TM_MAX; ++i) {
        if (!(bitmask & (1UL << i)))
            continue;
        uint slot = (i > floor_slot) ? i : floor_slot;
        double cost_s, p_succ;
        int family;
        rung_model(i, &dummy_tm, bits, factor_bits, &cost_s, &p_succ, &family);
        ev_add(slot, i, family, cand, bits, reach, reach * p_succ,
                reach * cost_s, 0);

        if (p_succ > 0) {
            double ps = reach * p_succ;
            struct compat_result cr;
            compatibility_split(factor_bits, t, E, &cr);
            double abort_p = ps * cr.p_incompatible;
            double check_s = ps * CT_PRIME_S;   /* tm_factor() */
            for (int k = 0; k < cr.n_compat; ++k) {
                double pj = ps * cr.compat_p[k];
                uint new_t = t / cr.compat_j[k];
                double reduced = bits - cr.compat_k[k] * factor_bits;
                uint new_bits = (reduced > 8) ? (uint)reduced : 8;
                if (new_t == 1) {
                    abort_p += pj;
                } else if (new_t == 2) {
                    check_s += pj * CT_PRIME_S;
                    abort_p += pj * (1.0 - p_cofactor_prime(new_bits));
                } else if (new_t & 1) {
                    check_s += pj * IS_TAUX_S;
                    abort_p += pj;
                } else {
                    double pp = p_cofactor_prime(new_bits);
                    check_s += pj * CT_PRIME_S;
                    abort_p += pj * pp;
                    candidate_chain(cand, new_t, E, new_bits, slot,
                            pj * (1.0 - pp), depth + 1);
                }
            }
            ev_add(slot, MOCK_CHECK_RUNG, 4, cand, bits, ps, 0, check_s,
                    abort_p);
        }
        reach *= (1.0 - p_succ);
        if (reach <= 1e-12)
            break;
    }
}

static int ev_cmp(const void *va, const void *vb) {
    const struct mock_event *a = va, *b = vb;
    if (a->slot != b->slot)
        return (a->slot < b->slot) ? -1 : 1;
    if (a->cand != b->cand)
        return (a->cand < b->cand) ? -1 : 1;
    return 0;
}

extern int taum_comparator(const void *va, const void *vb);
static int idx_cmp(const void *va, const void *vb) {
    return taum_comparator(&taum[*(const uint *)va], &taum[*(const uint *)vb]);
}

uint mock_tau_multi_run(uint count, tau_failure_handler tfh) {
    static bool registered = 0;
    if (!registered) {
        atexit(report_family_breakdown);
        registered = 1;
    }
    (void)tfh;   /* never invoked - see file header */
    ++g_mt_calls;

    /* Same filter as the real code: entries already fully resolved by
     * tau_multi_prep() (state == 0) never reach the ladder - previously
     * the mock charged a full ladder for them too. If that leaves
     * nothing, the real function returns 0 (success) deterministically,
     * with no factoring involved, so the mock does the same. */
    uint idx[count ? count : 1];
    uint n = 0;
    for (uint j = 0; j < count; ++j)
        if (taum[j].state != 0)
            idx[n++] = j;
    if (n == 0) {
        ++g_mt_prep_passes;
        return 0;
    }
    g_mt_entries += n;
    /* rung-major order within a slot follows the real qsort order */
    qsort(idx, n, sizeof(uint), &idx_cmp);

    g_ev_n = 0;
    for (uint c = 0; c < n; ++c) {
        t_tm *tm = &taum[idx[c]];
        candidate_chain(c, tm->t, tm->e ? tm->e : 1,
                mpz_sizeinbase(tm->n, 2), 0, 1.0, 0);
    }
    qsort(g_ev, g_ev_n, sizeof(struct mock_event), &ev_cmp);

    /* Walk rung-major. A[c] is P(candidate c has aborted the batch so
     * far); an event of candidate c is reached only if no OTHER
     * candidate has aborted yet (its own history is already in its
     * weights), treating candidates as independent. */
    double A[n];
    for (uint c = 0; c < n; ++c)
        A[c] = 0;
    double spent = 0;
    for (uint e = 0; e < g_ev_n; ) {
        uint slot = g_ev[e].slot, c = g_ev[e].cand;
        double others = 1.0;
        for (uint k = 0; k < n; ++k)
            if (k != c)
                others *= 1.0 - A[k];
        double group_abort = 0;
        for (; e < g_ev_n && g_ev[e].slot == slot && g_ev[e].cand == c; ++e) {
            struct mock_event *ev = &g_ev[e];
            double w_s = ev->cost * others;
            uint b = ev->bits >> 3;
            if (b >= MOCK_NBUCKET)
                b = MOCK_NBUCKET - 1;
            spent += w_s;
            g_mt_raw_s += ev->cost;
            g_mock_family_s[ev->fam] += w_s;
            g_ms_tries[ev->rung] += ev->tries * others;
            g_ms_hits[ev->rung] += ev->hits * others;
            g_ms_s[ev->rung] += w_s;
            g_mb_tries[ev->rung][b] += ev->tries * others;
            g_mb_hits[ev->rung][b] += ev->hits * others;
            g_mb_s[ev->rung][b] += w_s;
            group_abort += ev->abort_p;
        }
        A[c] += group_abort;
        if (A[c] > 1.0)
            A[c] = 1.0;
    }
    double survive = 1.0;
    for (uint c = 0; c < n; ++c)
        survive *= 1.0 - A[c];
    g_mt_aborts += 1.0 - survive;
    g_mock_spent_s += spent;
    /* Always report rejection when anything reached the ladder: a
     * mocked run's results are meaningless, only its timing is
     * modelled. (0 would mean "every entry validated".) */
    return count;
}
