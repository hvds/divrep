/* The mocks for calibration (MOCK_WALK, MOCK_LEAF): see mock.h. */

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <errno.h>
#include <math.h>
#include <time.h>

#include "coulint.h"
#include "coulfact.h"
#include "rootmod.h"
#include "coultau.h"
#include "mock.h"

/* The cost table and the models built on it are compiled into every
 * build: besides the mocks below, -ja learning charges the factoring
 * ladder its expected cost from them (cm_ladder_cost()).
 *
 * MOCK_WALK: calibration-only stub for walk_v(). Everything up to the
 * iteration loops runs for real; the loops themselves are replaced by
 * their expected cost, added to g_mock_spent_s, so that a run reports
 * real non-walk time plus modelled walk time, deterministically. Never
 * use for a real search: no candidate is ever tested.
 *
 * Per iteration: loop + P_inv * (C_p + P_prime * C_m) for a linear walk,
 * loop_sq + P_inv * (C_sq + P_sq * (C_p + P_prime * C_m)) plus setup per
 * walk for a fixed power (nqc == 1), where each loop cost is a base plus
 * a cost per inverse-filter entry tested. P_inv is exact from inv[];
 * P_prime multiplies prime probabilities over need_prime residuals.
 * All costs come from the machine's cost table named by
 * $MOCK_WALK_TABLE (see multibench-table), so that nothing here is
 * specific to one machine or MPUGMP build. Pell walks (nqc > 1) still
 * run for real.
 *
 * walk_1_set() runs for real over its first MW_W1S_PREFIX primes, but
 * with each surviving prime's tests replaced by their expected cost;
 * the rest of its primes are then charged per prime, plus the prefix's
 * rate of survivors times the cost of the checks and its mean test cost.
 *
 * The test costs model trial division explicitly, following
 * tau_multi_prep(): for each position, the distribution of the valuation
 * at each trial prime p of the values reaching the tests follows from the
 * walk (see t_mwwalk), and the tau still to find as factors are divided
 * out decides a rejection or an immediate decision there (all of tau
 * found, or only a prime left to find), at the cost measured for
 * stopping at p. Trial division goes to sqrt(value) when that is below
 * its limit L, and is then complete. The table, for inputs with no trial
 * factor, gives the rest. Results are cached by what decides them, and
 * for walk_1_set(), whose values are known exactly, sampled. The mock's
 * own CPU time is measured and discounted.
 */
#define MW_W1S_PREFIX 10000
#define MW_W1S_SAMPLE 8
#define MW_MAXT 256
#define MW_MAXB 64
typedef struct {
    uint t, e, nb;
    double bits[MW_MAXB], v[MW_MAXB][6];   /* rej dec pend pass prep run */
} t_mw;
static t_mw mw_tab[MW_MAXT];
static uint mw_count = 0;
static bool mw_loaded = 0;
/* Trial division: the table's rows are for inputs with no factor up to
 * the trial limit L for their size, since the mock handles the trial
 * primes itself for each walk. The "L bits p" rows give L by size and
 * the "S bits p prep_us prime_us" rows the cost of a test that fails at
 * trial prime p; each set is used for sizes nearest its bits. */
#define MW_MAXS 64
typedef struct {
    uint bits, L, ns;
    uint p[MW_MAXS];
    double prep[MW_MAXS], prime[MW_MAXS];
    double extra[MW_MAXS];  /* extra prep cost of a factor found at p that
                             * does not end prep */
    double KL;      /* prod p / (p - 1) over the trial primes */
} t_mwscan;
static t_mwscan mw_scan[16];
static uint mw_nscan = 0;
static uint *mw_tp = NULL, mw_ntp = 0;  /* primes up to the largest L */
static mpz_t mw_tmp;

/* prime test cost by bits: (pass rate, seconds) */
typedef struct {
    uint nb;
    double bits[MW_MAXB], v[MW_MAXB][2];
} t_mw1;
static t_mw1 mw_P, mw_R;
/* the "Q bits us fail" rows: QS alone (rung 24), whose cost depends
 * only on the size, stepping with its parameters by decimal digits
 */
static t_mw1 mw_Q;
/* the factoring ladder of tau_multi_run() on a composite of the given
 * bits with no factor up to L, from the "G" rows: for each rung that
 * applies at that size, the fraction of values reaching it without a
 * factor found, the mean cost of an attempt, the fraction of attempts
 * finding a factor, and for those the mean bits of the factor and the
 * fraction whose cofactor is prime
 */
#define MW_NSLOT 48     /* > TM_MAX */
#define MW_MAXLR 16     /* rungs per size */
#define MW_MAXLAD 64    /* sizes */
typedef struct {
    uint bits, nr;
    uint rung[MW_MAXLR];
    double reach[MW_MAXLR], cost[MW_MAXLR], hit[MW_MAXLR],
            fbits[MW_MAXLR], cprime[MW_MAXLR];
} t_mwlad;
static t_mwlad mw_lad[MW_MAXLAD];
static uint mw_nlad = 0;
static const ulong *mw_tmfbl;    /* the ladder's rung masks, get_tmfbl() */
static uint mw_tmfb_maxb;
static ulong mw_tmfb_lim;

/* scalars, all times in seconds */
typedef struct {
    char *name;
    double v;
    bool seen;
    bool is_time;
    double dflt;    /* if not 0, the value for a table without it */
} t_mwc;
static t_mwc mw_C[] = {
    { "loop0", 0, 0, 1 },       /* linear walk per ati */
    { "looptest", 0, 0, 1 },    /* linear walk per inverse test */
    { "sqsetup", 0, 0, 1 },     /* fixed-power walk per walk */
    { "sqloop0", 0, 0, 1 },     /* fixed-power walk per root */
    { "sqtest", 0, 0, 1 },      /* fixed-power walk per inverse test */
    { "cprime", 0, 0, 1 },      /* leaf loop per prime */
    { "cprimesq", 0, 0, 1 },    /* likewise, with a fixed-power walk */
    { "w1siter", 0, 0, 1 },     /* walk_1_set() per prime */
    { "w1scheck", 0, 0, 1 },    /* walk_1_set() per prime passing mod check */
    { "ctail", 0, 0, 1 },       /* rest of a loop of rejects, per prime */
    /* linear walk per walk (tables before it had none) */
    { "linsetup", 0, 0, 1, 2e-6 },
    /* recurse loop per prime applied, beyond cprime (likewise) */
    { "capply", 0, 0, 1, 0.5e-6 },
};
/* in the order of the CM_* constants in mock.h */
enum { MWC_LOOP0, MWC_LOOPTEST, MWC_SQSETUP, MWC_SQLOOP0, MWC_SQTEST,
        MWC_CPRIME, MWC_CPRIMESQ, MWC_W1SITER,
        MWC_W1SCHECK, MWC_CTAIL, MWC_LINSETUP, MWC_CAPPLY, MWC_COUNT };
#define MWC(i) (mw_C[i].v)

static void mw_add1(t_mw1 *tp, double bits, double v0, double v1) {
    if (tp->nb == MW_MAXB)
        fail("cost table: table too large");
    tp->bits[tp->nb] = bits;
    tp->v[tp->nb][0] = v0;
    tp->v[tp->nb][1] = v1;
    ++tp->nb;
}

/* The table's sizes are bit counts, where the mock has log2 of a value:
 * mw_bx() gives the size to look up, lg + 1/2 (values of b bits have
 * mean log2 about b - 1/2), kept within the sizes of as many limbs as
 * the value has, since costs step up with each limb.
 */
static inline uint mw_limbs(uint bits) {
    return (bits + 63) / 64;
}
static inline uint mw_nbits(double lg) {
    return (lg < 0) ? 1 : (uint)lg + 1;
}
static inline double mw_bx(double lg) {
    uint L = mw_limbs(mw_nbits(lg));
    double x = lg + 0.5, lo = 64.0 * (L - 1) + 1, hi = 64.0 * L;
    return (x < lo) ? lo : (x > hi) ? hi : x;
}

/* The trial division costs for a value with log2 lg: those of the
 * nearest size with as many limbs, else of the nearest size. With
 * create, those for exactly the given size (a bit count), made if new.
 */
static t_mwscan *mw_scan_find(double lg, bool create) {
    uint bits = create ? (uint)lg : mw_nbits(lg);
    double x = mw_bx(lg);
    t_mwscan *best = NULL, *bestl = NULL;
    for (uint i = 0; i < mw_nscan; ++i) {
        t_mwscan *sp = &mw_scan[i];
        if (create) {
            if (sp->bits == bits)
                best = sp;
            continue;
        }
        double d = fabs(sp->bits - x);
        if (!best || d < fabs(best->bits - x))
            best = sp;
        if (mw_limbs(sp->bits) == mw_limbs(bits)
                && (!bestl || d < fabs(bestl->bits - x)))
            bestl = sp;
    }
    if (bestl)
        return bestl;
    if (create && !best) {
        if (mw_nscan == sizeof(mw_scan) / sizeof(mw_scan[0]))
            fail("cost table: too many trial division sizes");
        best = &mw_scan[mw_nscan++];
        *best = (t_mwscan){ .bits = bits };
    }
    return best;
}

/* The table is the output of multibench-table: lines starting with a
 * digit are test_multi() rows "t e bits F rej dec pend pass prep run";
 * others are "C name value", "P bits F pass us", "R bits us us",
 * "S bits p us us" or "L bits p". Times in the file are in microseconds. */
static void mw_load(void);

/* the build that made each section of the table, from its V lines */
static struct {
    char section[16], sha[80];
} mw_ver[16];
static uint mw_nver = 0;

/* the build that made a section of the table, or NULL if not known */
const char *cm_table_sha(const char *section) {
    if (!mw_loaded)
        mw_load();
    for (uint i = 0; i < mw_nver; ++i)
        if (strcmp(mw_ver[i].section, section) == 0)
            return mw_ver[i].sha;
    return NULL;
}

/* the next line of the table, from the file if any, else from the
 * built-in default
 */
static char *mw_line(char *buf, size_t size, FILE *fp, const char **src) {
    if (fp)
        return fgets(buf, size, fp);
    if (!**src)
        return NULL;
    size_t i = 0;
    while (**src && i + 1 < size) {
        char c = *(*src)++;
        buf[i++] = c;
        if (c == '\n')
            break;
    }
    buf[i] = 0;
    return buf;
}

static void mw_load(void) {
    mw_loaded = 1;
    mpz_init(mw_tmp);
    /* $COST_TABLE, or as before $MOCK_WALK_TABLE, else the built-in */
    char *fn = getenv("COST_TABLE");
    if (!fn)
        fn = getenv("MOCK_WALK_TABLE");
    FILE *fp = NULL;
    const char *src = cm_default_table;
    if (fn) {
        fp = fopen(fn, "r");
        if (!fp)
            fail("cost table %s: %s", fn, strerror(errno));
    } else
        fn = "(built-in)";
    char line[256], name[32];
    while (mw_line(line, sizeof(line), fp, &src)) {
        char sha[sizeof(mw_ver[0].sha)];
        if (sscanf(line, "V %15s %79s", name, sha) == 2) {
            if (mw_nver < sizeof(mw_ver) / sizeof(mw_ver[0])) {
                strcpy(mw_ver[mw_nver].section, name);
                strcpy(mw_ver[mw_nver++].sha, sha);
            }
            continue;
        }
        uint t, e, b, F;
        double v[6];
        if (sscanf(line, "C %31s %lf", name, &v[0]) == 2) {
            for (uint i = 0; i < MWC_COUNT; ++i)
                if (strcmp(name, mw_C[i].name) == 0) {
                    mw_C[i].v = mw_C[i].is_time ? v[0] * 1e-6 : v[0];
                    mw_C[i].seen = 1;
                }
            continue;
        }
        uint r;
        if (sscanf(line, "G %u %u %lf %lf %lf %lf %lf", &b, &r, &v[0],
                &v[1], &v[2], &v[3], &v[4]) == 7 && r > 0) {
            uint i;
            for (i = 0; i < mw_nlad; ++i)
                if (mw_lad[i].bits == b)
                    break;
            if (i == mw_nlad) {
                if (mw_nlad == MW_MAXLAD)
                    fail("cost table: too many G sizes");
                mw_lad[mw_nlad++] = (t_mwlad){ .bits = b, .nr = 0 };
            }
            t_mwlad *lp = &mw_lad[i];
            if (lp->nr == MW_MAXLR)
                fail("cost table: too many G rungs at %u bits", b);
            uint j = lp->nr++;
            lp->rung[j] = r;
            lp->reach[j] = v[0];
            lp->cost[j] = v[1] * 1e-6;
            lp->hit[j] = v[2];
            lp->fbits[j] = v[3];
            lp->cprime[j] = v[4];
            continue;
        }
        if (sscanf(line, "P %u %u %lf %lf", &b, &F, &v[0], &v[1]) == 4) {
            mw_add1(&mw_P, b, v[0], v[1] * 1e-6);
            continue;
        }
        if (sscanf(line, "Q %u %lf %lf", &b, &v[0], &v[1]) == 3) {
            mw_add1(&mw_Q, b, v[0] * 1e-6, v[1]);
            continue;
        }
        if (sscanf(line, "R %u %lf %lf", &b, &v[0], &v[1]) == 3) {
            mw_add1(&mw_R, b, v[0] * 1e-6, v[1] * 1e-6);
            continue;
        }
        uint p;
        int nf = sscanf(line, "S %u %u %lf %lf %lf", &b, &p, &v[0], &v[1],
                &v[2]);
        if (nf >= 4) {
            t_mwscan *sp = mw_scan_find(b, 1);
            if (sp->ns == MW_MAXS)
                fail("cost table: too many S rows");
            sp->p[sp->ns] = p;
            sp->prep[sp->ns] = v[0] * 1e-6;
            sp->extra[sp->ns] = (nf == 5 && v[2] > 0) ? v[2] * 1e-6 : 0;
            sp->prime[sp->ns++] = v[1] * 1e-6;
            continue;
        }
        if (sscanf(line, "L %u %u", &b, &p) == 2) {
            mw_scan_find(b, 1)->L = p;
            continue;
        }
        if (sscanf(line, "%u %u %u %u %lf %lf %lf %lf %lf %lf", &t, &e, &b,
                &F, &v[0], &v[1], &v[2], &v[3], &v[4], &v[5]) != 10)
            continue;
        uint i;
        for (i = 0; i < mw_count; ++i)
            if (mw_tab[i].t == t && mw_tab[i].e == e)
                break;
        if (i == mw_count) {
            if (mw_count == MW_MAXT)
                fail("cost table: table too large");
            mw_tab[mw_count++] = (t_mw){ .t = t, .e = e, .nb = 0 };
        }
        t_mw *mp = &mw_tab[i];
        if (mp->nb == MW_MAXB)
            continue;
        mp->bits[mp->nb] = b;
        v[4] *= 1e-6;
        v[5] *= 1e-6;
        memcpy(mp->v[mp->nb++], v, sizeof(v));
    }
    if (fp)
        fclose(fp);
    for (uint i = 0; i < MWC_COUNT; ++i)
        if (!mw_C[i].seen) {
            if (!mw_C[i].dflt)
                fail("cost table: %s: no value for C %s", fn, mw_C[i].name);
            mw_C[i].v = mw_C[i].dflt;
        }
    if (!mw_P.nb || !mw_R.nb)
        fail("cost table: %s: need P and R rows", fn);
    if (!mw_nscan)
        fail("cost table: %s: need S and L rows", fn);
    uint maxL = 0;
    for (uint i = 0; i < mw_nscan; ++i) {
        if (!mw_scan[i].L || !mw_scan[i].ns)
            fail("cost table: %s: need S and L rows for %u bits", fn,
                    mw_scan[i].bits);
        if (mw_scan[i].L > maxL)
            maxL = mw_scan[i].L;
    }
    /* sieve the trial primes */
    char *comp = calloc(maxL + 1, 1);
    mw_tp = malloc((maxL / 2 + 2) * sizeof(uint));
    for (uint p = 2; p <= maxL; ++p) {
        if (comp[p])
            continue;
        mw_tp[mw_ntp++] = p;
        for (ulong q = (ulong)p * p; q <= maxL; q += p)
            comp[q] = 1;
    }
    free(comp);
    for (uint i = 0; i < mw_nscan; ++i) {
        mw_scan[i].KL = 1;
        for (uint j = 0; j < mw_ntp && mw_tp[j] <= mw_scan[i].L; ++j)
            mw_scan[i].KL *= (double)mw_tp[j] / (mw_tp[j] - 1);
    }
}

/* interpolate a one-dimensional table for a value of log2 lg (see
 * mw_bx()), geometrically for positive values
 */
static double mw_interp1(t_mw1 *tp, double lg, uint k) {
    if (!mw_loaded)
        mw_load();
    double bits = mw_bx(lg);
    if (bits <= tp->bits[0])
        return tp->v[0][k];
    if (bits >= tp->bits[tp->nb - 1])
        return tp->v[tp->nb - 1][k];
    uint j = 1;
    while (bits > tp->bits[j])
        ++j;
    double f = (bits - tp->bits[j - 1]) / (tp->bits[j] - tp->bits[j - 1]);
    double a = tp->v[j - 1][k], b = tp->v[j][k];
    return (a > 0 && b > 0) ? a * pow(b / a, f) : a + f * (b - a);
}

/* interpolate the table at (t, e) for a value of log2 lg (see mw_bx());
 * rows are in increasing bits
 */
static bool mw_lookup(uint t, uint e, double lg, double out[6]) {
    if (!mw_loaded)
        mw_load();
    double bits = mw_bx(lg);
    for (uint i = 0; i < mw_count; ++i) {
        t_mw *mp = &mw_tab[i];
        if (mp->t != t || mp->e != e)
            continue;
        uint j = 1;
        if (bits <= mp->bits[0]) {
            memcpy(out, mp->v[0], 6 * sizeof(double));
            return 1;
        }
        if (bits >= mp->bits[mp->nb - 1]) {
            memcpy(out, mp->v[mp->nb - 1], 6 * sizeof(double));
            return 1;
        }
        while (bits > mp->bits[j])
            ++j;
        double f = (bits - mp->bits[j - 1]) / (mp->bits[j] - mp->bits[j - 1]);
        for (uint k = 0; k < 4; ++k)
            out[k] = mp->v[j - 1][k] + f * (mp->v[j][k] - mp->v[j - 1][k]);
        for (uint k = 4; k < 6; ++k) {
            double a = mp->v[j - 1][k], b = mp->v[j][k];
            out[k] = (a > 0 && b > 0) ? a * pow(b / a, f) : a + f * (b - a);
        }
        return 1;
    }
    return 0;
}

/* the logarithmic integral, for counting primes */
static double mw_li(double x) {
    if (x < 2)
        return 0;
    double l = log(x);
    return x / l * (1 + 1 / l + 2 / (l * l));
}

/* exact inverse-filter pass rate: per distinct modulus m, the fraction
 * of residues mod m not excluded; if tests is non-NULL, also set it to
 * the expected number of entries tested per candidate */
static double mw_pinv(t_mod *inv, uint inv_count, double *tests) {
    if (tests) {
        double reach = 1.0;
        *tests = 0;
        for (uint i = 0; i < inv_count; ++i) {
            *tests += reach;
            reach *= 1.0 - 1.0 / inv[i].m;
        }
    }
    double p = 1.0;
    for (uint i = 0; i < inv_count; ++i) {
        bool seen = 0;
        for (uint j = 0; j < i; ++j)
            if (inv[j].m == inv[i].m) { seen = 1; break; }
        if (seen)
            continue;
        uint distinct = 0;
        for (uint j = i; j < inv_count; ++j) {
            if (inv[j].m != inv[i].m)
                continue;
            bool dup = 0;
            for (uint l = i; l < j; ++l)
                if (inv[l].m == inv[j].m && inv[l].v == inv[j].v) { dup = 1; break; }
            if (!dup)
                ++distinct;
        }
        p *= 1.0 - (double)distinct / inv[i].m;
    }
    return p;
}

#ifdef MOCK_LEAF
/* MOCK_LEAF: with MOCK_WALK, also stub innermost recurse loops - those
 * whose children all walk. A loop is pending from when it starts; if the
 * first child to survive apply_single() walks (a linear walk), that
 * walk's per-iteration cost and expected size are recorded, and when the
 * loop resumes, the remaining primes up to its cap are replaced by
 * c_prime each plus their walks, whose size scales as (p0/p)^(x-1). If
 * the first child recurses, or does anything not yet modelled, the loop
 * runs normally.
 * If instead the first child walks a fixed power (nqc == 1), whose cost
 * varies too irregularly with p to integrate, the loop is sampled: above
 * ML_SQ_PMIN (so that the cost changes little across a stride) every
 * ML_STRIDE-th prime runs normally, and each prime in between is only
 * iterated, and charged c_prime_sq plus the walk cost of the last prime
 * run. If a sampled child recurses, the loop reverts to running normally.
 * Loops above the leaves (ML_NOT) are strided likewise above ML_SQ_PMIN:
 * of each ML_STRIDE * ML_BLOCK primes the first ML_BLOCK run normally,
 * timed together (real time, and mock cost charged within them), and
 * each of the rest is charged their mean. Timing a block rather than a
 * single child spreads the cost of the clock reads over ML_BLOCK
 * children.
 * With $MOCK_LEAF_OFF set, leaf loops are identified but not stubbed,
 * so that comparing the two gives c_prime and c_prime_sq (the counts of
 * primes stubbed are reported at the end of the run).
 */
#define ML_MAX 256
#define ML_PENDING 1
#define ML_LEAF 2
#define ML_NOT 3
#define ML_SQ 4
#define ML_STRIDE 16
#define ML_BLOCK 8
#define ML_SQ_PMIN 65536
static uint ml_state[ML_MAX];
static double ml_iter_cost[ML_MAX], ml_r0[ML_MAX];
static ulong ml_p0[ML_MAX];
static ulong ml_count[ML_MAX];      /* ML_SQ: primes seen */
static double ml_walk[ML_MAX];      /* ML_SQ: walk cost of last prime run */
/* striding other loops: whether a sample block is running and how many
 * of its children have finished, when it started (clock, mock overhead
 * and mock cost so far), and the mean cost of the last complete block
 */
static bool ml_samp[ML_MAX], ml_have[ML_MAX];
static uint ml_nsamp[ML_MAX];
static double ml_t0[ML_MAX], ml_ov0[ML_MAX], ml_m0[ML_MAX], ml_cost[ML_MAX];
double g_ml_strided = 0;    /* primes skipped by striding */
double g_ml_primes = 0;     /* primes stubbed, for calibrating cprime */
double g_ml_primes_sq = 0;  /* likewise, for cprime_sq */
bool g_ml_off = 0;          /* $MOCK_LEAF_OFF: leave leaf loops real */


/* the cost of the rest of a leaf loop at level lvl, after prime p */
static double ml_stub_cost(uint lvl, ulong p, ulong limp, uint x) {
    if (limp <= p)
        return 0;
    double np = mw_li(limp) - mw_li(p);
    double s = x - 1, cost = MWC(MWC_CPRIME) * np;
    g_ml_primes += np;
    double sum = 0, step = pow(2.0, 0.125);
    for (double lo = p; lo < limp; lo *= step) {
        double hi = lo * step;
        if (hi > limp)
            hi = limp;
        double n = mw_li(hi) - mw_li(lo);
        if (n > 0)
            sum += n * pow(ml_p0[lvl] / sqrt(lo * hi), s);
    }
    return cost + ml_iter_cost[lvl] * ml_r0[lvl] * sum;
}

/* MOCK_LEAF also stubs the ends of loops whose primes apply_single()
 * would almost all reject on rq > zmax (CHECK_OVERFLOW), as in deep
 * recursion. With r = prev->rq < a = prev->aq, allocating p^(x-1) gives
 * rq = r + a.t for t roughly uniform mod p^(x-1), rejected when
 * t > T = floor((zmax - r) / a); so a prime passes with chance about
 * (T + 1) / p^(x-1), and for x >= 3 the rest of the loop from p expects
 * S <= (T + 1) / ((x - 2) p^(x-2) ln p) survivors. Once p passes the P*
 * where S falls to MR_TAIL_EPS (at once if r > zmax), the loop is ended
 * and its remaining primes (by li) are charged c_tail each, dropping
 * the few survivors expected: the bias is at most S times the cost of
 * a survivor. With $MOCK_TAIL_OFF set, such loops run to the end, so
 * that comparing the two gives c_tail (the count of primes stubbed is
 * reported at the end).
 */
#define MR_TAIL_EPS 0.01
static mpz_t mr_t;
static bool mr_set[ML_MAX];     /* mr_pstar[] is set for this loop */
static uint mr_seen[ML_MAX];    /* seen_best when it was set */
static double mr_pstar[ML_MAX]; /* P* */
double g_mr_tail = 0;           /* primes stubbed in loop tails */
bool g_mr_tail_off = 0;         /* $MOCK_TAIL_OFF: run loop tails */

static void mr_setup(uint lvl, t_level *prev, uint x) {
    mr_set[lvl] = 1;
    mr_seen[lvl] = seen_best;
    mr_pstar[lvl] = INFINITY;
    mpz_sub(mr_t, zmax, prev->rq);
    if (mpz_sgn(mr_t) < 0) {
        mr_pstar[lvl] = 0;
        return;
    }
    if (x < 3)
        return;
    /* solve (T + 1) / ((x - 2) p^(x-2) ln p) = MR_TAIL_EPS for p: the
     * fixed point converges fast, since ln p changes slowly
     */
    mpz_fdiv_q(mr_t, mr_t, prev->aq);
    double c = (mpz_get_d(mr_t) + 1) / ((x - 2) * MR_TAIL_EPS);
    double e = 1.0 / (x - 2), p = pow(c, e);
    for (uint i = 0; i < 4; ++i)
        p = pow(c / log(p < 3 ? 3 : p), e);
    mr_pstar[lvl] = p;
}

/* TRUE if the rest of the loop at lvl from p is stubbed */
static bool mr_tail(uint lvl, t_level *prev, t_level *cur, ulong p) {
    if (!mr_set[lvl] || mr_seen[lvl] != seen_best)
        mr_setup(lvl, prev, cur->x);
    if (p <= mr_pstar[lvl])
        return 0;
    double np = mw_li(cur->limp) - mw_li(p) + 1;
    if (np < 1)
        np = 1;
    g_mr_tail += np;
    g_mock_spent_s += np * MWC(MWC_CTAIL);
    return 1;
}
#endif

#ifdef MOCK_WALK
/* what the mocks stubbed, at the end of a run or on -Ld timeout */
void mock_report(void) {
    report("368 mock %.3fs (overhead %.3fs)", g_mock_spent_s,
            g_mock_overhead_s);
#   ifdef MOCK_LEAF
    report(", leaf primes %.0f, sq primes %.0f, strided %.0f", g_ml_primes,
            g_ml_primes_sq, g_ml_strided);
    report(", tail %.0f", g_mr_tail);
#   endif
    report("\n");
}
#endif

#define MW_MAXEXCL 16

/* CPU time, to measure (and discount) the mock's own overhead, and
 * time stride samples; CPU time is unaffected by other load. Not
 * CLOCK_PROCESS_CPUTIME_ID: while a CPU-time timer is armed (as the
 * diag and log timers are, see init_time()), Linux samples the process
 * clock from the thread group's cputimer, which advances only at
 * scheduler ticks (4ms here), so almost every interval read as 0 or
 * one tick. The thread clock stays precise, and pcoul has one thread.
 * It is a system call (~0.25us here).
 */
static inline double mw_clock(void) {
    struct timespec ts;
    clock_gettime(CLOCK_THREAD_CPUTIME_ID, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

/* The CPU time of one mw_clock(), which is itself overhead: an interval
 * between two reads includes about one read's worth, and about one more
 * falls outside it.
 */
double g_mw_read = 0;
static void mw_clock_init(void) {
    double t0 = mw_clock(), t1 = t0;
    for (uint i = 0; i < 1000; ++i)
        t1 = mw_clock();
    g_mw_read = (t1 - t0) / 1000;
}

static inline ulong mw_mulmod(ulong a, ulong b, ulong m) {
    return (ulong)((unsigned __int128)a * b % m);
}

/* The distribution of the valuation of a value at p, for a value
 * qq.ati + o over the ati that reach the tests, or of o itself if qq is
 * NULL: val[a] for a < MW_MAXV (the tail beyond is dropped). excl lists
 * residues of ati mod p already known not to reach the tests (because
 * they make some other position divisible by p where it may not be).
 */
#define MW_MAXV 8
static void mw_valuation(
    double *val, uint p, mpz_t o, mpz_t *qq, ulong *excl, uint nexcl
) {
    for (uint a = 0; a < MW_MAXV; ++a)
        val[a] = 0;
    /* valuations up to MW_MAXV - 1 from residues mod p^m */
    ulong pm = 1;
    uint m = 0;
    while (m < MW_MAXV - 1 && pm <= (1UL << 62) / p) {
        pm *= p;
        ++m;
    }
    ulong ro = mpz_fdiv_ui(o, pm), x = ro;
    uint a0 = 0;
    while (a0 < m && x % p == 0) {
        x /= p;
        ++a0;
    }
    if (!qq) {
        val[a0] = 1;
        return;
    }
    ulong rq = mpz_fdiv_ui(*qq, pm);
    uint b0 = 0;
    x = rq;
    while (b0 < m && x % p == 0) {
        x /= p;
        ++b0;
    }
    double d;       /* probability that p^b0 divides, then 1/p for each more */
    if (b0 > 0) {
        if (a0 < b0) {
            val[a0] = 1;
            return;
        }
        d = 1;
    } else {
        /* the ati residue making p divide: -o / qq (mod p) */
        ulong r = mw_mulmod(ro % p, simple_invert(rq % p, p), p);
        r = r ? p - r : 0;
        uint ne = 0;
        bool hit = 0;
        for (uint i = 0; i < nexcl; ++i) {
            bool dup = 0;
            for (uint l = 0; l < i; ++l)
                if (excl[l] == excl[i]) { dup = 1; break; }
            if (dup)
                continue;
            ++ne;
            if (excl[i] == r)
                hit = 1;
        }
        d = hit ? 0 : 1.0 / (p - ne);
        b0 = 1;
    }
    val[0] = 1 - d;
    double pa = d * (1 - 1.0 / p);
    for (uint a = b0; a < MW_MAXV; ++a) {
        val[a] += pa;
        pa /= p;
    }
}

/* the valuation of a value divisible by p with probability d, and by
 * each further power of p with probability 1/p */
static void mw_geometric(double *val, uint p, double d) {
    val[0] = 1 - d;
    double pa = d * (1 - 1.0 / p);
    for (uint a = 1; a < MW_MAXV; ++a) {
        val[a] = pa;
        pa /= p;
    }
}


static ulong mw_powmod(ulong b, ulong e, ulong m) {
    ulong r = 1;
    b %= m;
    while (e) {
        if (e & 1)
            r = mw_mulmod(r, b, m);
        b = mw_mulmod(b, b, m);
        e >>= 1;
    }
    return r;
}

/* The walk a value comes from, which decides how its divisibility by the
 * trial primes is distributed. In a linear walk the values are qq.ati + o
 * with ati uniform; in a walk of a fixed power at position s, with
 * cand + off_s = q_s.r^xi and r uniform, position j has q_j.v_j =
 * q_s.r^xi - c for c = off_s - off_j, so p divides v_j for as many r
 * mod p as c / q_s has xi-th roots: for xi == 2, when q_s.c is a square
 * v_j factorizes algebraically, and is divisible by p about twice as often.
 */
#define MWK_LINEAR 0
#define MWK_FIXED 1     /* in a walk of a fixed power */
#define MWK_EXACT 2     /* wv_o[] is the value itself */
#define MWK_ROOT 3      /* the root of a fixed power: coprime to the
                         * allocated primes, else no information */
typedef struct {
    uint kind;
    uint s, xi;         /* MWK_FIXED: the fixed power's position, root degree */
    bool pp;            /* MWK_FIXED: the root must be prime */
    mpz_t *qs;          /* MWK_FIXED: q_s */
    ulong khash;        /* MWK_FIXED: hash of q_s free of xi-th powers */
    ulong *alloc;       /* primes allocated anywhere */
    uint nalloc;
} t_mwwalk;

/* the outcome of trial division of one value: probability and cost of
 * rejection there, and for each tau s still to find the probability of
 * surviving with it and the expected bits divided out meanwhile */
typedef struct {
    ulong key;
    uint t;
    double rej, rejcost;
    double pass, passcost;  /* completed within trial division */
    double *ec;             /* extra scan cost carried by each survivor */
    double Kend;            /* prod q / (q - 1) over the trial primes used:
                             * a survivor of b bits is prime with
                             * probability Kend / (b ln 2) */
    double *w, *rb;
} t_mwtrial;
#define MW_CACHE (1 << 16)
static t_mwtrial *mw_cache[MW_CACHE];

/* hash n bytes into h, a word at a time */
static inline ulong mw_hash(ulong h, const void *p, size_t n) {
    const unsigned char *c = p;
    while (n) {
        ulong v = 0;
        size_t m = n < sizeof(v) ? n : sizeof(v);
        memcpy(&v, c, m);
        h = (h ^ v) * 0x9e3779b97f4a7c15UL;
        h ^= h >> 29;
        c += m;
        n -= m;
    }
    return h;
}

/* the valuation at p of position vj's value, for p not handled by the
 * key's special cases */
static void mw_generic(double *val, uint p, t_mwwalk *wk, uint vj) {
    if (wk->kind != MWK_FIXED) {
        mw_geometric(val, p, 1.0 / p);
        return;
    }
    long c = (long)TYPE_OFFSET(wk->s) - (long)TYPE_OFFSET(vj);
    ulong qs = mpz_fdiv_ui(*wk->qs, p);
    ulong cp = (ulong)(((c % (long)p) + (long)p) % (long)p);
    uint den = p - (wk->pp ? 1 : 0);
    uint N;
    if (qs == 0)
        N = cp ? 0 : p;         /* not expected: p would be allocated */
    else if (cp == 0)
        N = wk->pp ? 0 : 1;     /* r == 0 (mod p) */
    else {
        ulong x = mw_mulmod(cp, simple_invert(qs, p), p);
        ulong g = p - 1, xi = wk->xi;
        while (xi) {            /* g = gcd(xi, p - 1) */
            ulong r = g % xi;
            g = xi;
            xi = r;
        }
        N = (mw_powmod(x, (p - 1) / g, p) == 1) ? g : 0;
    }
    mw_geometric(val, p, (double)N / den);
}

/* the cost of a test that fails at trial prime p, interpolated; or with
 * which = 2 the extra cost of a factor found there that does not end it */
static double mw_scan_cost(t_mwscan *sc, uint p, uint which) {
    double *cv = (which == 2) ? sc->extra : which ? sc->prime : sc->prep;
    if (p <= sc->p[0])
        return cv[0];
    for (uint i = 1; i < sc->ns; ++i)
        if (p <= sc->p[i])
            return cv[i - 1] + (cv[i] - cv[i - 1])
                    * (double)(p - sc->p[i - 1]) / (sc->p[i] - sc->p[i - 1]);
    return cv[sc->ns - 1];
}

/* MPUGMP's primality_pretest() takes a gcd with the primes below
 * MW_PRETEST_LIM (BGCD_NEXTPRIME) for values up to 300 bits, the last
 * of them MW_PRETEST_LAST
 */
#define MW_PRETEST_LIM 1009
#define MW_PRETEST_LAST 997

/* The cost of a prime test (BPSW) of a value that passed the pretest,
 * of b bits and prime with probability r: the P rows give the mean over
 * values with no factor up to L, prime with probability P.pass, and the
 * R rows the cost on composites, from which the cost on primes follows.
 */
static double mw_ptest(double b, double r) {
    double pass = mw_interp1(&mw_P, b, 0), mean = mw_interp1(&mw_P, b, 1);
    double comp = mw_interp1(&mw_R, b, 1);
    double prime = (pass > 0) ? (mean - (1 - pass) * comp) / pass : mean;
    if (prime < comp)
        prime = comp;
    return r * prime + (1 - r) * comp;
}

/* the trial division part of the test of position vj's value for tau t
 * with exponent multiplier e; with prime set, the costs are those of a
 * prime test */
static t_mwtrial *mw_trial(
    t_mwwalk *wk, uint vj, uint t, uint e, double bits, bool prime,
    ulong excl[][MW_MAXEXCL], uint *nexcl
) {
    t_mwscan *sc = mw_scan_find(bits, 0);
    /* special primes: the small ones whose valuations are known exactly
     * (allocated ones, or all for exact values) or modified by exclusions;
     * larger allocated primes are treated as generic, an error of O(1/p),
     * since keying on them would defeat the cache */
    uint nspecial = 0;
    uint sp[16];
    double sval[16][MW_MAXV];
    ulong key = mw_hash(0xcbf29ce484222325UL, &t, sizeof(t));
    key = mw_hash(key, &e, sizeof(e));
    key = mw_hash(key, &sc->L, sizeof(sc->L));
    key = mw_hash(key, &prime, sizeof(prime));
    uint ibits = (uint)bits;
    key = mw_hash(key, &ibits, sizeof(ibits));
    key = mw_hash(key, &wk->kind, sizeof(wk->kind));
    if (wk->kind == MWK_FIXED) {
        long c = (long)TYPE_OFFSET(wk->s) - (long)TYPE_OFFSET(vj);
        key = mw_hash(key, &c, sizeof(c));
        key = mw_hash(key, &wk->xi, sizeof(wk->xi));
        key = mw_hash(key, &wk->pp, sizeof(wk->pp));
        key = mw_hash(key, &wk->khash, sizeof(wk->khash));
    }
    {
        for (uint i = 0; i < mw_ntp && mw_tp[i] <= 47; ++i) {
            uint p = mw_tp[i];
            bool alloc = 0;
            for (uint j = 0; j < wk->nalloc; ++j)
                if (wk->alloc[j] == p) { alloc = 1; break; }
            if (wk->kind == MWK_ROOT) {
                /* the root is coprime to the allocated primes */
                if (!alloc)
                    continue;
                mw_geometric(sval[nspecial], p, 0);
            } else if (wk->kind == MWK_EXACT)
                mw_valuation(sval[nspecial], p, wv_o[vj], NULL, NULL, 0);
            else if (alloc || (excl && nexcl[i]))
                mw_valuation(sval[nspecial], p, wv_o[vj], &wv_qq[vj],
                        excl ? excl[i] : NULL, excl ? nexcl[i] : 0);
            else
                continue;   /* generic, decided by the rest of the key */
            sp[nspecial++] = p;
        }
        key = mw_hash(key, sp, nspecial * sizeof(sp[0]));
        key = mw_hash(key, sval, nspecial * sizeof(sval[0]));
    }
    /* the value itself is known: find its exact valuations, uncached */
    static t_mwtrial exact_r;
    bool exact = (wk->kind == MWK_EXACT);
    t_mwtrial **slot = &mw_cache[key & (MW_CACHE - 1)];
    if (exact) {
        mpz_set(mw_tmp, wv_o[vj]);
        slot = NULL;
    } else if (*slot && (*slot)->key == key && (*slot)->t == t)
        return *slot;

    double w[t + 1], w2[t + 1], rb[t + 1], rb2[t + 1], ec[t + 1], ec2[t + 1];
    for (uint i = 0; i <= t; ++i)
        w[i] = rb[i] = ec[i] = 0;
    /* the states are the divisors of t from 2 up */
    uint nd = 0, dv[t];
    for (uint x = 2; x <= t; ++x)
        if (t % x == 0)
            dv[nd++] = x;
    w[t] = 1;
    double rej = 0, rejcost = 0, pass = 0, passcost = 0;
    /* trial division goes up to sqrt(value) if that is below L, and is
     * then complete; a prime test's pretest (primality_pretest()) only
     * takes a gcd with the primes below MW_PRETEST_LIM, leaving the rest
     * to BPSW
     */
    double L = prime ? MW_PRETEST_LIM : sc->L;
    double lim = (bits < 62) ? sqrt(pow(2.0, bits)) : L;
    bool complete = (lim < L);
    if (!complete)
        lim = L;
    uint lastp = 2;
    double Kp = 1;      /* prod q / (q - 1) over the trial primes so far */
    for (uint i = 0; i < mw_ntp && mw_tp[i] <= lim; ++i) {
        uint p = mw_tp[i];
        lastp = p;
        double gval[MW_MAXV], *val;
        uint j;
        if (exact) {
            uint a = 0;
            while (a < MW_MAXV - 1 && mpz_divisible_ui_p(mw_tmp, p)) {
                mpz_divexact_ui(mw_tmp, mw_tmp, p);
                ++a;
            }
            for (j = 0; j < MW_MAXV; ++j)
                gval[j] = (j == a);
            val = gval;
        } else {
            for (j = 0; j < nspecial; ++j)
                if (sp[j] == p)
                    break;
            if (j < nspecial)
                val = sval[j];
            else {
                mw_generic(gval, p, wk, vj);
                val = gval;
            }
        }
        /* what is left after p has no factor up to p */
        Kp *= (double)p / (p - 1);
        if (val[0] >= 1)
            continue;
        double cost = mw_scan_cost(sc, p, prime);
        double extra = mw_scan_cost(sc, p, 2);
        double lp = log2(p);
        for (uint di = 0; di < nd; ++di) {
            uint x = dv[di];
            w2[x] = rb2[x] = ec2[x] = 0;
        }
        for (uint di = 0; di < nd; ++di) {
            uint x = dv[di];
            if (w[x] == 0)
                continue;
            w2[x] += w[x] * val[0];
            rb2[x] += rb[x] * val[0];
            ec2[x] += ec[x] * val[0];
            for (uint a = 1; a < MW_MAXV; ++a) {
                double y = w[x] * val[a];
                if (y == 0)
                    continue;
                if (y < 1e-15)
                    break;      /* the rest fall geometrically */
                /* the extra cost of earlier factors found on this path */
                double yec = ec[x] * val[a];
                rejcost += yec;     /* (or passcost: see below) */
                uint et = a * e + 1;
                if (x / et == 1 && x % et == 0) {
                    /* all of tau found: passes if nothing is left, which
                     * (since what is left has no factor up to p) is when
                     * less than p is left */
                    double left = bits - rb[x] / w[x] - a * lp;
                    if (left < lp) {
                        pass += y;
                        passcost += y * cost + yec;
                        rejcost -= yec;
                    } else {
                        rej += y;
                        rejcost += y * cost;
                    }
                } else if (x % et || x / et < e + 1) {
                    rej += y;
                    rejcost += y * cost;
                } else if (x / et == e + 1 && !prime) {
                    /* the rest must be prime: prep tests it at once */
                    double left = bits - rb[x] / w[x] - a * lp;
                    double pp = (left < 2 * lp) ? 1 : Kp / (left * M_LN2);
                    if (pp > 1)
                        pp = 1;
                    double lb = left < 1 ? 1 : left;
                    pass += y * pp;
                    passcost += y * pp * (cost + mw_interp1(&mw_R, lb, 0))
                            + pp * yec;
                    rejcost -= pp * yec;
                    rej += y * (1 - pp);
                    rejcost += y * (1 - pp)
                            * (cost + mw_interp1(&mw_R, lb, 1));
                } else {
                    rejcost -= yec;
                    w2[x / et] += y;
                    rb2[x / et] += rb[x] * val[a] + y * a * lp;
                    ec2[x / et] += yec + y * extra;
                }
            }
        }
        for (uint di = 0; di < nd; ++di) {
            uint x = dv[di];
            w[x] = w2[x];
            rb[x] = rb2[x];
            ec[x] = ec2[x];
        }
    }
    /* Survivors go to the table at the size left: when trial division
     * was complete (to sqrt(value) below L), what is left is 1 or a
     * prime, and the table rows for such sizes, whose inputs have no
     * factor up to L, are for exactly that, including the cost of the
     * scan (which with batched trial division is not that of failing
     * at the last prime). */
    (void)complete;
    (void)lastp;
    t_mwtrial *r = exact ? &exact_r : *slot;
    if (!r || r->t < t) {
        if (r) {
            free(r->w);
            free(r->rb);
            free(r->ec);
        } else
            r = malloc(sizeof(t_mwtrial));
        r->w = malloc((t + 1) * sizeof(double));
        r->rb = malloc((t + 1) * sizeof(double));
        r->ec = malloc((t + 1) * sizeof(double));
    }
    r->key = key;
    r->t = t;
    r->rej = rej;
    r->rejcost = rejcost;
    r->pass = pass;
    r->passcost = passcost;
    r->Kend = Kp;
    for (uint x = 0; x <= t; ++x) {
        r->w[x] = w[x];
        r->rb[x] = w[x] > 0 ? rb[x] / w[x] : 0;
        r->ec[x] = w[x] > 0 ? ec[x] / w[x] : 0;
    }
    if (slot)
        *slot = r;
    return r;
}

/* expected outcome of one position's test: prep time, probability of
 * rejection in prep, of passing in prep, of pending for the ladder, and
 * of passing the ladder, and the ladder's time if pending */
typedef struct {
    double prep, rej, dec, pend, pass, run;
    /* with G rows: for the value if pending (weighted by the chance it
     * is), the expected cost at each rung of tau_multi_run() and the
     * chance of it aborting the call there; and its likeliest tau and
     * size, for the order of the pending values
     */
    double lc[MW_NSLOT], la[MW_NSLOT];
    uint lt;
    double lb;
} t_mwtest;

static inline ulong mw_lmask(uint b) {
    if (!mw_tmfbl)
        mw_tmfbl = get_tmfbl(&mw_tmfb_maxb, &mw_tmfb_lim);
    return (b <= mw_tmfb_maxb) ? mw_tmfbl[b] : mw_tmfb_lim;
}

/* the G size for a value of b bits: the nearest with the same rungs,
 * else the nearest
 */
static t_mwlad *mw_lad_for(double lg) {
    ulong m = mw_lmask(mw_nbits(lg));
    double b = mw_bx(lg);
    t_mwlad *best = NULL, *bestm = NULL;
    for (uint i = 0; i < mw_nlad; ++i) {
        t_mwlad *lp = &mw_lad[i];
        double d = fabs(lp->bits - b);
        if (mw_lmask(lp->bits) == m
                && (!bestm || d < fabs(bestm->bits - b)))
            bestm = lp;
        if (!best || d < fabs(best->bits - b))
            best = lp;
    }
    return bestm ? bestm : best;
}

/* What follows a factor found in a value tested for tau(n^e) = t, as in
 * tau_multi_run(), given the chance cp that the cofactor is prime: the
 * chance of aborting the call, and of going on to test the cofactor for
 * tau t2 (the rest completes the value). A factor almost always divides
 * just once, contributing e + 1.
 */
static void mw_lad_outcome(
    uint t, uint e, double cp, double *pab, double *prs, uint *t2
) {
    uint u = t / (e + 1);
    *prs = 0;
    *t2 = 0;
    if (t % (e + 1) || u == 1 || (u & 1)) {
        *pab = 1;
        return;
    }
    if (u == 2) {
        *pab = 1 - cp;      /* the cofactor must be prime */
        return;
    }
    *pab = cp;              /* the cofactor must not be prime */
    *prs = 1 - cp;
    *t2 = u;
}

static void mw_lad_standalone(uint t, uint e, double b, double *E,
        double *A);

/* Add to c[] and a[], scaled by w, the expected cost at each rung and
 * the chance of aborting there for a value of b bits tested for
 * tau(n^e) = t. Going on to test a cofactor restarts the ladder for
 * that value alone, which is counted at the rung that found the factor.
 */
static void mw_lad_slots(
    uint t, uint e, double b, double *c, double *a, double w
) {
    t_mwlad *lp = mw_lad_for(b);
    if (!lp)
        return;
    /* the rungs this run uses at this size: with -o<flake>, none from
     * QS (rung 24) on above the flake size, the values that reach it
     * going to the failure handler once the rest are done, at no cost
     * modelled here
     */
    ulong mask = mw_lmask(mw_nbits(b));
    for (uint j = 0; j < lp->nr; ++j) {
        uint r = lp->rung[j];
        if (r >= 64 || !(mask & (1UL << r)))
            continue;
        double pab, prs, Es = 0, As = 0;
        uint t2;
        mw_lad_outcome(t, e, lp->cprime[j], &pab, &prs, &t2);
        double b2 = b - lp->fbits[j];
        if (prs > 0 && b2 >= 2)
            mw_lad_standalone(t2, e, b2, &Es, &As);
        else
            pab += prs, prs = 0;
        double h = lp->reach[j] * lp->hit[j];
        double cost = (r == 24 && mw_Q.nb) ? mw_interp1(&mw_Q, b, 0)
                : lp->cost[j];
        /* unless the factor already rules it out, the cofactor gets a
         * primality test, or for odd tau is_taux(), which is quick to
         * reject a non-square: charged as a composite
         */
        uint u = (t % (e + 1)) ? 0 : t / (e + 1);
        double ct = (u < 2 || b2 < 2) ? 0
                : mw_ptest(b2, (u & 1) ? 0 : lp->cprime[j]);
        c[r] += w * (lp->reach[j] * cost + h * (ct + prs * Es));
        a[r] += w * h * (pab + prs * As);
    }
}

/* the expected cost and chance of aborting for a value tested alone */
#define MW_LMEMO 1024
typedef struct {
    uint t, e, bq;
    double E, A;
} t_mwlmemo;
static t_mwlmemo mw_lmemo[MW_LMEMO];
static void mw_lad_standalone(
    uint t, uint e, double b, double *E, double *A
) {
    uint bq = (uint)(b * 4 + 0.5);
    uint h = (t * 2654435761U ^ e * 40503U ^ bq * 69069U) % MW_LMEMO;
    t_mwlmemo *mp = &mw_lmemo[h];
    if (mp->t == t && mp->e == e && mp->bq == bq) {
        *E = mp->E;
        *A = mp->A;
        return;
    }
    double c[MW_NSLOT] = { 0 }, a[MW_NSLOT] = { 0 };
    mw_lad_slots(t, e, b, c, a, 1);
    double sc = 0, sa = 0;
    for (uint r = 0; r < MW_NSLOT; ++r) {
        sc += c[r];
        sa += a[r];
    }
    *mp = (t_mwlmemo){ .t = t, .e = e, .bq = bq, .E = sc, .A = sa };
    *E = sc;
    *A = sa;
}

/* The expected cost of tau_multi_run() on n pending values, in the
 * order it sorts them, from each one's cost and chance of aborting at
 * each rung: it runs each rung over the values in turn, stopping at the
 * first abort, so a value's cost at rung r counts only if no value
 * before it has aborted by rung r, nor any after it before rung r.
 */
static double mw_lad_interleave(uint n, t_mwtest **m) {
    double F[n], Fr[n], total = 0;
    for (uint k = 0; k < n; ++k)
        F[k] = 0;
    for (uint r = 0; r < MW_NSLOT; ++r) {
        for (uint k = 0; k < n; ++k) {
            Fr[k] = F[k] + m[k]->la[r];
            if (Fr[k] > 1)
                Fr[k] = 1;
        }
        for (uint j = 0; j < n; ++j) {
            if (m[j]->lc[r] == 0)
                continue;
            double surv = 1;
            for (uint k = 0; k < n; ++k)
                if (k != j)
                    surv *= 1 - (k < j ? Fr[k] : F[k]);
            total += m[j]->lc[r] * surv;
        }
        for (uint k = 0; k < n; ++k)
            F[k] = Fr[k];
    }
    return total;
}

/* the order in which tau_multi_run() sorts the pending values */
static int mw_lad_cmp(const void *va, const void *vb) {
    const t_mwtest *a = *(t_mwtest *const *)va, *b = *(t_mwtest *const *)vb;
    uint at2 = a->lt ^ (a->lt - 1), bt2 = b->lt ^ (b->lt - 1);
    if (at2 != bt2)
        return at2 < bt2 ? -1 : 1;
    if (a->lt != b->lt)
        return a->lt < b->lt ? -1 : 1;
    return (a->lb > b->lb) - (a->lb < b->lb);
}

/* The expected cost of the trial division a test makes on a value of
 * log2 lg with no known structure, and the chance that it finds no
 * factor: which is 0 for test_multi_append(), 1 for test_prime_append().
 * A value is taken to be divisible by each trial prime p independently
 * with probability 1/p, and the test to stop at the first, at the cost
 * the S rows give for stopping there. Cached by size.
 */
#define MW_TRMAX 1024
static double mw_tr_cost[2][MW_TRMAX], mw_tr_surv[2][MW_TRMAX];
static double mw_trial_random(double lg, uint which, double *surv) {
    uint nb = mw_nbits(lg);
    if (nb < MW_TRMAX && mw_tr_cost[which][nb] > 0) {
        *surv = mw_tr_surv[which][nb];
        return mw_tr_cost[which][nb];
    }
    t_mwscan *sc = mw_scan_find(lg, 0);
    double reach = 1, cost = 0;
    for (uint i = 0; i < mw_ntp && mw_tp[i] <= sc->L; ++i) {
        uint p = mw_tp[i];
        cost += reach / p * mw_scan_cost(sc, p, which);
        reach *= 1 - 1.0 / p;
    }
    cost += reach * mw_scan_cost(sc, sc->L, which);
    if (nb < MW_TRMAX) {
        mw_tr_cost[which][nb] = cost;
        mw_tr_surv[which][nb] = reach;
    }
    *surv = reach;
    return cost;
}

static inline double mw_lg(mpz_t n) {
    long ex;
    double d = mpz_get_d_2exp(&ex, n);
    return log2(d) + ex;
}

/* The expected cost of test_prime_append() and the prime test that
 * follows if trial division finds no factor, for the value n.
 */
double cm_price_prime(mpz_t n) {
    double lg = mw_lg(n), surv;
    double c = mw_trial_random(lg, 1, &surv);
    return c + surv * mw_interp1(&mw_P, lg, 1);
}

/* The price of tau_multi_prep() for a value of nbits bits tested for
 * tau(n^e) = t, by what it did: the S rows' cost of trial division
 * stopping at the prime p (where it found a factor ruling the value
 * out, or reached its limit or the square root), and if it ran to the
 * end, the primality test that follows, from the R rows.
 */
double cm_prep_price(uint t, uint e, uint nbits, ulong p, bool full) {
    double lg = nbits - 0.5;
    t_mwscan *sc = mw_scan_find(lg, 0);
    double c = mw_scan_cost(sc, p, 0);
    if (full)
        c += mw_interp1(&mw_R, lg, 1);
    return c;
}

/* The price of tau_prime_prep() for a value of nbits bits, by its
 * result res: 0 if trial division found a factor (the mean cost of
 * stopping at a trial prime, for a value without special structure), 1
 * if it found the value prime, 2 if a prime test must follow (whose cost
 * the P rows give with that of the trial division).
 */
double cm_pprep_price(uint nbits, int res) {
    double lg = nbits - 0.5, surv;
    if (res == 2)
        return mw_interp1(&mw_P, lg, 1);
    t_mwscan *sc = mw_scan_find(lg, 0);
    if (res == 1)
        return mw_scan_cost(sc, sc->L, 1);
    double c = mw_trial_random(lg, 1, &surv);
    double full = surv * mw_scan_cost(sc, sc->L, 1);
    return (surv < 1) ? (c - full) / (1 - surv) : c;
}

/* the table's scalar costs (see mw_C[]), in seconds */
double cm_const(uint which) {
    if (!mw_loaded)
        mw_load();
    return mw_C[which].v;
}

/* whether a cost table is available: always, since there is a built-in
 * default, unless that is empty and none is named
 */
bool cm_have_table(void) {
    static int have = -1;
    if (have < 0) {
        have = (getenv("COST_TABLE") || getenv("MOCK_WALK_TABLE")
                || cm_default_table[0]) ? 1 : 0;
        if (have && !mw_loaded)
            mw_load();
    }
    return have;
}

/* The expected cost of tau_multi_run() on the values pending in tm[0]
 * .. tm[count - 1] (those with state 0 are already done): what -ja
 * learning charges in place of the time it actually takes, which is
 * heavy-tailed. Returns -1 without a cost table ($MOCK_WALK_TABLE).
 */
double cm_ladder_cost(uint count, t_tm *tm) {
    if (!cm_have_table() || !mw_nlad)
        return -1;
    t_mwtest test[count], *m[count];
    uint n = 0;
    for (uint j = 0; j < count; ++j) {
        if (tm[j].state == 0)
            continue;
        t_mwtest *tp = &test[n];
        memset(tp, 0, sizeof(*tp));
        long ex;
        double d = mpz_get_d_2exp(&ex, tm[j].n);
        tp->lb = log2(d) + ex;
        tp->lt = tm[j].t;
        mw_lad_slots(tm[j].t, tm[j].e, tp->lb, tp->lc, tp->la, 1);
        m[n++] = tp;
    }
    if (n == 0)
        return 0;
    qsort(m, n, sizeof(t_mwtest *), &mw_lad_cmp);
    return mw_lad_interleave(n, m);
}

/* the test of position vj's value, of tau t with exponent multiplier e
 * and about 'bits' bits: trial division as above, then the table for
 * each tau still to find */
static void mw_other(
    t_mwtest *out, t_mwwalk *wk, uint vj, uint t, uint e, double bits,
    ulong excl[][MW_MAXEXCL], uint *nexcl
) {
    t_mwtrial *tr = mw_trial(wk, vj, t, e, bits, 0, excl, nexcl);
    *out = (t_mwtest){ .prep = tr->rejcost + tr->passcost, .rej = tr->rej,
            .dec = tr->pass };
    double pend_run = 0, pend_pass = 0, lbest = 0;
    out->lt = t;
    out->lb = bits;
    for (uint s = 2; s <= t; ++s) {
        double w = tr->w[s];
        if (w == 0)
            continue;
        double b = bits - tr->rb[s];
        if (b < 1)
            b = 1;
        out->prep += w * tr->ec[s];
        if (s == 2) {
            /* the rest must be prime */
            double pp = tr->Kend / (b * M_LN2);
            if (pp > 1)
                pp = 1;
            out->prep += w * mw_interp1(&mw_P, b, 1);
            out->rej += w * (1 - pp);
            out->dec += w * pp;
            continue;
        }
        double m[6];
        if (!mw_lookup(s, e, b, m)) {
            out->prep += w * 15e-6;     /* no table row: rough fallback */
            continue;
        }
        out->prep += w * m[4];
        out->rej += w * m[0];
        out->dec += w * m[1];
        out->pend += w * m[2];
        pend_pass += w * m[2] * m[3];
        pend_run += w * m[2] * m[5];
        if (mw_nlad && w * m[2] > 0) {
            mw_lad_slots(s, e, b, out->lc, out->la, w * m[2]);
            if (w * m[2] > lbest) {
                lbest = w * m[2];
                out->lt = s;
                out->lb = b;
            }
        }
    }
    out->pass = out->pend > 0 ? pend_pass / out->pend : 0;
    out->run = out->pend > 0 ? pend_run / out->pend : 0;
}

/* The expected cost after the inverse filter and any fixed power's own
 * test: C_p + P_prime * C_m, over the need_prime and need_other positions,
 * for candidates of zb bits, from the walk wk. For a linear walk, the
 * residues of ati that the inverse filter inv[] skips (making a position
 * divisible again by a prime allocated there), and those that make a
 * position that must be prime divisible by a small prime, are excluded
 * from the values reaching the later tests.
 */
static double mw_tail(
    double zb, mpz_t **q, uint *t, uint *need_prime, uint npc,
    uint *need_other, uint noc, t_mwwalk *wk, t_mod *inv, uint inv_count
) {
    if (!mw_loaded)
        mw_load();
    uint nsmall = 0;
    while (nsmall < mw_ntp && mw_tp[nsmall] <= 47)
        ++nsmall;
    /* the inverse filter's exclusions come first, so that nexcl_inv[]
     * gives them alone, for the positions that must be prime
     */
    ulong excl[nsmall][MW_MAXEXCL];
    uint nexcl[nsmall], nexcl_inv[nsmall];
    for (uint i = 0; i < nsmall; ++i) {
        nexcl[i] = nexcl_inv[i] = 0;
        if (wk->kind != MWK_LINEAR)
            continue;
        uint p = mw_tp[i];
        for (uint j = 0; j < inv_count; ++j)
            if (inv[j].m == p && nexcl[i] < MW_MAXEXCL)
                excl[i][nexcl[i]++] = inv[j].v;
        nexcl_inv[i] = nexcl[i];
        for (uint j = 0; j < npc; ++j) {
            uint vj = need_prime[j];
            ulong r = small_divmod(wv_o[vj], wv_qq[vj], p);
            if (r == p)     /* p | qq: fixed, not a residue of ati */
                continue;
            if (nexcl[i] < MW_MAXEXCL)
                excl[i][nexcl[i]++] = r ? p - r : 0;
        }
    }
    /* as test_primes(): each position's prep (the pretest) in turn until
     * one fails, then for those left pending, the prime tests in turn
     * until one fails; the P and R rows include the pretest, which for a
     * value passing it is paid in the prep, so is moved there
     */
    double pprep = 1.0, cp = 0, lf[npc], lr[npc], lc[npc];
    for (uint i = 0; i < npc; ++i) {
        uint vi = need_prime[i];
        double b = zb - log2(mpz_get_d(*q[vi]));
        if (b < 1)
            b = 1;
        t_mwtrial *tr = mw_trial(wk, vi, 2, 1, b, 1,
                wk->kind == MWK_LINEAR ? excl : NULL, nexcl_inv);
        double pc = tr->w[2];
        double bb = b - tr->rb[2];
        if (bb < 1)
            bb = 1;
        double pre = mw_scan_cost(mw_scan_find(b, 0),
                MW_PRETEST_LAST, 1);
        cp += pprep * (tr->rejcost + tr->passcost + pc * pre);
        double ok = tr->pass + pc;
        lf[i] = ok > 0 ? pc / ok : 0;
        lr[i] = tr->Kend / (bb * M_LN2);
        if (lr[i] > 1)
            lr[i] = 1;
        lc[i] = mw_ptest(bb, lr[i]) - pre;
        if (lc[i] < 0)
            lc[i] = 0;
        pprep *= ok;
    }
    double lsurv = 1, ladder_p = 0;
    for (uint i = 0; i < npc; ++i) {
        ladder_p += lsurv * lf[i] * lc[i];
        lsurv *= 1 - lf[i] + lf[i] * lr[i];
    }
    cp += pprep * ladder_p;
    double pprime = pprep * lsurv;
    /* as test_multi(): each position's prep in turn until one fails, then
     * the ladder over those left pending; with G rows, as it runs
     * (mw_lad_interleave()), else as the sum of their ladder costs alone
     */
    double cm = 0, survive = 1, ladder = 0;
    t_mwtest mo[noc], *mp[noc];
    for (uint i = 0; i < noc; ++i) {
        uint vi = need_other[i];
        t_mwtest *m = &mo[i];
        mp[i] = m;
        mw_other(m, wk, vi, t[vi], 1, zb - log2(mpz_get_d(*q[vi])),
                excl, nexcl);
        cm += survive * m->prep;
        survive *= 1 - m->rej;
        ladder += (m->rej < 1 ? m->pend / (1 - m->rej) : 0) * m->run;
        if (mw_nlad) {
            /* given that it passed the prep */
            double sc = m->rej < 1 ? 1 / (1 - m->rej) : 0;
            for (uint r = 0; r < MW_NSLOT; ++r) {
                m->lc[r] *= sc;
                m->la[r] *= sc;
            }
        }
    }
    if (mw_nlad && noc) {
        qsort(mp, noc, sizeof(mp[0]), &mw_lad_cmp);
        ladder = mw_lad_interleave(noc, mp);
    }
    cm += survive * ladder;
    return cp + pprime * cm;
}

/* set up wk for a walk: the primes allocated anywhere, and for a fixed
 * power at position s (s >= k for none) its details */
static void mw_walk_init(
    t_mwwalk *wk, uint kind, ulong *alloc, uint s, uint xi, bool pp
) {
    wk->kind = kind;
    wk->alloc = alloc;
    wk->nalloc = 0;
    for (uint vi = 0; vi < k; ++vi) {
        t_value *vp = &value[vi];
        for (uint ai = 1; ai < cur_vlevel[vi]; ++ai) {
            ulong p = vp->alloc[ai].p;
            uint j;
            for (j = 0; j < wk->nalloc; ++j)
                if (alloc[j] == p)
                    break;
            if (j == wk->nalloc)
                alloc[wk->nalloc++] = p;
        }
    }
    if (kind != MWK_FIXED)
        return;
    wk->s = s;
    wk->xi = xi;
    wk->pp = pp;
    wk->qs = &value[s].alloc[cur_vlevel[s] - 1].q;
    /* q_s with xi-th powers removed, for the character of q_s mod p */
    ulong h = 0xcbf29ce484222325UL;
    t_value *vp = &value[s];
    for (uint i = 0; i < wk->nalloc; ++i) {
        ulong p = alloc[i];
        uint x = 0;
        for (uint ai = 1; ai < cur_vlevel[s]; ++ai)
            if (vp->alloc[ai].p == p)
                x += vp->alloc[ai].x - 1;
        x %= xi;
        if (x) {
            h = mw_hash(h, &p, sizeof(p));
            h = mw_hash(h, &x, sizeof(x));
        }
    }
    wk->khash = h;
}

/* Set up the mocks, once options are handled. */
void mock_init(void) {
    mw_clock_init();
#ifdef MOCK_LEAF
    mpz_init(mr_t);
    g_ml_off = getenv("MOCK_LEAF_OFF") != NULL;
    g_mr_tail_off = getenv("MOCK_TAIL_OFF") != NULL;
#endif
}

/* walk_v(): for a linear walk or one of a single fixed power (nqc < 2),
 * charge its modelled cost instead of walking, and return TRUE. The
 * arguments are those walk_v() has prepared: the positions' q, target
 * tau and classification, the inverse filter, and for a linear walk
 * the range of ati.
 */
bool mock_walk_v(
    t_level *cur_level, mpz_t **q, uint *t, uint nqc, uint *need_square,
    uint *need_prime, uint npc, uint *need_other, uint noc, t_mod *inv,
    uint inv_count, mpz_t ati, mpz_t end
) {
    if (nqc >= 2)
        return 0;
    double mo0 = mw_clock();
    ulong mw_alloc[k * maxfact];
    t_mwwalk wk;
    if (nqc)
        mw_walk_init(&wk, MWK_FIXED, mw_alloc, need_square[0],
                divisors[t[need_square[0]]].gcddm,
                divisors[t[need_square[0]]].alldiv == 2);
    else
        mw_walk_init(&wk, MWK_LINEAR, mw_alloc, k, 0, 0);
    double tail = mw_tail(log2(mpz_get_d(zmax)), q, t, need_prime, npc,
            need_other, noc, &wk, inv, inv_count);
    double tests;
    double pinv = mw_pinv(inv, inv_count, &tests);
    double cost;
#ifdef MOCK_LEAF
    uint L = cur_level->level;
#endif
    if (nqc == 0) {
        double iters = mpz_get_d(end) - mpz_get_d(ati) + 1;
        if (iters < 0)
            iters = 0;
        double loop = MWC(MWC_LOOP0) + tests * MWC(MWC_LOOPTEST);
        cost = iters * (loop + pinv * tail);
#ifdef MOCK_LEAF
        if (L < ML_MAX && ml_state[L] == ML_PENDING) {
            ml_state[L] = ML_LEAF;
            ml_iter_cost[L] = loop + pinv * tail;
            ml_r0[L] = (mpz_get_d(zmax) - mpz_get_d(zmin))
                    / mpz_get_d(cur_level->aq);
            ml_p0[L] = cur_level->p;
        }
#endif
    } else {
#ifdef MOCK_LEAF
        if (L < ML_MAX && ml_state[L] == ML_PENDING) {
            ml_state[L] = ML_SQ;
            ml_count[L] = 1;
            ml_walk[L] = 0;
        }
#endif
        uint sqi = need_square[0];
        uint ti = t[sqi];
        uint xi = divisors[ti].gcddm;
        t_results *xr = res_array(cur_level->level);
        double qd = mpz_get_d(*q[sqi]), qqd = mpz_get_d(wv_qq[sqi]);
        double hi = pow((mpz_get_d(zmax) + TYPE_OFFSET(sqi)) / qd, 1.0 / xi);
        double lo = (mpz_sgn(zmin) > 0)
                ? pow((mpz_get_d(zmin) + TYPE_OFFSET(sqi)) / qd, 1.0 / xi) : 0;
        double iters = xr->count * (hi - lo) / qqd;
        double rbits = log2(hi > 2 ? hi : 2);
        double csq, psq;
        t_mwwalk rk = { .kind = MWK_ROOT, .alloc = wk.alloc,
                .nalloc = wk.nalloc };
        if (divisors[ti].alldiv == 2) {
            /* a prime test of the root, coprime to the allocated primes */
            t_mwtrial *tr = mw_trial(&rk, sqi, 2, 1, rbits, 1, NULL, NULL);
            double b = rbits - tr->rb[2];
            if (b < 1)
                b = 1;
            double r = tr->Kend / (b * M_LN2);
            if (r > 1)
                r = 1;
            csq = tr->rejcost + tr->passcost + tr->w[2] * mw_ptest(b, r);
            psq = tr->pass + tr->w[2] * r;
        } else {
            /* the root's own test, with no information on its
             * divisibility
             */
            t_mwtest m;
            mw_other(&m, &rk, sqi, ti, xi, rbits, NULL, NULL);
            csq = m.prep + m.pend * m.run;
            psq = m.dec + m.pend * m.pass;
        }
        double setup = MWC(MWC_SQSETUP) * (iters < 1 ? iters : 1);
        double loop = MWC(MWC_SQLOOP0) + tests * MWC(MWC_SQTEST);
        cost = setup + iters * (loop + pinv * (csq + psq * tail));
#ifdef MOCK_LEAF
        if (L < ML_MAX && ml_state[L] == ML_SQ)
            ml_walk[L] += cost;
#endif
    }
    g_mock_spent_s += cost;
    g_mock_overhead_s += mw_clock() - mo0 + g_mw_read;
    return 1;
}

/* walk_1_set(): its first MW_W1S_PREFIX primes run for real, the tests
 * of those that reach them modelled (every MW_W1S_SAMPLE-th exactly, the
 * rest charged the mean), and the rest of the primes charged at the
 * prefix's rates. walk_1_set() is not reentrant, so the state is here.
 */
static struct {
    mpz_t **q;
    ulong *alloc;
    t_mwwalk wk;
    ulong primes, pass, nsample;
    double tailsum;
} mw1;

void mock_w1s_start(void) {
    if (!mw1.q) {
        mw1.q = malloc(k * sizeof(mpz_t *));
        mw1.alloc = malloc(k * maxfact * sizeof(ulong));
    }
    for (uint vj = 0; vj < k; ++vj)
        mw1.q[vj] = &value[vj].alloc[cur_vlevel[vj] - 1].q;
    mw1.primes = mw1.pass = mw1.nsample = 0;
    mw1.tailsum = 0;
    mw_walk_init(&mw1.wk, MWK_EXACT, mw1.alloc, k, 0, 0);
}

/* the next prime p, up to phigh: TRUE if the rest has been charged */
bool mock_w1s_prime(ulong p, ulong phigh) {
    if (++mw1.primes <= MW_W1S_PREFIX)
        return 0;
    double rem = mw_li(phigh) - mw_li(p) + 1;
    double rate = (double)mw1.pass / MW_W1S_PREFIX;
    double tail = mw1.nsample ? mw1.tailsum / mw1.nsample : 0;
    g_mock_spent_s += rem * (MWC(MWC_W1SITER)
            + rate * (MWC(MWC_W1SCHECK) + tail));
    return 1;
}

/* a prime reaching the tests, with the value at w1_v and the positions'
 * values in wv_o[]
 */
void mock_w1s_pass(
    mpz_t v, uint *t, uint *need_prime, uint npc, uint *need_other, uint noc
) {
    ++mw1.pass;
    /* tested in the same order as walk_1_set() */
    oc_t = t;
    qsort(need_other, noc, sizeof(uint), &other_comparator);
    if ((mw1.pass - 1) % MW_W1S_SAMPLE == 0) {
        double mo0 = mw_clock();
        mw1.tailsum += mw_tail(log2(mpz_get_d(v)), mw1.q, t, need_prime,
                npc, need_other, noc, &mw1.wk, NULL, 0);
        ++mw1.nsample;
        g_mock_overhead_s += mw_clock() - mo0 + g_mw_read;
    }
    g_mock_spent_s += mw1.tailsum / mw1.nsample;
}

#ifdef MOCK_LEAF
/* walk_1_set() from the loop at this level: not a leaf loop */
void mock_leaf_w1s(uint level) {
    if (level < ML_MAX && ml_state[level] == ML_PENDING)
        ml_state[level] = ML_NOT;
}

/* recurse() starts a loop at this level */
void mock_loop_start(uint level) {
    if (level < ML_MAX) {
        mr_set[level] = 0;
        ml_state[level] = ML_PENDING;
        ml_count[level] = 0;
        ml_samp[level] = ml_have[level] = 0;
    }
    if (level >= 1 && level - 1 < ML_MAX
            && (ml_state[level - 1] == ML_PENDING
                || ml_state[level - 1] == ML_SQ))
        ml_state[level - 1] = ML_NOT;
}

/* recurse() resumes the loop at this level: TRUE if it is a leaf loop,
 * now charged in full
 */
bool mock_loop_leaf(uint level, t_level *cur_level) {
    if (level >= ML_MAX || ml_state[level] != ML_LEAF || g_ml_off)
        return 0;
    g_mock_spent_s += ml_stub_cost(level, cur_level->p, cur_level->limp,
            cur_level->x);
    ml_state[level] = 0;
    return 1;
}

/* recurse() has the next prime p for the loop at this level: go on with
 * it, skip it (charged), or end the loop (its tail charged)
 */
e_mock_loop mock_loop_prime(
    uint level, t_level *prev_level, t_level *cur_level, ulong p
) {
    if (level >= ML_MAX)
        return MOCK_LOOP_GO;
#ifdef CHECK_OVERFLOW
    if (!g_mr_tail_off && mr_tail(level, prev_level, cur_level, p))
        return MOCK_LOOP_END;
#endif
    if (g_ml_off)
        return MOCK_LOOP_GO;
    if (ml_state[level] == ML_SQ) {
        if (p > ML_SQ_PMIN && ml_count[level]++ % ML_STRIDE) {
            g_mock_spent_s += MWC(MWC_CPRIMESQ) + ml_walk[level];
            ++g_ml_primes_sq;
            return MOCK_LOOP_SKIP;
        }
        ml_walk[level] = 0;
    }
    if (ml_state[level] == ML_NOT) {
        /* the child just finished was in a sample block: when the block
         * is complete, take its mean cost, real and mocked, less the
         * mock's own overhead (including the clock reads bracketing it)
         */
        if (ml_samp[level] && ++ml_nsamp[level] == ML_BLOCK) {
            ml_cost[level] = ((mw_clock() - ml_t0[level]) - g_mw_read
                    - (g_mock_overhead_s - ml_ov0[level])
                    + (g_mock_spent_s - ml_m0[level])) / ML_BLOCK;
            if (ml_cost[level] < 0)
                ml_cost[level] = 0;
            g_mock_overhead_s += g_mw_read;
            ml_samp[level] = 0;
            ml_have[level] = 1;
        }
        if (p > ML_SQ_PMIN) {
            ulong pos = ml_count[level]++ % (ML_STRIDE * ML_BLOCK);
            if (ml_have[level] && pos >= ML_BLOCK) {
                g_mock_spent_s += ml_cost[level];
                ++g_ml_strided;
                return MOCK_LOOP_SKIP;
            }
            if (!ml_samp[level]) {
                ml_samp[level] = 1;
                ml_nsamp[level] = 0;
                g_mock_overhead_s += g_mw_read;
                ml_t0[level] = mw_clock();
                ml_ov0[level] = g_mock_overhead_s;
                ml_m0[level] = g_mock_spent_s;
            }
        }
    }
    return MOCK_LOOP_GO;
}
#endif
