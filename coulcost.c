/* The cost table and its models: see coulcost.h. */

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
#include "coulcost.h"

/* The cost table and the models built on it are compiled into every
 * build: the mocks (mock.c) charge them in place of the work.
 *
 * A walk costs, per iteration: loop + P_inv * (C_p + P_prime * C_m) for
 * a linear walk, loop_sq + P_inv * (C_sq + P_sq * (C_p + P_prime * C_m))
 * plus setup per walk for a fixed power (nqc == 1), where each loop cost
 * is a base plus a cost per inverse-filter entry tested. P_inv is exact
 * from inv[]; P_prime multiplies prime probabilities over need_prime
 * residuals. All costs come from the machine's cost table (see
 * cm_load() and multibench-table), so that nothing here is specific to
 * one machine or MPUGMP build.
 *
 * The test costs model trial division explicitly, following
 * tau_multi_prep(): for each position, the distribution of the valuation
 * at each trial prime p of the values reaching the tests follows from the
 * walk (see t_cmwalk), and the tau still to find as factors are divided
 * out decides a rejection or an immediate decision there (all of tau
 * found, or only a prime left to find), at the cost measured for
 * stopping at p. Trial division goes to sqrt(value) when that is below
 * its limit L, and is then complete. The table, for inputs with no trial
 * factor, gives the rest. Results are cached by what decides them, and
 * for walk_1_set(), whose values are known exactly, sampled.
 */
#define CM_MAXT 256
#define CM_MAXB 64
typedef struct {
    uint t, e, nb;
    double bits[CM_MAXB], v[CM_MAXB][6];   /* rej dec pend pass prep run */
} t_cm;
static t_cm cm_tab[CM_MAXT];
static uint cm_count = 0;
static bool cm_loaded = 0;
/* What tau_multi_prep() does with a value that has no factor up to the
 * trial limit, left to have tau(value^e) = t, depends on t and e only
 * through their class:
 *   CMT_NONE   t < e + 1: rejected at once;
 *   CMT_PRIME  t == e + 1: a prime test decides it;
 *   CMT_REJ    t > e + 1, t and e of the same parity: rejected after a
 *              prime test and a power test, since with no power found
 *              tau(value^e) is odd exactly when e is even;
 *   CMT_PEND   t > e + 1 otherwise: after the same tests, rejected if
 *              prime, else left pending for the ladder.
 * (A perfect power, which changes e, is rare enough among such values
 * to ignore, as the benches do.) So a test_multi() row of the table
 * serves every t and e of its class: those the table has no row for
 * take the row cm_cls[] gives for their class (see cm_lookup()). What
 * the ladder then does does depend on t, but is derived from the G rows
 * (see cm_lad_slots()).
 */
enum { CMT_NONE, CMT_PRIME, CMT_REJ, CMT_PEND, CMT_COUNT };
static inline uint cm_tclass(uint t, uint e) {
    if (t < e + 1)
        return CMT_NONE;
    if (t == e + 1)
        return CMT_PRIME;
    return ((t ^ e) & 1) ? CMT_PEND : CMT_REJ;
}
/* the row standing for each class, or -1 if the table has none */
static int cm_cls[CMT_COUNT];
/* Trial division: the table's rows are for inputs with no factor up to
 * the trial limit L for their size, since the model handles the trial
 * primes itself for each walk. The "L bits p" rows give L by size and
 * the "S bits p prep_us prime_us" rows the cost of a test that fails at
 * trial prime p; each set is used for sizes nearest its bits.
 */
#define CM_MAXS 64
typedef struct {
    uint bits, L, ns;
    uint p[CM_MAXS];
    double prep[CM_MAXS], prime[CM_MAXS];
    /* extra prep cost of a factor found at p that does not end prep */
    double extra[CM_MAXS];
    double KL;      /* prod p / (p - 1) over the trial primes */
} t_cmscan;
static t_cmscan cm_scan[16];
static uint cm_nscan = 0;
static uint *cm_tp = NULL, cm_ntp = 0;  /* primes up to the largest L */
static mpz_t cm_tmp;

/* prime test cost by bits: (pass rate, seconds) */
typedef struct {
    uint nb;
    double bits[CM_MAXB], v[CM_MAXB][2];
} t_cm1;
static t_cm1 cm_P, cm_R;
/* The "Q bits us fail" rows: QS alone (rung 24), whose cost depends
 * only on the size, stepping with its parameters by decimal digits.
 */
static t_cm1 cm_Q;
/* The factoring ladder of tau_multi_run() on a composite of the given
 * bits with no factor up to L, from the "G" rows: for each rung that
 * applies at that size, the fraction of values reaching it without a
 * factor found, the mean cost of an attempt, the fraction of attempts
 * finding a factor, and for those the mean bits of the factor and the
 * fraction whose cofactor is prime.
 */
#define CM_NSLOT 48     /* > TM_MAX */
#define CM_MAXLR 16     /* rungs per size */
#define CM_MAXLAD 64    /* sizes */
typedef struct {
    uint bits, nr;
    uint rung[CM_MAXLR];
    double reach[CM_MAXLR], cost[CM_MAXLR], hit[CM_MAXLR],
            fbits[CM_MAXLR], cprime[CM_MAXLR];
} t_cmlad;
static t_cmlad cm_lad[CM_MAXLAD];
static uint cm_nlad = 0;
static const ulong *cm_tmfbl;    /* the ladder's rung masks, get_tmfbl() */
static uint cm_tmfb_maxb;
static ulong cm_tmfb_lim;

/* scalars, all times in seconds */
typedef struct {
    char *name;
    double v;
    bool seen;
    bool is_time;
    double dflt;    /* if not 0, the value for a table without it */
} t_cmc;
static t_cmc cm_C[] = {
    { "loop0", 0, 0, 1 },       /* linear walk per ati */
    { "looptest", 0, 0, 1 },    /* linear walk per inverse test */
    { "sqsetup", 0, 0, 1 },     /* fixed-power walk per walk */
    { "sqloop0", 0, 0, 1 },     /* fixed-power walk per root */
    { "sqtest", 0, 0, 1 },      /* fixed-power walk per inverse test */
    { "w1siter", 0, 0, 1 },     /* walk_1_set() per prime */
    { "w1scheck", 0, 0, 1 },    /* walk_1_set() per prime passing mod check */
    /* linear walk per walk (with a value for a table that lacks it) */
    { "linsetup", 0, 0, 1, 2e-6 },
    /* Recurse loop, the further cost of each prime applied:
     * multibench-table does not fit it yet, so this value stands.
     */
    { "capply", 0, 0, 1, 0.5e-6 },
};
#define CMC(i) (cm_C[i].v)

static void cm_add1(t_cm1 *tp, double bits, double v0, double v1) {
    if (tp->nb == CM_MAXB)
        fail("cost table: table too large");
    tp->bits[tp->nb] = bits;
    tp->v[tp->nb][0] = v0;
    tp->v[tp->nb][1] = v1;
    ++tp->nb;
}

/* The table's sizes are bit counts, where the model has log2 of a value:
 * cm_bx() gives the size to look up, lg + 1/2 (values of b bits have
 * mean log2 about b - 1/2), kept within the sizes of as many limbs as
 * the value has, since costs step up with each limb.
 */
static inline uint cm_limbs(uint bits) {
    return (bits + 63) / 64;
}
static inline uint cm_nbits(double lg) {
    return (lg < 0) ? 1 : (uint)lg + 1;
}
static inline double cm_bx(double lg) {
    uint L = cm_limbs(cm_nbits(lg));
    double x = lg + 0.5, lo = 64.0 * (L - 1) + 1, hi = 64.0 * L;
    return (x < lo) ? lo : (x > hi) ? hi : x;
}

/* The trial division costs for a value with log2 lg: those of the
 * nearest size with as many limbs, else of the nearest size. With
 * create, those for exactly the given size (a bit count), made if new.
 */
static t_cmscan *cm_scan_find(double lg, bool create) {
    uint bits = create ? (uint)lg : cm_nbits(lg);
    double x = cm_bx(lg);
    t_cmscan *best = NULL, *bestl = NULL;
    for (uint i = 0; i < cm_nscan; ++i) {
        t_cmscan *sp = &cm_scan[i];
        if (create) {
            if (sp->bits == bits)
                best = sp;
            continue;
        }
        double d = fabs(sp->bits - x);
        if (!best || d < fabs(best->bits - x))
            best = sp;
        if (cm_limbs(sp->bits) == cm_limbs(bits)
                && (!bestl || d < fabs(bestl->bits - x)))
            bestl = sp;
    }
    if (bestl)
        return bestl;
    if (create && !best) {
        if (cm_nscan == sizeof(cm_scan) / sizeof(cm_scan[0]))
            fail("cost table: too many trial division sizes");
        best = &cm_scan[cm_nscan++];
        *best = (t_cmscan){ .bits = bits };
    }
    return best;
}

/* The table is the output of multibench-table: lines starting with a
 * digit are test_multi() rows "t e bits F rej dec pend pass prep run"
 * (each standing for the class of its t and e: see cm_tclass());
 * others are "C name value", "P bits F pass us", "R bits us us",
 * "S bits p us us" or "L bits p". Times in the file are in microseconds.
 */
static void cm_load(void);

/* The build that made each section of the table, from its V lines
 * "V section sha [clock]", and the unit of its times: clock "CY<GHz>"
 * for cycles at that clock rate, as pcoul reports times with the cycle
 * counter open (see work_clock()), else "CPU" for CPU seconds; with no
 * clock (a table from before it was recorded), CPU seconds.
 */
static struct {
    char section[16], sha[80];
    double ghz;
} cm_ver[16];
static uint cm_nver = 0;

/* the build that made a section of the table, or NULL if not known */
const char *cm_table_sha(const char *section) {
    if (!cm_loaded)
        cm_load();
    for (uint i = 0; i < cm_nver; ++i)
        if (strcmp(cm_ver[i].section, section) == 0)
            return cm_ver[i].sha;
    return NULL;
}

/* the unit of a section's times: cycles at this many GHz, 0 for CPU
 * seconds, or -1 if the section is not known
 */
double cm_table_ghz(const char *section) {
    if (!cm_loaded)
        cm_load();
    for (uint i = 0; i < cm_nver; ++i)
        if (strcmp(cm_ver[i].section, section) == 0)
            return cm_ver[i].ghz;
    return -1;
}

/* The next line of the table, from the file if any, else from the
 * built-in default.
 */
static char *cm_line(char *buf, size_t size, FILE *fp, const char **src) {
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

static void cm_load(void) {
    cm_loaded = 1;
    mpz_init(cm_tmp);
    /* $COST_TABLE, else the built-in */
    char *fn = getenv("COST_TABLE");
    FILE *fp = NULL;
    const char *src = cm_default_table;
    if (fn) {
        fp = fopen(fn, "r");
        if (!fp)
            fail("cost table %s: %s", fn, strerror(errno));
    } else
        fn = "(built-in)";
    char line[256], name[32];
    while (cm_line(line, sizeof(line), fp, &src)) {
        char sha[sizeof(cm_ver[0].sha)], clk[16];
        int nv = sscanf(line, "V %15s %79s %15s", name, sha, clk);
        if (nv >= 2) {
            double ghz = 0;
            if (nv == 3 && strncmp(clk, "CY", 2) == 0)
                ghz = strtod(clk + 2, NULL);
            if (cm_nver < sizeof(cm_ver) / sizeof(cm_ver[0])) {
                strcpy(cm_ver[cm_nver].section, name);
                strcpy(cm_ver[cm_nver].sha, sha);
                cm_ver[cm_nver++].ghz = ghz;
            }
            continue;
        }
        uint t, e, b, F;
        double v[6];
        if (sscanf(line, "C %31s %lf", name, &v[0]) == 2) {
            for (uint i = 0; i < CM_COUNT; ++i)
                if (strcmp(name, cm_C[i].name) == 0) {
                    cm_C[i].v = cm_C[i].is_time ? v[0] * 1e-6 : v[0];
                    cm_C[i].seen = 1;
                }
            continue;
        }
        uint r;
        if (sscanf(line, "G %u %u %lf %lf %lf %lf %lf", &b, &r, &v[0],
                &v[1], &v[2], &v[3], &v[4]) == 7 && r > 0) {
            uint i;
            for (i = 0; i < cm_nlad; ++i)
                if (cm_lad[i].bits == b)
                    break;
            if (i == cm_nlad) {
                if (cm_nlad == CM_MAXLAD)
                    fail("cost table: too many G sizes");
                cm_lad[cm_nlad++] = (t_cmlad){ .bits = b, .nr = 0 };
            }
            t_cmlad *lp = &cm_lad[i];
            if (lp->nr == CM_MAXLR)
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
            cm_add1(&cm_P, b, v[0], v[1] * 1e-6);
            continue;
        }
        if (sscanf(line, "Q %u %lf %lf", &b, &v[0], &v[1]) == 3) {
            cm_add1(&cm_Q, b, v[0] * 1e-6, v[1]);
            continue;
        }
        if (sscanf(line, "R %u %lf %lf", &b, &v[0], &v[1]) == 3) {
            cm_add1(&cm_R, b, v[0] * 1e-6, v[1] * 1e-6);
            continue;
        }
        uint p;
        int nf = sscanf(line, "S %u %u %lf %lf %lf", &b, &p, &v[0], &v[1],
                &v[2]);
        if (nf >= 4) {
            t_cmscan *sp = cm_scan_find(b, 1);
            if (sp->ns == CM_MAXS)
                fail("cost table: too many S rows");
            sp->p[sp->ns] = p;
            sp->prep[sp->ns] = v[0] * 1e-6;
            sp->extra[sp->ns] = (nf == 5 && v[2] > 0) ? v[2] * 1e-6 : 0;
            sp->prime[sp->ns++] = v[1] * 1e-6;
            continue;
        }
        if (sscanf(line, "L %u %u", &b, &p) == 2) {
            cm_scan_find(b, 1)->L = p;
            continue;
        }
        if (sscanf(line, "%u %u %u %u %lf %lf %lf %lf %lf %lf", &t, &e, &b,
                &F, &v[0], &v[1], &v[2], &v[3], &v[4], &v[5]) != 10)
            continue;
        uint i;
        for (i = 0; i < cm_count; ++i)
            if (cm_tab[i].t == t && cm_tab[i].e == e)
                break;
        if (i == cm_count) {
            if (cm_count == CM_MAXT)
                fail("cost table: table too large");
            cm_tab[cm_count++] = (t_cm){ .t = t, .e = e, .nb = 0 };
        }
        t_cm *mp = &cm_tab[i];
        if (mp->nb == CM_MAXB)
            continue;
        mp->bits[mp->nb] = b;
        v[4] *= 1e-6;
        v[5] *= 1e-6;
        memcpy(mp->v[mp->nb++], v, sizeof(v));
    }
    if (fp)
        fclose(fp);
    for (uint i = 0; i < CM_COUNT; ++i)
        if (!cm_C[i].seen) {
            if (!cm_C[i].dflt)
                fail("cost table: %s: no value for C %s", fn, cm_C[i].name);
            cm_C[i].v = cm_C[i].dflt;
        }
    if (!cm_P.nb || !cm_R.nb)
        fail("cost table: %s: need P and R rows", fn);
    if (!cm_nscan)
        fail("cost table: %s: need S and L rows", fn);
    uint maxL = 0;
    for (uint i = 0; i < cm_nscan; ++i) {
        if (!cm_scan[i].L || !cm_scan[i].ns)
            fail("cost table: %s: need S and L rows for %u bits", fn,
                    cm_scan[i].bits);
        if (cm_scan[i].L > maxL)
            maxL = cm_scan[i].L;
    }
    /* sieve the trial primes */
    char *comp = calloc(maxL + 1, 1);
    cm_tp = malloc((maxL / 2 + 2) * sizeof(uint));
    for (uint p = 2; p <= maxL; ++p) {
        if (comp[p])
            continue;
        cm_tp[cm_ntp++] = p;
        for (ulong q = (ulong)p * p; q <= maxL; q += p)
            comp[q] = 1;
    }
    free(comp);
    for (uint i = 0; i < cm_nscan; ++i) {
        cm_scan[i].KL = 1;
        for (uint j = 0; j < cm_ntp && cm_tp[j] <= cm_scan[i].L; ++j)
            cm_scan[i].KL *= (double)cm_tp[j] / (cm_tp[j] - 1);
    }
    /* The row for each class: the one multibench-table makes for it,
     * else the first the table has.
     */
    static const uint cls_te[CMT_COUNT][2] = {
        [CMT_PRIME] = { 3, 2 }, [CMT_REJ] = { 3, 1 }, [CMT_PEND] = { 4, 1 }
    };
    for (uint c = 0; c < CMT_COUNT; ++c)
        cm_cls[c] = -1;
    for (uint i = 0; i < cm_count; ++i) {
        t_cm *mp = &cm_tab[i];
        uint c = cm_tclass(mp->t, mp->e);
        if (c == CMT_NONE)
            continue;
        if (cm_cls[c] < 0 || (mp->t == cls_te[c][0] && mp->e == cls_te[c][1]))
            cm_cls[c] = i;
    }
}

/* Interpolate a one-dimensional table for a value of log2 lg (see
 * cm_bx()), geometrically for positive values.
 */
static double cm_interp1(t_cm1 *tp, double lg, uint k) {
    if (!cm_loaded)
        cm_load();
    double bits = cm_bx(lg);
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

/* Interpolate a test_multi() row for a value of bits (see cm_bx());
 * rows are in increasing bits.
 */
static void cm_interp_row(t_cm *mp, double bits, double out[6]) {
    uint j = 1;
    if (bits <= mp->bits[0]) {
        memcpy(out, mp->v[0], 6 * sizeof(double));
        return;
    }
    if (bits >= mp->bits[mp->nb - 1]) {
        memcpy(out, mp->v[mp->nb - 1], 6 * sizeof(double));
        return;
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
}

/* The test_multi() row for (t, e) for a value of log2 lg: the table's
 * own row if it has one, else that of the class of (t, e) (see
 * cm_tclass()). A class row's pass and run columns are for its own t,
 * so it is used only when the ladder comes from the G rows, which do
 * not use them. If the table has no row for the class, a CMT_PRIME or
 * CMT_REJ row is derived from the CMT_PEND row, which makes the same
 * prime test (and a power test, which CMT_PRIME does not make, so that
 * one is overcharged slightly). Returns 0 if there is nothing to go on.
 */
static bool cm_lookup(uint t, uint e, double lg, double out[6]) {
    if (!cm_loaded)
        cm_load();
    double bits = cm_bx(lg);
    for (uint i = 0; i < cm_count; ++i) {
        t_cm *mp = &cm_tab[i];
        if (mp->t == t && mp->e == e) {
            cm_interp_row(mp, bits, out);
            return 1;
        }
    }
    uint c = cm_tclass(t, e);
    if (c == CMT_NONE) {
        /* rejected before any test */
        out[0] = 1;
        out[1] = out[2] = out[3] = out[4] = out[5] = 0;
        return 1;
    }
    if (!cm_nlad)
        return 0;
    if (cm_cls[c] >= 0) {
        cm_interp_row(&cm_tab[cm_cls[c]], bits, out);
        return 1;
    }
    if (cm_cls[CMT_PEND] < 0)
        return 0;
    cm_interp_row(&cm_tab[cm_cls[CMT_PEND]], bits, out);
    double pp = out[0];     /* the fraction rejected as prime */
    out[0] = (c == CMT_PRIME) ? 1 - pp : 1;
    out[1] = (c == CMT_PRIME) ? pp : 0;
    out[2] = out[3] = out[5] = 0;
    return 1;
}

/* Exact inverse-filter pass rate: per distinct modulus m, the fraction
 * of residues mod m not excluded; if tests is non-NULL, also set it to
 * the expected number of entries tested per candidate.
 */
double cm_pinv(t_mod *inv, uint inv_count, double *tests) {
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
            if (inv[j].m == inv[i].m) {
                seen = 1;
                break;
            }
        if (seen)
            continue;
        uint distinct = 0;
        for (uint j = i; j < inv_count; ++j) {
            if (inv[j].m != inv[i].m)
                continue;
            bool dup = 0;
            for (uint l = i; l < j; ++l)
                if (inv[l].m == inv[j].m && inv[l].v == inv[j].v) {
                    dup = 1;
                    break;
                }
            if (!dup)
                ++distinct;
        }
        p *= 1.0 - (double)distinct / inv[i].m;
    }
    return p;
}

#define CM_MAXEXCL 16

/* The distribution of the valuation of a value at p, for a value
 * qq.ati + o over the ati that reach the tests, or of o itself if qq is
 * NULL: val[a] for a < CM_MAXV (the tail beyond is dropped). excl lists
 * residues of ati mod p already known not to reach the tests (because
 * they make some other position divisible by p where it may not be).
 */
#define CM_MAXV 8
static void cm_valuation(
    double *val, uint p, mpz_t o, mpz_t *qq, ulong *excl, uint nexcl
) {
    for (uint a = 0; a < CM_MAXV; ++a)
        val[a] = 0;
    /* valuations up to CM_MAXV - 1 from residues mod p^m */
    ulong pm = 1;
    uint m = 0;
    while (m < CM_MAXV - 1 && pm <= (1UL << 62) / p) {
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
        ulong r = mulmod_u64(ro % p, invert_u64(rq % p, p), p);
        r = r ? p - r : 0;
        uint ne = 0;
        bool hit = 0;
        for (uint i = 0; i < nexcl; ++i) {
            bool dup = 0;
            for (uint l = 0; l < i; ++l)
                if (excl[l] == excl[i]) {
                    dup = 1;
                    break;
                }
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
    for (uint a = b0; a < CM_MAXV; ++a) {
        val[a] += pa;
        pa /= p;
    }
}

/* The valuation of a value divisible by p with probability d, and by
 * each further power of p with probability 1/p.
 */
static void cm_geometric(double *val, uint p, double d) {
    val[0] = 1 - d;
    double pa = d * (1 - 1.0 / p);
    for (uint a = 1; a < CM_MAXV; ++a) {
        val[a] = pa;
        pa /= p;
    }
}

/* The walk a value comes from, which decides how its divisibility by the
 * trial primes is distributed. In a linear walk the values are qq.ati + o
 * with ati uniform; in a walk of a fixed power at position s, with
 * cand + off_s = q_s.r^xi and r uniform, position j has q_j.v_j =
 * q_s.r^xi - c for c = off_s - off_j, so p divides v_j for as many r
 * mod p as c / q_s has xi-th roots: for xi == 2, when q_s.c is a square
 * v_j factorizes algebraically, and is divisible by p about twice as often.
 */
/* The outcome of trial division of one value: probability and cost of
 * rejection there, and for each tau s still to find the probability of
 * surviving with it and the expected bits divided out meanwhile.
 */
typedef struct {
    ulong key;
    uint t;
    double rej, rejcost;
    double pass, passcost;  /* completed within trial division */
    double *ec;             /* extra scan cost carried by each survivor */
    /* Kend is prod q / (q - 1) over the trial primes used: a survivor
     * of b bits is prime with probability Kend / (b ln 2).
     */
    double Kend;
    double *w, *rb;
} t_cmtrial;
#define CM_CACHE (1 << 16)
static t_cmtrial *cm_cache[CM_CACHE];

/* hash n bytes into h, a word at a time */
static inline ulong cm_hash(ulong h, const void *p, size_t n) {
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

/* The valuation at p of position vj's value, for p not handled by the
 * key's special cases.
 */
static void cm_generic(double *val, uint p, t_cmwalk *wk, uint vj) {
    if (wk->kind != CMK_FIXED) {
        cm_geometric(val, p, 1.0 / p);
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
        ulong x = mulmod_u64(cp, invert_u64(qs, p), p);
        ulong g = p - 1, xi = wk->xi;
        while (xi) {            /* g = gcd(xi, p - 1) */
            ulong r = g % xi;
            g = xi;
            xi = r;
        }
        N = (powmod_u64(x, (p - 1) / g, p) == 1) ? g : 0;
    }
    cm_geometric(val, p, (double)N / den);
}

/* The cost of a test that fails at trial prime p, interpolated; or with
 * which = 2 the extra cost of a factor found there that does not end it.
 */
static double cm_scan_cost(t_cmscan *sc, uint p, uint which) {
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
 * CM_PRETEST_LIM (BGCD_NEXTPRIME) for values up to 300 bits, the last
 * of them CM_PRETEST_LAST.
 */
#define CM_PRETEST_LIM 1009
#define CM_PRETEST_LAST 997

/* The cost of a prime test (BPSW) of a value that passed the pretest,
 * of b bits and prime with probability r: the P rows give the mean over
 * values with no factor up to L, prime with probability P.pass, and the
 * R rows the cost on composites, from which the cost on primes follows.
 */
static double cm_ptest(double b, double r) {
    double pass = cm_interp1(&cm_P, b, 0), mean = cm_interp1(&cm_P, b, 1);
    double comp = cm_interp1(&cm_R, b, 1);
    double prime = (pass > 0) ? (mean - (1 - pass) * comp) / pass : mean;
    if (prime < comp)
        prime = comp;
    return r * prime + (1 - r) * comp;
}

/* The trial division part of the test of position vj's value for tau t
 * with exponent multiplier e; with prime set, the costs are those of a
 * prime test.
 */
static t_cmtrial *cm_trial(
    t_cmwalk *wk, uint vj, uint t, uint e, double bits, bool prime,
    ulong excl[][CM_MAXEXCL], uint *nexcl
) {
    t_cmscan *sc = cm_scan_find(bits, 0);
    /* Special primes: the small ones whose valuations are known exactly
     * (allocated ones, or all for exact values) or modified by exclusions;
     * larger allocated primes are treated as generic, an error of O(1/p),
     * since keying on them would defeat the cache.
     */
    uint nspecial = 0;
    uint sp[16];
    double sval[16][CM_MAXV];
    ulong key = cm_hash(0xcbf29ce484222325UL, &t, sizeof(t));
    key = cm_hash(key, &e, sizeof(e));
    key = cm_hash(key, &sc->L, sizeof(sc->L));
    key = cm_hash(key, &prime, sizeof(prime));
    uint ibits = (uint)bits;
    key = cm_hash(key, &ibits, sizeof(ibits));
    key = cm_hash(key, &wk->kind, sizeof(wk->kind));
    if (wk->kind == CMK_FIXED) {
        long c = (long)TYPE_OFFSET(wk->s) - (long)TYPE_OFFSET(vj);
        key = cm_hash(key, &c, sizeof(c));
        key = cm_hash(key, &wk->xi, sizeof(wk->xi));
        key = cm_hash(key, &wk->pp, sizeof(wk->pp));
        key = cm_hash(key, &wk->khash, sizeof(wk->khash));
    }
    {
        for (uint i = 0; i < cm_ntp && cm_tp[i] <= 47; ++i) {
            uint p = cm_tp[i];
            bool alloc = 0;
            for (uint j = 0; j < wk->nalloc; ++j)
                if (wk->alloc[j] == p) {
                    alloc = 1;
                    break;
                }
            if (wk->kind == CMK_ROOT) {
                /* the root is coprime to the allocated primes */
                if (!alloc)
                    continue;
                cm_geometric(sval[nspecial], p, 0);
            } else if (wk->kind == CMK_EXACT)
                cm_valuation(sval[nspecial], p, wv_o[vj], NULL, NULL, 0);
            else if (alloc || (excl && nexcl[i]))
                cm_valuation(sval[nspecial], p, wv_o[vj], &wv_qq[vj],
                        excl ? excl[i] : NULL, excl ? nexcl[i] : 0);
            else
                continue;   /* generic, decided by the rest of the key */
            sp[nspecial++] = p;
        }
        key = cm_hash(key, sp, nspecial * sizeof(sp[0]));
        key = cm_hash(key, sval, nspecial * sizeof(sval[0]));
    }
    /* the value itself is known: find its exact valuations, uncached */
    static t_cmtrial exact_r;
    bool exact = (wk->kind == CMK_EXACT);
    t_cmtrial **slot = &cm_cache[key & (CM_CACHE - 1)];
    if (exact) {
        mpz_set(cm_tmp, wv_o[vj]);
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
    /* Trial division goes up to sqrt(value) if that is below L, and is
     * then complete; a prime test's pretest (primality_pretest()) only
     * takes a gcd with the primes below CM_PRETEST_LIM, leaving the rest
     * to BPSW.
     */
    double L = prime ? CM_PRETEST_LIM : sc->L;
    double lim = (bits < 62) ? sqrt(pow(2.0, bits)) : L;
    bool complete = (lim < L);
    if (!complete)
        lim = L;
    uint lastp = 2;
    double Kp = 1;      /* prod q / (q - 1) over the trial primes so far */
    for (uint i = 0; i < cm_ntp && cm_tp[i] <= lim; ++i) {
        uint p = cm_tp[i];
        lastp = p;
        double gval[CM_MAXV], *val;
        uint j;
        if (exact) {
            uint a = 0;
            while (a < CM_MAXV - 1 && mpz_divisible_ui_p(cm_tmp, p)) {
                mpz_divexact_ui(cm_tmp, cm_tmp, p);
                ++a;
            }
            for (j = 0; j < CM_MAXV; ++j)
                gval[j] = (j == a);
            val = gval;
        } else {
            for (j = 0; j < nspecial; ++j)
                if (sp[j] == p)
                    break;
            if (j < nspecial)
                val = sval[j];
            else {
                cm_generic(gval, p, wk, vj);
                val = gval;
            }
        }
        /* what is left after p has no factor up to p */
        Kp *= (double)p / (p - 1);
        if (val[0] >= 1)
            continue;
        double cost = cm_scan_cost(sc, p, prime);
        double extra = cm_scan_cost(sc, p, 2);
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
            for (uint a = 1; a < CM_MAXV; ++a) {
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
                    /* All of tau found: passes if nothing is left, which
                     * (since what is left has no factor up to p) is when
                     * less than p is left.
                     */
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
                    passcost += y * pp * (cost + cm_interp1(&cm_R, lb, 0))
                            + pp * yec;
                    rejcost -= pp * yec;
                    rej += y * (1 - pp);
                    rejcost += y * (1 - pp)
                            * (cost + cm_interp1(&cm_R, lb, 1));
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
     * at the last prime).
     */
    (void)complete;
    (void)lastp;
    t_cmtrial *r = exact ? &exact_r : *slot;
    if (!r || r->t < t) {
        if (r) {
            free(r->w);
            free(r->rb);
            free(r->ec);
        } else
            r = malloc(sizeof(t_cmtrial));
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

/* Expected outcome of one position's test: prep time, probability of
 * rejection in prep, of passing in prep, of pending for the ladder, and
 * of passing the ladder, and the ladder's time if pending.
 */
struct s_mwtest {
    double prep, rej, dec, pend, pass, run;
    /* With G rows: for the value if pending (weighted by the chance it
     * is), the expected cost at each rung of tau_multi_run() and the
     * chance of it aborting the call there; and its likeliest tau and
     * size, for the order of the pending values.
     */
    double lc[CM_NSLOT], la[CM_NSLOT];
    uint lt;
    double lb;
};

static inline ulong cm_lmask(uint b) {
    if (!cm_tmfbl)
        cm_tmfbl = get_tmfbl(&cm_tmfb_maxb, &cm_tmfb_lim);
    return (b <= cm_tmfb_maxb) ? cm_tmfbl[b] : cm_tmfb_lim;
}

/* The G size for a value of b bits: the nearest with the same rungs,
 * else the nearest.
 */
static t_cmlad *cm_lad_for(double lg) {
    ulong m = cm_lmask(cm_nbits(lg));
    double b = cm_bx(lg);
    t_cmlad *best = NULL, *bestm = NULL;
    for (uint i = 0; i < cm_nlad; ++i) {
        t_cmlad *lp = &cm_lad[i];
        double d = fabs(lp->bits - b);
        if (cm_lmask(lp->bits) == m
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
static void cm_lad_outcome(
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

static void cm_lad_standalone(uint t, uint e, double b, double *E,
        double *A);

/* Add to c[] and a[], scaled by w, the expected cost at each rung and
 * the chance of aborting there for a value of b bits tested for
 * tau(n^e) = t. Going on to test a cofactor restarts the ladder for
 * that value alone, which is counted at the rung that found the factor.
 */
static void cm_lad_slots(
    uint t, uint e, double b, double *c, double *a, double w
) {
    t_cmlad *lp = cm_lad_for(b);
    if (!lp)
        return;
    /* The rungs this run uses at this size: with -o<flake>, none from
     * QS (rung 24) on above the flake size, the values that reach it
     * going to the failure handler once the rest are done, at no cost
     * modelled here.
     */
    ulong mask = cm_lmask(cm_nbits(b));
    for (uint j = 0; j < lp->nr; ++j) {
        uint r = lp->rung[j];
        if (r >= 64 || !(mask & (1UL << r)))
            continue;
        double pab, prs, Es = 0, As = 0;
        uint t2;
        cm_lad_outcome(t, e, lp->cprime[j], &pab, &prs, &t2);
        double b2 = b - lp->fbits[j];
        if (prs > 0 && b2 >= 2)
            cm_lad_standalone(t2, e, b2, &Es, &As);
        else
            pab += prs, prs = 0;
        double h = lp->reach[j] * lp->hit[j];
        double cost = (r == 24 && cm_Q.nb) ? cm_interp1(&cm_Q, b, 0)
                : lp->cost[j];
        /* Unless the factor already rules it out, the cofactor gets a
         * primality test, or for odd tau is_taux(), which is quick to
         * reject a non-square: charged as a composite.
         */
        uint u = (t % (e + 1)) ? 0 : t / (e + 1);
        double ct = (u < 2 || b2 < 2) ? 0
                : cm_ptest(b2, (u & 1) ? 0 : lp->cprime[j]);
        c[r] += w * (lp->reach[j] * cost + h * (ct + prs * Es));
        a[r] += w * h * (pab + prs * As);
    }
}

/* the expected cost and chance of aborting for a value tested alone */
#define CM_LMEMO 1024
typedef struct {
    uint t, e, bq;
    double E, A;
} t_cmlmemo;
static t_cmlmemo cm_lmemo[CM_LMEMO];
static void cm_lad_standalone(
    uint t, uint e, double b, double *E, double *A
) {
    uint bq = (uint)(b * 4 + 0.5);
    uint h = (t * 2654435761U ^ e * 40503U ^ bq * 69069U) % CM_LMEMO;
    t_cmlmemo *mp = &cm_lmemo[h];
    if (mp->t == t && mp->e == e && mp->bq == bq) {
        *E = mp->E;
        *A = mp->A;
        return;
    }
    double c[CM_NSLOT] = { 0 }, a[CM_NSLOT] = { 0 };
    cm_lad_slots(t, e, b, c, a, 1);
    double sc = 0, sa = 0;
    for (uint r = 0; r < CM_NSLOT; ++r) {
        sc += c[r];
        sa += a[r];
    }
    *mp = (t_cmlmemo){ .t = t, .e = e, .bq = bq, .E = sc, .A = sa };
    *E = sc;
    *A = sa;
}

/* The expected cost of tau_multi_run() on n pending values, in the
 * order it sorts them, from each one's cost and chance of aborting at
 * each rung: it runs each rung over the values in turn, stopping at the
 * first abort, so a value's cost at rung r counts only if no value
 * before it has aborted by rung r, nor any after it before rung r.
 */
static double cm_lad_interleave(uint n, t_cmtest **m) {
    double F[n], Fr[n], total = 0;
    for (uint k = 0; k < n; ++k)
        F[k] = 0;
    for (uint r = 0; r < CM_NSLOT; ++r) {
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
static int cm_lad_cmp(const void *va, const void *vb) {
    const t_cmtest *a = *(t_cmtest *const *)va, *b = *(t_cmtest *const *)vb;
    uint at2 = a->lt ^ (a->lt - 1), bt2 = b->lt ^ (b->lt - 1);
    if (at2 != bt2)
        return at2 < bt2 ? -1 : 1;
    if (a->lt != b->lt)
        return a->lt < b->lt ? -1 : 1;
    return (a->lb > b->lb) - (a->lb < b->lb);
}

/* the table's scalar costs (see cm_C[]), in seconds */
double cm_const(uint which) {
    if (!cm_loaded)
        cm_load();
    return cm_C[which].v;
}

/* count of the times cm_other() has found no row in the table for a test */
static ulong cm_missing = 0;

/* The test of position vj's value, of tau t with exponent multiplier e
 * and about 'bits' bits: trial division as above, then the table for
 * each tau still to find.
 */
static void cm_other(
    t_cmtest *out, t_cmwalk *wk, uint vj, uint t, uint e, double bits,
    ulong excl[][CM_MAXEXCL], uint *nexcl
) {
    t_cmtrial *tr = cm_trial(wk, vj, t, e, bits, 0, excl, nexcl);
    *out = (t_cmtest){ .prep = tr->rejcost + tr->passcost, .rej = tr->rej,
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
            out->prep += w * cm_interp1(&cm_P, b, 1);
            out->rej += w * (1 - pp);
            out->dec += w * pp;
            continue;
        }
        double m[6];
        if (!cm_lookup(s, e, b, m)) {
            out->prep += w * 15e-6;     /* no table row: rough fallback */
            ++cm_missing;
            continue;
        }
        out->prep += w * m[4];
        out->rej += w * m[0];
        out->dec += w * m[1];
        out->pend += w * m[2];
        pend_pass += w * m[2] * m[3];
        pend_run += w * m[2] * m[5];
        if (cm_nlad && w * m[2] > 0) {
            cm_lad_slots(s, e, b, out->lc, out->la, w * m[2]);
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
 * If root is given, it is the test of a fixed power's root that is left
 * pending: it stays queued through the prime tests, and runs in the ladder
 * with the need_other positions.
 */
double cm_tail(
    double zb, mpz_t **q, uint *t, uint *need_prime, uint npc,
    uint *need_other, uint noc, t_cmwalk *wk, t_mod *inv, uint inv_count,
    t_cmtest *root
) {
    if (!cm_loaded)
        cm_load();
    uint nsmall = 0;
    while (nsmall < cm_ntp && cm_tp[nsmall] <= 47)
        ++nsmall;
    /* The inverse filter's exclusions come first, so that nexcl_inv[]
     * gives them alone, for the positions that must be prime.
     */
    ulong excl[nsmall][CM_MAXEXCL];
    uint nexcl[nsmall], nexcl_inv[nsmall];
    for (uint i = 0; i < nsmall; ++i) {
        nexcl[i] = nexcl_inv[i] = 0;
        if (wk->kind != CMK_LINEAR)
            continue;
        uint p = cm_tp[i];
        for (uint j = 0; j < inv_count; ++j)
            if (inv[j].m == p && nexcl[i] < CM_MAXEXCL)
                excl[i][nexcl[i]++] = inv[j].v;
        nexcl_inv[i] = nexcl[i];
        for (uint j = 0; j < npc; ++j) {
            uint vj = need_prime[j];
            ulong r = small_divmod(wv_o[vj], wv_qq[vj], p);
            if (r == p)     /* p | qq: fixed, not a residue of ati */
                continue;
            if (nexcl[i] < CM_MAXEXCL)
                excl[i][nexcl[i]++] = r ? p - r : 0;
        }
    }
    /* As test_primes(): each position's prep (the pretest) in turn until
     * one fails, then for those left pending, the prime tests in turn
     * until one fails; the P and R rows include the pretest, which for a
     * value passing it is paid in the prep, so is moved there.
     */
    double pprep = 1.0, cp = 0, lf[npc], lr[npc], lc[npc];
    for (uint i = 0; i < npc; ++i) {
        uint vi = need_prime[i];
        double b = zb - log2(mpz_get_d(*q[vi]));
        if (b < 1)
            b = 1;
        t_cmtrial *tr = cm_trial(wk, vi, 2, 1, b, 1,
                wk->kind == CMK_LINEAR ? excl : NULL, nexcl_inv);
        double pc = tr->w[2];
        double bb = b - tr->rb[2];
        if (bb < 1)
            bb = 1;
        double pre = cm_scan_cost(cm_scan_find(b, 0),
                CM_PRETEST_LAST, 1);
        cp += pprep * (tr->rejcost + tr->passcost + pc * pre);
        double ok = tr->pass + pc;
        lf[i] = ok > 0 ? pc / ok : 0;
        lr[i] = tr->Kend / (bb * M_LN2);
        if (lr[i] > 1)
            lr[i] = 1;
        lc[i] = cm_ptest(bb, lr[i]) - pre;
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
    /* As test_multi(): each position's prep in turn until one fails, then
     * the ladder over those left pending; with G rows, as it runs
     * (cm_lad_interleave()), else as the sum of their ladder costs alone.
     */
    double cm = 0, survive = 1, ladder = 0;
    t_cmtest mo[noc + 1], *mp[noc + 1];
    uint nlad = noc;
    for (uint i = 0; i < noc; ++i) {
        uint vi = need_other[i];
        t_cmtest *m = &mo[i];
        mp[i] = m;
        cm_other(m, wk, vi, t[vi], 1, zb - log2(mpz_get_d(*q[vi])),
                excl, nexcl);
        cm += survive * m->prep;
        survive *= 1 - m->rej;
        ladder += (m->rej < 1 ? m->pend / (1 - m->rej) : 0) * m->run;
        if (cm_nlad) {
            /* given that it passed the prep */
            double sc = m->rej < 1 ? 1 / (1 - m->rej) : 0;
            for (uint r = 0; r < CM_NSLOT; ++r) {
                m->lc[r] *= sc;
                m->la[r] *= sc;
            }
        }
    }
    if (root && cm_nlad) {
        /* given that it is pending */
        t_cmtest *m = &mo[noc];
        double sc = root->pend > 0 ? 1 / root->pend : 0;
        *m = *root;
        for (uint r = 0; r < CM_NSLOT; ++r) {
            m->lc[r] *= sc;
            m->la[r] *= sc;
        }
        mp[nlad++] = m;
    } else if (root)
        ladder = root->run + root->pass * ladder;
    if (cm_nlad && nlad) {
        qsort(mp, nlad, sizeof(mp[0]), &cm_lad_cmp);
        ladder = cm_lad_interleave(nlad, mp);
    }
    cm += survive * ladder;
    return cp + pprime * cm;
}

/* Set up wk for a walk: the primes allocated anywhere, and for a fixed
 * power at position s (s >= k for none) its details.
 */
void cm_walk_init(
    t_cmwalk *wk, uint kind, ulong *alloc, uint s, uint xi, bool pp
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
    if (kind != CMK_FIXED)
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
            h = cm_hash(h, &p, sizeof(p));
            h = cm_hash(h, &x, sizeof(x));
        }
    }
    wk->khash = h;
}

/* The modelled cost per root of a walk of a single fixed power at
 * position sqi, with candidates of zb bits and roots of rbits: the loop,
 * and for the roots that pass the inverse filter, the root's own test
 * and what follows it. The other arguments are as walk_v() prepares them.
 */
double cm_root_cost(
    double zb, double rbits, mpz_t **q, uint *t, uint sqi, uint *need_prime,
    uint npc, uint *need_other, uint noc, t_mod *inv, uint inv_count
) {
    uint ti = t[sqi];
    uint xi = divisors[ti].gcddm;
    ulong cm_alloc[k * maxfact];
    t_cmwalk wk;
    cm_walk_init(&wk, CMK_FIXED, cm_alloc, sqi, xi, divisors[ti].alldiv == 2);
    double tail = cm_tail(zb, q, t, need_prime, npc, need_other, noc, &wk,
            inv, inv_count, NULL);
    double tests;
    double pinv = cm_pinv(inv, inv_count, &tests);
    double after;
    t_cmwalk rk = { .kind = CMK_ROOT, .alloc = wk.alloc,
            .nalloc = wk.nalloc };
    if (divisors[ti].alldiv == 2) {
        /* a prime test of the root, coprime to the allocated primes */
        t_cmtrial *tr = cm_trial(&rk, sqi, 2, 1, rbits, 1, NULL, NULL);
        double b = rbits - tr->rb[2];
        if (b < 1)
            b = 1;
        double r = tr->Kend / (b * M_LN2);
        if (r > 1)
            r = 1;
        after = tr->rejcost + tr->passcost + tr->w[2] * cm_ptest(b, r)
                + (tr->pass + tr->w[2] * r) * tail;
    } else {
        /* The root's own test, with no information on its divisibility.
         * If trial division does not settle it, the rest is left for
         * the ladder, once the primes have passed.
         */
        t_cmtest m;
        cm_other(&m, &rk, sqi, ti, xi, rbits, NULL, NULL);
        after = m.prep + m.dec * tail;
        if (m.pend > 0)
            after += m.pend * cm_tail(zb, q, t, need_prime, npc, need_other,
                    noc, &wk, inv, inv_count, &m);
    }
    return CMC(CM_SQLOOP0) + tests * CMC(CM_SQTEST) + pinv * after;
}
