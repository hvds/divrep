/* The cost table: see coulcost.h. */

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

/* The cost table is compiled into every build. All its costs are
 * measured on one machine and MPUGMP build (see cm_load() and
 * multibench-table), so that nothing using them need be specific to
 * either.
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
 * digit are test_multi() rows "t e bits F rej dec pend pass prep run";
 * others are "C name value", "P bits F pass us", "R bits us us",
 * "S bits p us us" or "L bits p". Times in the file are in microseconds.
 */
static void cm_load(void);

/* the build that made each section of the table, from its V lines */
static struct {
    char section[16], sha[80];
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
        char sha[sizeof(cm_ver[0].sha)];
        if (sscanf(line, "V %15s %79s", name, sha) == 2) {
            if (cm_nver < sizeof(cm_ver) / sizeof(cm_ver[0])) {
                strcpy(cm_ver[cm_nver].section, name);
                strcpy(cm_ver[cm_nver++].sha, sha);
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
}
