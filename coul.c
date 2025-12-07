/* needed on FreeBSD for getline() to be exported from stdio.h */
#define _WITH_GETLINE

#include <stdlib.h>
#include <stdio.h>
#include <unistd.h>
#include <stdarg.h>
#include <string.h>
#include <errno.h>
#include <assert.h>
#ifdef HAVE_SETPROCTITLE
#   include <sys/types.h>
#endif
#include <signal.h>
#include <time.h>
#include <ctype.h>
#include <sys/time.h>
#include <sys/resource.h>

#include "coul.h"
#include "coulfact.h"
#include "diag.h"
#include "rootmod.h"
#include "coultau.h"
#include "pell.h"
#include "coulvec.h"
#include "assume.h"

/* from MPUG */
#include "factor.h"
#include "gmp_main.h"
#include "utility.h"
#include "primality.h"

/* primary parameters - we are searching for f(n, k), the least d such
 * that for all 0 <= i < k:
 *   (if compiled with TYPE_o): tau(d + i) = n
 *   (if compiled with TYPE_a): tau(d + in) = n
 *   (if compiled with TYPE_r): tau(d + i) = tau(n + i), d <> n
 *   (if compiled with TYPE_t): tau(n + di) = tau(n)
 * (TYPE_t not yet supported.)
 */
uint n, k;

/* mpz_t passed as function parameter decays to pointer in a way that
 * allows it to be used as mpz_t, but cannot be converted to a pointer
 * in a typesafe manner. Given a function called as foo(z), use this as
 *   mpz_t *zp = PARAM_TO_PTR(z);
 */
static inline mpz_t *PARAM_TO_PTR(__mpz_struct *z) {
    return (mpz_t *)z;
}

/* We assume x != 0 */
#ifdef __GNUC__
    static inline bool ispow2(ulong x) {
        return __builtin_popcountl(x) == 1;
    }
#else
    static inline bool ispow2(ulong x) {
        return (x & (x - 1)) == 0;
    }
#endif

/* stash of mpz_t, initialized once at start */
typedef enum {
    zero, zone,                 /* constants */
    temp,
    tfp_v,                      /* test_forcep */
    sqm_t, sqm_q, sqm_b, sqm_z, sqm_x,  /* sqrtmod_t */
    uc_minusvi, uc_px,          /* update_chinese */
    ur_a, ur_m, ur_ipg,         /* update_residues */
    asq_o, asq_qq, asq_m,       /* alloc_square */
    wv_ati, wv_end, wv_cand,    /* walk_v */
    wv_startr, wv_endr, wv_qqr, wv_qqnext, wv_r, wv_rx, wv_temp,
    wv_x, wv_y, wv_x2, wv_y2,
    w1_v, w1_j, w1_r,           /* walk_1 */
    w1_m, w1_mr,
    lp_x, lp_mint, lp_mint2,    /* limit_p */
    r_walk,                     /* recurse */

    sdm_p, sdm_r,               /* small_divmod (TODO) */
    dm_r,                       /* divmod */
    np_p,                       /* next_prime */
    s_exp, uls_temp,            /* ston, ulston */
    j4a, j4b, j4m, j4p, j4q,    /* best_6x() */

    MAX_ZSTASH
} t_zstash;
mpz_t *zstash;
static inline mpz_t *ZP(t_zstash e) { return &zstash[e]; }
#define Z(e) *ZP(e)
/* additional arrays of mpz_t initialized once at start */
mpz_t *wv_o, *wv_qq;        /* size [k] */
mpz_t *mint_best, *mint_px; /* size [sumpm(n / high(n))] */
/* for failure diagnostics */
mpz_t *g_q0;
uint g_ati;

/* used to store disallowed inverses in walk_v() */
typedef struct s_mod {
    ulong v;
    ulong m;
} t_mod;

/* warn if the divisor array will be bigger than this */
#define DIVISOR_WARN_LIMIT (100000)
t_divisors *divisors = NULL;
#if defined(TYPE_r)
    uint *target_tau = NULL;
    uint target_lcm;
    static inline uint target_t(uint vi) { return target_tau[vi]; }
#else
#   define target_lcm (n)
    static inline uint target_t(uint vi) { return n; }
#endif

/* For prime p < k, we "force" allocation of powers in a batch to ensure
 * that multiple allocations of the same prime are coherent. Whereas normal
 * allocation considers only p^{x-1} where x is divisible by the highest
 * prime dividing t_i, forced primes may allocate any p^{x-1} with x | t_i.
 *
 * For cases where two or more v_i are divisible by p, we always force
 * every possible case. For cases where only one v_i is divisible by p,
 * we force them only if n == 2 (mod 4) (heuristically, since allocations
 * are always either at least as powerful as normal allocations _or_ they
 * have x=2, leaving v_i.t odd) or if requested by the -f option (force_all).
 *
 * The "primary" of a batch is the least index v_i at which the greatest
 * power of p appears.
 */
typedef struct s_forcebatch {
    uint primary;   /* x[primary] is first max */
    uint x[0];      /* allocate p^{x-1} at v_i for i: 0..k-1 */
} t_forcebatch;
static inline size_t size_forcebatch(void) {
    return sizeof(t_forcebatch) + k * sizeof(uint);
}
typedef struct s_forcep {
    uint p;
    uint count;
    t_forcebatch *batch;    /* beware, struct is dynamically sized */
} t_forcep;
t_forcep *forcep = NULL;
uint forcedp;
uint force_all = 0;
uint unforce_all = 0;

/* When allocation forces the residue of some v_i to be square, we want
 * to calculate the roots mod every allocation (before and after this one),
 * first to check if a solution is possible, and second to avoid duplicate
 * work when we actually use the roots in walk_v().
 * The set of roots lives in resarray(level), but here we track what power
 * root they are: the allocation at value[sq0].alloc[i] leaves gcddm sqg[i].
 */
uint sq0 = 0;
uint *sqg = NULL;   /* size maxfact */

uint maxlevel;              /* avvailable entries in levels[] */
t_level *levels = NULL;     /* one level per allocated prime */
uint level = 0;             /* current recursion level */
uint final_level = 0;       /* level at which to terminate */
t_value *value = NULL;      /* v_0 .. v_{k-1} */

static inline void level_setp(t_level *lp, ulong p) {
    lp->p = p;
    prime_iterator_setprime(&lp->piter, p);
}

/* reset allocations at this level to those at previous level */
static inline void reset_vlevel(t_level *cur_level) {
    assert(cur_level->level > 0);
    t_level *prev_level = &levels[cur_level->level - 1];
    memcpy(cur_level->vlevel, prev_level->vlevel, k * sizeof(uint));
}

/* list of some small primes, at least enough for one per allocation,
 * and a reverse lookup */
uint *sprimes = NULL;
uint *ptoi = NULL;
uint nsprimes;
uint lastprime;

/* set to utime at start of run, minus last timestamp of recovery file */
double t0 = 0;
struct rusage rusage_buf;
static inline double utime(void) {
    getrusage(RUSAGE_SELF, &rusage_buf);
    return (double)rusage_buf.ru_utime.tv_sec
            + (double)rusage_buf.ru_utime.tv_usec / 1000000;
}
timer_t diag_timerid, log_timerid;
volatile bool need_work, need_diag, need_log;
bool clock_is_realtime = 0;

mpz_t zmin, zmax;   /* limits to check for v_0 */
mpz_t best;         /* best solution seen */
bool improve_max = 1;   /* reduce zmax when solution found */
uint seen_best = 0; /* number of times we've improved zmax */
ulong gain = 0;     /* used to fine-tune balance of recursion vs. walk */
ulong antigain = 0;
ulong gain2 = 0;    /* as gain/antigain for squares */
ulong antigain2 = 0;
/* maxp[e] is the greatest prime we should attempt to allocate as power p^e;
 * minp[e] is the threshold that at least one allocated p^e should exceed
 * (else we can skip the walk); midp[e] is the additional threshold up to
 * which we should pre-walk.
 * sminp, smaxp, smidp are the strings that express the requests.
 */
ulong *minp = NULL, *maxp = NULL, *midp = NULL;
char *sminp = NULL, *smaxp = NULL, *smidp = NULL;
char *sminpx = NULL, *smaxpx = NULL, *smidpx = NULL;
bool highpow = 0;   /* allocate even p^{2^x-1} (based on roughness) */
ulong limp_cap = 0;
bool midp_only = 0, in_midp = 0, need_maxp = 0, need_midp = 0;
/* where to walk for -W (midp) */
typedef struct s_midpp {
    uint vi;
    uint x;
    ulong maxp;
    ulong minp;
} t_midpp;
uint midppc;
t_midpp *midpp = NULL;

struct {
    uint valid;
    ulong p;
    uint x;
    uint vi;
} midp_recover;
uint rough = 0;     /* test roughness if tau >= rough */
bool opt_print = 0; /* print candidates instead of fully testing them */
uint opt_flake = 0; /* test less before printing candidates */
/* If opt_alloc is non-zero and opt_batch < 0, just show the forced-prime
 * allocation; if opt_alloc is non-zero and opt_batch >= 0, just process
 * the specified batch_alloc.
 */
uint opt_alloc = 0;
int opt_batch_min = -1, opt_batch_max;
int batch_alloc = 0;    /* index of forced-prime allocations */
int last_batch_seen = -1;
uint cur_batch_level = 0;   /* for disp_batch, best_fixed */
bool seen_valid = 0;    /* if nothing seen, this case has no solutions */
/* by default, we call walk_v() as soon as we have 2 values fixed to
 * be squares rather than waiting for a full batch allocation; however
 * this can stop us noticing that there are no valid batches. Running
 * with '-jp' tells us to wait until we have a full batch before doing
 * a Pell walk.
 */
bool defer_pell = 0;
uint strategy;          /* best_v() strategy */
uint strategy_set = 0;  /* strategy was user-selected */
uint prev_strategy;     /* for special-case strategy override */
uint fixed_level = 0;   /* number of values specified for -js */
uint *fixed_v = NULL;   /* values specified for -js */

typedef uint (*t_strategy)(t_level *cur_level);
uint best_v0(t_level *cur_level);
uint best_v1(t_level *cur_level);
uint best_v2(t_level *cur_level);
uint best_v3(t_level *cur_level);
uint best_v4(t_level *cur_level);
/* best_6x() special-case strategy (TYPE_o only) */
uint best_6x(t_level *cur_level);
/* best_fixed() special-case strategy (-js) */
uint best_fixed(t_level *cur_level);
#define STRATEGY_6X 5
#define STRATEGY_FIXED 6
#define NUM_STRATEGIES 7
t_strategy strategies[NUM_STRATEGIES] = {
    &best_v0, &best_v1, &best_v2, &best_v3, &best_v4,
    &best_6x, &best_fixed
};

uint check = 0;         /* modulus to check up to */
uint check_prime = 0;   /* skip moduli divisible by prime greater than this */
double check_ratio = 1.0;  /* drop moduli that have too low rejection ratio */
uint check_chunk = 0;   /* combine moduli into chunks of this size */

bool debugw = 0;    /* diag and keep every case seen (excluding walk) */
bool debugW = 0;    /* diag and keep every case seen (including walk) */
uint debugw_count = 0;  /* debugw/W only for the first n iterations */
bool debugx = 0;    /* show p^x constraints */
bool debugb = 0;    /* show batch id, if changed */
bool debugB = 0;    /* show every batch id */
bool debugf = 0;    /* show prepped sub-batches */
bool debugt = 0;    /* show target_t() */
bool debugv = 0;    /* show modular constraints */
bool debugV = 0;    /* show more modular constraints */
bool debugm = 0;    /* track and show mintau results */
bool log_full = 0;  /* show prefinal result for harness */

ulong randseed = 1; /* for ECM, etc */
bool vt100 = 0;     /* update window title with VT100 escape sequences */

char *rpath = NULL; /* path to log file */
FILE *rfp = NULL;   /* file handle to log file */
bool start_seen = 0;    /* true if log file has been written to before */
bool skip_recover = 0;  /* true if we should not attempt recovery */
t_fact *rstack = NULL;  /* point reached in recovery log file */
t_fact *istack = NULL;  /* point requested by -I */
bool have_rwalk = 0;    /* true if recovery is mid-walk */
mpz_t rwalk_from;
mpz_t rwalk_to;

t_fact nf;      /* factors of n */
uint maxfact;   /* count of prime factors dividing n, with multiplicity */
uint maxodd;    /* as above for odd prime factors */
uint *maxforce = NULL;  /* max prime to force at v_i */
mpz_t px;       /* p^x */

/* If .valid, this mintau is .v as long as the index of the next available
 * prime is >= .from
 */
typedef struct s_mint_capped {
    mpz_t v;
    uint from;
    bool valid;
} t_mint_capped;
struct s_mint;
typedef struct s_mint {
    size_t capped_size;
    size_t branch_size;
    t_mint_capped *capped;
    struct s_mint **branch;
} t_mint;
typedef struct s_mint_state {
    uint *pfreev;       /* bit vector of available primes */
    ushort *pfreei;     /* list of free prime indices */
    ushort pfreenext;   /* where to start looking for next free prime */
    ushort pfreedepth;  /* number of free primes found */
} t_mint_state;
size_t pfree_vecsize;
t_mint **mint_base;
uint *restricted;
uint restricted_count;
t_mint ***mint_base_restricted;
t_mint_state mint_state;

#define DIAG 1
#define LOG 600
double diag_delay = DIAG, log_delay = LOG, death_delay = 0, diagt, logt;
ulong countr, countw, countwi;
#define MAX_DEC_ULONG 20
#define MAX_DEC_POWER 5
#define DIAG_BUFSIZE (6 + MAX_DEC_ULONG + k * maxfact * (MAX_DEC_ULONG + 1 + MAX_DEC_POWER + 1) + 1)
char *diag_buf = NULL;
uint aux_buf_size = 0;
char *aux_buf = NULL;

/* Initial pattern set with -I */
char *init_pattern = NULL;

/* Default cvec context */
t_context *cx0 = NULL;

/* Mod constraints set with -m */
typedef struct s_modfix {
    mpz_t mod;
    mpz_t val;
    bool negate;
} t_modfix;
t_modfix *modfix = NULL;
uint modfix_count = 0;
/* have_modfix = 1 means that a global modular constraint on v_0 has been
 * stored in levels[0].rq/aq.
 */
bool have_modfix = 0;

typedef struct s_sizedstr {
    char *s;
    size_t size;
} t_sizedstr;

uint tm_count = 0;
static inline void test_multi_reset(void) {
    tm_count = 0;
}
/* Note: test_multi_append() steals the input mpz_t */
static inline bool test_multi_append(mpz_t n, uint vi, uint t, uint e) {
    uint i = tm_count++;
    t_tm *tm = &taum[i];
    mpz_swap(tm->n, n);
    tm->vi = vi;
    tm->t = t;
    tm->e = e;
    return tau_multi_prep(i);
}
/* Note: test_prime_append() steals the input mpz_t */
static inline bool test_prime_append(mpz_t n, uint vi) {
    uint i = tm_count++;
    t_tm *tm = &taum[i];
    mpz_swap(tm->n, n);
    tm->vi = vi;
    tm->t = 2;
    tm->e = 1;
    return tau_prime_prep(i);
}
static inline uint test_prime_run(void) {
    return tau_prime_run(tm_count);
}
static inline uint test_multi_run(tau_failure_handler tfh) {
    return tau_multi_run(tm_count, tfh);
}

#if defined(TYPE_o) || defined(TYPE_r)
    static inline uint TYPE_OFFSET(uint i) {
        return i;
    }
#elif defined(TYPE_a)
    static inline uint TYPE_OFFSET(uint i) {
        return i * n;
    }
#else
#   error "No type defined"
#endif

static inline char typename(void) {
#if defined(TYPE_o)
    return 'o';
#elif defined(TYPE_a)
    return 'a';
#elif defined(TYPE_r)
    return 'r';
#endif
}

uint know_target(uint vi) {
#if defined(TYPE_r)
    t_fact f;
    init_fact(&f);
    simple_fact(n + vi, &f);
    uint t = simple_tau(&f);
    free_fact(&f);
    return t;
#else
    return n;
#endif
}

#ifdef TRACK_STATS
    ulong* count_bad;
    static inline void TRACK_GOOD(uint vk, uint vi) { }
    static inline void TRACK_BAD(uint vk, uint vi) {
        ++count_bad[vk];
    }
    static inline void TRACK_MULTI(uint count, uint* need, t_tm *tm) {
        ++count_bad[k - count];
    }
    void init_stats(uint k) {
        count_bad = calloc(k + 1, sizeof(ulong));
    }
    void done_stats(void) {
        free(count_bad);
    }
#else
    static inline void TRACK_GOOD(uint vk, uint vi) { }
    static inline void TRACK_BAD(uint vk, uint vi) { }
    static inline void TRACK_MULTI(uint count, uint* need, t_tm *tm) { }
    void init_stats(uint k) { }
    void done_stats(void) { }
#endif

void update_window(t_level *cur_level) {
    if (vt100) {
        /* update window title and icon with <ESC> ] 0 ; "string" <BEL> */
        uint this_batch = (opt_batch_min < 0) ? batch_alloc : batch_alloc - 1;
        printf("\x1b]0;b%d:", this_batch);
        uint pc = 0;
        for (uint i = 1; i <= cur_level->level && pc < 3; ++i) {
            if (levels[i].is_forced)
                continue;
            printf(" %lu", levels[i].p);
            ++pc;
        }
        printf("\a");
    }
    fflush(stdout);
}

void prep_show_v(t_level *cur_level) {
    uint offset = 0;
    uint mid_vi;
    if (in_midp)
        mid_vi = cur_level->vi;
    offset += (batch_alloc)
        ? sprintf(&diag_buf[offset], "b%u: ", batch_alloc - 1)
        : sprintf(&diag_buf[offset], "b*: ");
    for (uint vi = 0; vi < k; ++vi) {
        uint vlevel = cur_level->vlevel[vi]
                - ((in_midp && vi == mid_vi) ? 1 : 0);
        if (vi)
            diag_buf[offset++] = ' ';
        if (vlevel == 1)
            diag_buf[offset++] = '.';
        else {
            t_value *vp = &value[vi];
            for (uint ai = 1; ai < vlevel; ++ai) {
                t_allocation *ap = &vp->alloc[ai];
                if (ai > 1)
                    diag_buf[offset++] = '.';
                offset += sprintf(&diag_buf[offset], "%lu", ap->p);
                if (ap->x > 2)
                    offset += sprintf(&diag_buf[offset], "^%u", ap->x - 1);
            }
        }
    }
    if (in_midp) {
        ulong p = cur_level->p;
        uint x = cur_level->x;
        offset += sprintf(&diag_buf[offset], " W(%lu,%u,%u)", p, x, mid_vi);
    }
    diag_buf[offset] = 0;
}

void diag_csv_head(void) {
    printf("Batch id");
    for (uint i = 0; i < k; ++i)
        printf(",v_%u", i);
    t_divisors *dp = &divisors[n];
    printf(",LCM");
    for (uint i = 0; i < dp->alldiv; ++i)
        printf(",t %u", dp->div[i]);
    printf("\n");
}

void diag_csv(t_level *cur_level) {
    t_divisors *dp = &divisors[n];
    uint tc[dp->alldiv];
    memset(&tc[0], 0, dp->alldiv * sizeof(uint));
    mpz_set_ui(Z(temp), 1);
    printf("%u", batch_alloc);
    for (uint vi = 0; vi < k; ++vi) {
        t_value *vp = &value[vi];
        uint vlevel = cur_level->vlevel[vi];
        printf(",");
        for (uint ai = 1; ai < vlevel; ++ai) {
            t_allocation *ap = &vp->alloc[ai];
            if (ai > 1)
                printf(".");
            printf("%lu", ap->p);
            if (ap->x > 2)
                printf("^%u", ap->x - 1);
        }
        if (vlevel <= 1)
            printf("1");
        t_allocation *ap = &vp->alloc[vlevel - 1];
        mpz_lcm(Z(temp), Z(temp), ap->q);
        uint t = ap->t;
        for (uint di = 0; di < dp->alldiv; ++di)
            if (t == dp->div[di]) {
                ++tc[di];
                break;
            }
    }
    gmp_printf(",%Zu", Z(temp));
    for (uint di = 0; di < dp->alldiv; ++di)
        printf(",%u", tc[di]);
    printf("\n");
}

void report(char *format, ...) {
    keep_diag();
    va_list ap;
    va_start(ap, format);
    gmp_vfprintf(stdout, format, ap);
    va_end(ap);

    if (rfp) {
        va_start(ap, format);
        gmp_vfprintf(rfp, format, ap);
        va_end(ap);
        fflush(rfp);
    }
}

double seconds(double t1) {
    return (t1 - t0);
}

double elapsed(void) {
    return seconds(utime());
}

uint _sizeinbase(uint n, uint base) {
    uint size = 1;
    while (n >= base) {
        ++size;
        n /= base;
    }
    return size;
}

uint write_fact(t_sizedstr *bufp, mpz_t v, uint target) {
    factor_state fs;
    uint t = 1;

    if (mpz_cmp_ui(v, 1) == 0) {
        bufp->s = realloc(bufp->s, 2);
        bufp->size = sprintf(bufp->s, "1");
        return t;
    }

    fs_init(&fs);
    mpz_set(fs.n, v);
    while (1) {
        if (!factor_one(&fs))
            break;
        t *= fs.e + 1;
        uint next = bufp->size ? 1 : 0;
        uint size = bufp->size + next + 1;
        size += mpz_sizeinbase(fs.f, 10);
        if (fs.e > 1)
            size += 1 + _sizeinbase(fs.e, 10);
        bufp->s = realloc(bufp->s, size);
        bufp->size += gmp_sprintf(&bufp->s[bufp->size], "%s%Zu",
                (next ? "." : ""), fs.f);
        if (fs.e > 1)
            bufp->size += sprintf(&bufp->s[bufp->size], "^%u", fs.e);
    }
    fs_clear(&fs);
    return t;
}

bool report_211(uint vi, t_sizedstr *bufp) {
    /* 211 Sequence  0:  4 = tau(1248619267217398415 = 5.249723853443479683) */
    mpz_add_ui(Z(temp), best, vi);
    uint target = know_target(vi);
    uint t = write_fact(bufp, Z(temp), target);
    report("211 Sequence %d: %d = tau(%Zu = %s)\n",
            vi, t, Z(temp), bufp->s);
    bufp->size = 0;
    return t == target;
}

void report_prefinal(double tz) {
    if (!seen_best) {
        /* 500 f(241, 9) > 56346707724292074686037507 (655.570s) */
        report("500 f(%d, %d) > %Zd (%.3fs)\n",
                n, k, zmax, seconds(tz));
        return;
    }
    t_sizedstr buf = { NULL, 0 };
    bool good = 1;
    for (uint i = 0; i <= k || good; ++i)
        if (!report_211(i, &buf))
            good = 0;
    free(buf.s);
}

/* gmp_sprintf into aux_buf, resizing as needed */
void aux_sprintf(char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    uint size = gmp_vsnprintf(aux_buf, aux_buf_size, fmt, ap);
    va_end(ap);
    if (size >= aux_buf_size) {
        size += 32;
        aux_buf = realloc(aux_buf, size);
        aux_buf_size = size;
        va_start(ap, fmt);
        gmp_vsprintf(aux_buf, fmt, ap);
        va_end(ap);
    }
}

void disp_batch(void) {
    assert(level >= cur_batch_level);

    t_level *lp = &levels[cur_batch_level];
    if (opt_alloc & 2) {
        diag_csv(lp);
    } else {
        prep_show_v(lp);        /* into diag_buf */
        if (lp->have_square) {
            uint l = strlen(diag_buf);
            sprintf(&diag_buf[l], " [sq=%u]", lp->have_square);
        }
        report("203 %s\n", diag_buf);
    }
}

void diag_any(t_level *cur_level, bool need_disp) {
    double t1 = utime();
    update_window(cur_level);

    if ((debugb && !debugB)
        && batch_alloc != last_batch_seen
        && ((need_diag && need_disp) || (rfp && need_log))
    ) {
        last_batch_seen = batch_alloc;
        disp_batch();
    }

    prep_show_v(cur_level);     /* into diag_buf */
    if (need_diag) {
        if (need_disp)
            diag("%s%s", diag_buf, aux_buf);
        if (debugw) {
            keep_diag();
            if (debugw_count) {
                --debugw_count;
                if (debugw_count == 0) {
                    debugw = 0;
                    debugW = 0;
                    need_diag = 0;
                }
            }
        } else
            need_diag = 0;
        if (death_delay)
            if (seconds(t1 - t0) >= death_delay) {
                keep_diag();
                report("301 Timeout after %.2fs\n", seconds(t1));
                fail_silent();
            }
    }

    if (rfp && need_log) {
#ifdef TRACK_STATS
        fprintf(rfp, "305 %s%s (%.2fs) [", diag_buf, aux_buf, seconds(t1));
        for (uint i = 0; i < k; ++i) {
            if (i)
                fprintf(rfp, " ");
            fprintf(rfp, "%lu", count_bad[i]);
        }
        fprintf(rfp, "]\n");
#else
        fprintf(rfp, "305 %s%s (%.2fs)\n", diag_buf, aux_buf, seconds(t1));
#endif
        logt = t1 + log_delay;
        need_log = 0;
    }
    if (!debugw)
        need_work = 0;
}

void diag_plain(t_level *cur_level) {
    aux_sprintf("");
    diag_any(cur_level, 1);
}

void diag_walk_v(t_level *cur_level, ulong ati, ulong end) {
    aux_sprintf(": %lu / %lu", ati, end);
    diag_any(cur_level, !(debugw && !debugW && ati));
}

void diag_walk_zv(t_level *cur_level, mpz_t ati, mpz_t end) {
    aux_sprintf(": %Zu / %Zu", ati, end);
    diag_any(cur_level, !(debugw && !debugW && mpz_sgn(ati)));
}

void diag_walk_pell(t_level *cur_level, uint pc) {
    aux_sprintf(": P%u", pc);
    diag_any(cur_level, !(debugw && !debugW && pc));
}

/* Record a found candidate; returns FALSE if we should continue testing
 * larger candidates with the current set of allocations.
 */
bool candidate(mpz_t c) {
#if defined(TYPE_r)
    if (mpz_fits_ulong_p(c) && mpz_get_ui(c) == n)
        return 0;
#endif
    keep_diag();
    double t1 = utime();
    report("202 Candidate %Zu (%.2fs)\n", c, seconds(t1));
    if (!seen_best || mpz_cmp(c, best) <= 0) {
        mpz_set(best, c);
        ++seen_best;
    }
    if (improve_max && mpz_cmp(c, zmax) <= 0)
        mpz_set(zmax, c);
    return improve_max;
}

void free_levels(void) {
    for (uint i = 0; i < maxlevel; ++i) {
        t_level *l = &levels[i];
        free(l->vlevel);
        free(l->pfreev);
        mpz_clear(l->aq);
        mpz_clear(l->rq);
        prime_iterator_destroy(&l->piter);
    }
    free(levels);
}

void init_levels(void) {
    levels = calloc(maxlevel + 1, sizeof(t_level));
    for (uint i = 0; i < maxlevel; ++i) {
        t_level *l = &levels[i];
        l->level = i;
        l->vlevel = calloc(k, sizeof(uint));
        l->pfreev = malloc(pfree_vecsize * sizeof(uint));
        mpz_init(l->aq);
        mpz_init(l->rq);
#if 0
        /* not needed, prime_iterator_setprime() later will initialize */
        prime_iterator_init(&l->piter);
#endif
    }
    mpz_set_ui(levels[0].aq, 1);
    mpz_set_ui(levels[0].rq, 0);
    levels[0].have_square = 0;
    levels[0].have_min = (sminp || sminpx) ? 0 : 1;
    levels[0].next_best = 0;
    levels[0].nextpi = 0;
    levels[0].maxp = 0;
    levels[0].is_forced = 2;    /* special value for dummy entry */
    if (forcedp + 1 > 8 * sizeof(levels[0].fp_need))
        fail("FIXME: too many forced primes");
    levels[0].fp_need = (1 << forcedp) - 1;
    memset(levels[0].pfreev, 0xff, pfree_vecsize * sizeof(uint));
    for (uint j = 0; j < k; ++j)
        levels[0].vlevel[j] = 1;
    level = 1;
}

void free_value(void) {
    for (int i = 0; i < k; ++i) {
        t_value *v = &value[i];
        for (int j = 0; j <= maxfact; ++j) {
            mpz_clear(v->alloc[j].q);
            mpz_clear(v->alloc[j].lim);
        }
        free(v->alloc);
    }
    free(value);
}

void init_value(void) {
    value = malloc(k * sizeof(t_value));
    for (int i = 0; i < k; ++i) {
        t_value *v = &value[i];
        v->alloc = malloc((maxfact + 1) * sizeof(t_allocation));
        for (uint j = 0; j <= maxfact; ++j) {
            mpz_init(v->alloc[j].q);
            mpz_init(v->alloc[j].lim);
        }
        t_allocation *ap = &v->alloc[0];
        ap->p = 0;
        ap->x = 0;
        ap->t = target_t(i);
        mpz_set_ui(ap->q, 1);
    }
}

t_mint *new_mint(void) {
    t_mint *mp = calloc(1, sizeof(t_mint));
    return mp;
}

/* TODO: optimize resizing strategy */
static inline void resize_branch(t_mint *base, uint need) {
    size_t size = need + 1;
    base->branch = realloc(base->branch, size * sizeof(t_mint *));
    for (uint i = base->branch_size; i < size; ++i)
        base->branch[i] = NULL;
    base->branch_size = size;
}
static inline void resize_capped(t_mint *base, uint need) {
    size_t size = need + 1;
    base->capped = realloc(base->capped, size * sizeof(t_mint_capped));
    for (uint i = base->capped_size; i < size; ++i)
        base->capped[i].valid = 0;
    base->capped_size = size;
}

t_mint *mint_branch(t_mint *base, uint pdiff, bool create) {
    t_mint *branch;
    if (base->branch_size <= pdiff) {
        if (!create)
            return (t_mint *)NULL;
        resize_branch(base, pdiff);
    }
    branch = base->branch[pdiff];
    if (branch == NULL) {
        if (!create)
            return (t_mint *)NULL;
        branch = new_mint();
        base->branch[pdiff] = branch;
    }
    return branch;
}

t_mint_capped *mint_capped(t_mint *base, uint pdiff, bool create) {
    t_mint_capped *capped;
    if (base->capped_size <= pdiff) {
        if (!create)
            return (t_mint_capped *)NULL;
        resize_capped(base, pdiff);
    }
    return &base->capped[pdiff];
}

void mint_init_base(t_mint ***p) {
    uint maxtau = n / divisors[n].high;
    t_divisors *dp = &divisors[maxtau];
    *p = calloc(maxtau + 1, sizeof(t_mint *));
    for (uint di = 0; di < dp->alldiv; ++di) {
        uint f = dp->div[di];
        if (f == 1)
            continue;
        (*p)[f] = new_mint();
    }
}

void prep_mintau(void) {
    mint_init_base(&mint_base);

    restricted_count = 0;
    restricted = NULL;
    t_divisors *dp = &divisors[n];
    for (uint di = 0; di < dp->alldiv; ++di) {
        uint d = dp->div[di];
        uint h = divisors[d].high;
        if (h <= 2)
            break;
        if ((n / d) % h)
            continue;
        restricted = realloc(restricted, (restricted_count + 1) * sizeof(uint));
        restricted[restricted_count++] = d;
    }
    if (restricted_count) {
        mint_base_restricted = malloc(restricted_count * sizeof(t_mint **));
        for (uint i = 0; i < restricted_count; ++i)
            mint_init_base(&mint_base_restricted[i]);
    }

    uint maxtau = n / divisors[n].high;
    dp = &divisors[maxtau];
    ushort maxdepth = dp->sumpm;
    pfree_vecsize = (nsprimes + 31) >> 5;
    t_mint_state *s = &mint_state;
    s->pfreei = calloc(maxdepth, sizeof(ushort));

    mint_best = malloc(maxdepth * sizeof(mpz_t));
    mint_px = malloc(maxdepth * sizeof(mpz_t));
    for (uint i = 0; i < maxdepth; ++i) {
        mpz_init(mint_best[i]);
        mpz_init(mint_px[i]);
    }
}

void free_mint(t_mint *mtp) {
    for (uint i = 0; i < mtp->capped_size; ++i) {
        t_mint_capped *capped = &mtp->capped[i];
        if (capped->valid)
            mpz_clear(capped->v);
    }
    free(mtp->capped);
    for (uint i = 0; i < mtp->branch_size; ++i) {
        t_mint *branch = mtp->branch[i];
        if (branch)
            free_mint(branch);
    }
    free(mtp->branch);
    free(mtp);
}

void mint_free_base(t_mint ***p) {
    uint maxtau = n / divisors[n].high;
    t_divisors *dp = &divisors[maxtau];
    for (uint di = 0; di < dp->alldiv; ++di) {
        uint f = dp->div[di];
        if (f == 1)
            continue;
        t_mint *mtp = (*p)[f];
        if (mtp)
            free_mint(mtp);
    }
    free(*p);
}

void done_mintau(void) {
    t_mint_state *s = &mint_state;
    free(s->pfreei);

    mint_free_base(&mint_base);
    if (restricted_count) {
        free(restricted);
        for (uint i = 0; i < restricted_count; ++i)
            mint_free_base(&mint_base_restricted[i]);
        free(mint_base_restricted);
    }

    uint maxtau = n / divisors[n].high;
    t_divisors *dp = &divisors[maxtau];
    ushort maxdepth = dp->sumpm;
    for (uint i = 0; i < maxdepth; ++i) {
        mpz_clear(mint_best[i]);
        mpz_clear(mint_px[i]);
    }
    free(mint_best);
    free(mint_px);
}

void track_mintau(mpz_t mint, uint t, uint depth0) {
    t_mint_state *s = &mint_state;
    gmp_fprintf(stderr, "mintau(%u) = %Zu [", t, mint);
    for (uint i = depth0; i < s->pfreedepth; ++i) {
        if (i > depth0)
            gmp_fprintf(stderr, " ");
        gmp_fprintf(stderr, "%u", sprimes[s->pfreei[i]]);
    }
    gmp_fprintf(stderr, "]\n");
}

void done(void) {
    /* update window title on completion */
    if (vt100)
        printf("\x1b]2;b%d: done\a",
                opt_batch_min < 0 ? batch_alloc : opt_batch_max);

    if (check)
        cvec_done(cx0);
    free(diag_buf);
    free(aux_buf);
    if (wv_qq)
        for (uint i = 0; i < k; ++i)
            mpz_clear(wv_qq[i]);
    free(wv_qq);
    if (wv_o)
        for (uint i = 0; i < k; ++i)
            mpz_clear(wv_o[i]);
    free(wv_o);
    free(minp);
    free(maxp);
    free(midp);
    free(midpp);
    free(sqg);
    free(fixed_v);
    free_value();
    free_levels();
    free(sprimes);
    free(ptoi);
    if (forcep)
        for (int i = 0; i < forcedp; ++i)
            free(forcep[i].batch);
    free(forcep);
    free(maxforce);
    done_mintau();
    if (divisors)
        for (int i = 0; i <= target_lcm; ++i)
            free(divisors[i].div);
    free(divisors);
#if defined(TYPE_r)
    free(target_tau);
#endif
    if (have_rwalk) {
        mpz_clear(rwalk_from);
        mpz_clear(rwalk_to);
    }
    if (rstack) {
        for (int i = 0; i < k; ++i)
            free_fact(&rstack[i]);
        free(rstack);
    }
    if (istack) {
        for (int i = 0; i < k; ++i)
            free_fact(&istack[i]);
        free(istack);
    }
    if (rfp)
        fclose(rfp);
    free(rpath);
    for (t_zstash i = 0; i < MAX_ZSTASH; ++i)
        mpz_clear(Z(i));
    free(zstash);
    mpz_clear(px);
    free_fact(&nf);
    mpz_clear(zmax);
    mpz_clear(zmin);
    mpz_clear(best);
    done_pell();
    done_rootmod();
    done_stats();
    done_tau();
    _GMP_destroy();
}

void fail_silent(void) {
    /* we accept leaks on fatal error, but should close the log file */
    if (rfp)
        fclose(rfp);
    exit(0);
}
void fail(char *format, ...) {
    va_list ap;
    va_start(ap, format);
    gmp_vprintf(format, ap);
    printf("\n");
    va_end(ap);
    /* we accept leaks on fatal error, but should close the log file */
    if (rfp)
        fclose(rfp);
    exit(1);
}

void handle_sig(int sig) {
    need_work = 1;
    if (sig == SIGUSR1)
        need_diag = 1;
    else
        need_log = 1;
}

void init_time(void) {
    struct sigaction sa;
    struct sigevent sev;
    struct itimerspec diag_timer, log_timer;

    sa.sa_handler = &handle_sig;
    sa.sa_flags = SA_RESTART;
    sigemptyset(&sa.sa_mask);

    if (diag_delay) {
        if (sigaction(SIGUSR1, &sa, NULL))
            fail("Could not set USR1 handler: %s\n", strerror(errno));
        sev.sigev_notify = SIGEV_SIGNAL;
        sev.sigev_signo = SIGUSR1;
        sev.sigev_value.sival_ptr = &diag_timerid;
        if (timer_create(CLOCK_PROCESS_CPUTIME_ID, &sev, &diag_timerid)) {
            /* guess that the CPUTIME clock is not supported */
            if (timer_create(CLOCK_REALTIME, &sev, &diag_timerid))
                fail("Could not create diag timer: %s\n", strerror(errno));
            clock_is_realtime = 1;
        }
        diag_timer.it_value.tv_sec = diag_delay;
        diag_timer.it_value.tv_nsec = 0;
        diag_timer.it_interval.tv_sec = diag_delay;
        diag_timer.it_interval.tv_nsec = 0;
        if (timer_settime(diag_timerid, 0, &diag_timer, NULL))
            fail("Could not set diag timer: %s\n", strerror(errno));
    }

    if (log_delay) {
        if (sigaction(SIGUSR2, &sa, NULL))
            fail("Could not set USR2 handler: %s\n", strerror(errno));
        sev.sigev_notify = SIGEV_SIGNAL;
        sev.sigev_signo = SIGUSR2;
        sev.sigev_value.sival_ptr = &log_timerid;
        if (timer_create(CLOCK_PROCESS_CPUTIME_ID, &sev, &log_timerid)) {
            /* guess that the CPUTIME clock is not supported */
            if (timer_create(CLOCK_REALTIME, &sev, &log_timerid))
                fail("Could not create log timer: %s\n", strerror(errno));
            clock_is_realtime = 1;
        }
        log_timer.it_value.tv_sec = log_delay;
        log_timer.it_value.tv_nsec = 0;
        log_timer.it_interval.tv_sec = log_delay;
        log_timer.it_interval.tv_nsec = 0;
        if (timer_settime(log_timerid, 0, &log_timer, NULL))
            fail("Could not set log timer: %s\n", strerror(errno));
    }
}

void init_pre(void) {
    _GMP_init();
    /* reseed immediately to retain reproducibility */
    clear_randstate();
    init_randstate(1);
    /* we may do this again after options handled, to select real seed */

    init_pell();
    t0 = utime();
    mpz_init_set_ui(zmin, 0);
    mpz_init_set_ui(zmax, 0);
    init_fact(&nf);
    mpz_init(px);
    zstash = malloc(MAX_ZSTASH * sizeof(mpz_t));
    for (t_zstash i = 0; i < MAX_ZSTASH; ++i)
        mpz_init(Z(i));
    mpz_set_ui(Z(zero), 0);
    mpz_set_ui(Z(zone), 1);
    mpz_init(best);
    midp_recover.valid = 0;
}

/* Parse a "305" log line for initialization.
 * Input string should point after the initial "305 ".
 */
void parse_305(char *s, t_fact **stackp) {
    double dtime;
    t_ppow pp;
    bool is_W = 0;

    t_fact *stack = malloc(k * sizeof(t_fact));
    *stackp = stack;
    for (int i = 0; i < k; ++i)
        init_fact(&stack[i]);

    if (s[0] == 'b') {
        int off = 0;
        sscanf(s, "b%u: %n", &batch_alloc, &off);
        if (off == 0) {
            batch_alloc = -1;
            sscanf(s, "b*: %n", &off);
            if (off == 0)
                fail("501 error parsing 305 line '%s'", s);
        }
        s += off;
        ++batch_alloc;  /* we always point to the next batch */
    }
        
    for (int i = 0; i < k; ++i) {
        if (i) {
            if (s[0] != ' ') {
                if (s[0] == 0)
                    fail("502 Unexpected end of init or recovery pattern");
                fail("503 Unexpected character in init or recovery pattern");
            }
            ++s;
        }
        if (s[0] == '.') {
            ++s;
            continue;
        }
        while (1) {
            pp.p = strtoul(s, &s, 10);
            pp.e = (s[0] == '^') ? strtoul(&s[1], &s, 10) : 1;
            if (pp.p == 1 || pp.e == 0)
                continue;
            add_fact(&stack[i], pp);
            if (s[0] != '.')
                break;
            ++s;
        }
        /* reverse them, so we can pop as we allocate */
        reverse_fact(&stack[i]);
    }
    if (strncmp(s, " W(", 3) == 0) {
        s += 3;
        is_W = 1;
        midp_recover.p = strtoul(s, &s, 10);
        assert(s[0] == ',');
        ++s;
        midp_recover.x = strtoul(s, &s, 10);
        if (s[0] == ')') {
#if 1
            /* new version uses different order, cannot reliably recover */
            fail("504 cannot recover from old-style 'W(...)' entry");
#else
            /* old version had x fixed to 3 */
            midp_recover.vi = midp_recover.x;
            midp_recover.x = 3;
#endif
        } else {
            if (s[0] != ',')
                fail("505 unexpected character in W(...) recovery");
            ++s;
            midp_recover.vi = strtoul(s, &s, 10);
        }
        if (s[0] != ')')
            fail("505 unexpected character in W(...) recovery");
        ++s;
        midp_recover.valid = 1;
    }
    if (s[0] == ':') {
        if (s[1] != ' ')
            fail("506 unexpected character at end of recvoery pattern");
        s += 2;
        if (strncmp("t=1", s, 3) == 0)
            s += 3; /* ignore */
        else if (s[0] == 'P') {
            /* "P\d+" is a Pell walk, ignore for now */
            ++s;
            while (isdigit(*s))
                ++s;
        } else {
            int from_start, from_end, to_start, to_end = 0;
            have_rwalk = 1;
            sscanf(s, "%n%*[0-9]%n / %n%*[0-9]%n ",
                    &from_start, &from_end, &to_start, &to_end);
            if (to_end == 0)
                fail("507 could not parse 305 from/to: '%s'", s);
            s[from_end] = 0;
            mpz_init_set_str(rwalk_from, &s[from_start], 10);
            s[to_end] = 0;
            mpz_init_set_str(rwalk_to, &s[to_start], 10);
            have_rwalk = 1;
            s[to_end] = ' ';
            s = &s[to_end];
        }
    }
    while (s[0] == ' ')
        ++s;
    if (s[0] == '(') {
        int off = 0;
        sscanf(s, "(%lfs)%n", &dtime, &off);
        if (off == 0)
            fail("508 could not parse recovery time: '%s'", s);
        s += off;
    } else
        dtime = 0;
    while (s[0] == ' ')
        ++s;
#ifdef TRACK_STATS
    if (s[0] == '[') {
        ++s;
        for (uint i = 0; i < k; ++i) {
            if (i) {
                if (s[0] != ' ')
                    fail("509 could not parse recovery stats: '%s'", s);
                ++s;
            }
            int off = 0;
            sscanf(s, "%lu%n", &count_bad[i], &off);
            if (off == 0)
                fail("509 could not parse recovery stats: '%s'", s);
            s += off;
        }
        if (s[0] != ']')
            fail("509 could not parse recovery stats: '%s'", s);
        ++s;
    }
#endif
    while (s[0] == ' ')
        ++s;
    if (s[0] != 0 && s[0] != '\n' && s[0] != '\r')
        fail("511 unexpected text at end of init/recovery pattern: %s", s);
    if (is_W && !need_midp)
        fail("512 recovery expected -W option");
    t0 -= dtime;
}

void recover(FILE *fp) {
    char *last305 = NULL;
    char *curbuf = NULL;
    size_t len = 120, len305 = 0, len202 = 0;

    while (1) {
        ssize_t nread = getline(&curbuf, &len, fp);
        if (nread <= 0) {
            if (errno == 0)
                break;
            fail("error reading %s: %s", rpath, strerror(errno));
        }
        if (curbuf[nread - 1] != '\n'
                || memchr(curbuf, 0, nread) != NULL) {
            /* corrupt line, file should be truncated */
            off_t offset = ftello(fp);
            if (offset == -1)
                fail("could not ask offset: %s", strerror(errno));
            /* not ftruncate(), we are open only for reading */
            if (truncate(rpath, offset - nread) != 0)
                fail("could not truncate %s to %lu: %s", rpath, offset - nread,
                        strerror(errno));
            break;
        }
        if (strncmp("305 ", curbuf, 4) == 0) {
            char *t = last305;
            last305 = curbuf;
            curbuf = t;
            size_t lt = len305;
            len305 = len;
            len = lt;
        } else if (strncmp("202 ", curbuf, 4) == 0) {
            int start, end, off = 0;
            mpz_t cand;
            sscanf(curbuf, "202 Candidate %n%*[0-9]%n (%*[0-9.]s)%n",
                    &start, &end, &off);
            if (off == 0)
                fail("error parsing 202 line '%s'", curbuf);
            curbuf[end] = 0;
            mpz_init_set_str(cand, &curbuf[start], 10);
            if (!seen_best || mpz_cmp(best, cand) >= 0)
                mpz_set(best, cand);
            seen_best = 1;
            mpz_clear(cand);
        } else if (strncmp("001 ", curbuf, 4) == 0) {
            /* TODO: parse and check for consistent options */
            start_seen = 1;
        } else if (strncmp("000 ", curbuf, 4) == 0)
            ;   /* comment */
        else if (strncmp("203 ", curbuf, 4) == 0)
            ;   /* batch number */
        else
            fail("unexpected log line %.3s in %s", curbuf, rpath);
    }
    if (improve_max && seen_best && mpz_cmp(best, zmax) < 0)
        mpz_set(zmax, best);
    if (last305)
        parse_305(last305 + 4, &rstack);
    free(curbuf);
    free(last305);
}

int cmp_high(const void *va, const void *vb) {
    uint a = *(uint *)va, b = *(uint *)vb;
    return (int)divisors[b].high - (int)divisors[a].high;
}

/* Note this is used only for prep_primes(), not at runtime */
ulong next_prime(ulong cur) {
    mpz_set_ui(Z(np_p), cur);
    _GMP_next_prime(Z(np_p));
    if (mpz_fits_ulong_p(Z(np_p)))
        return mpz_get_ui(Z(np_p));
    fail("next_prime overflow\n");
}

/* prep target_tau[], target_lcm, maxfact, maxodd */
void prep_target(void) {
    t_fact f;
    init_fact(&f);

#if defined(TYPE_r)
    target_tau = malloc(k * sizeof(uint));
    target_lcm = 1;
#endif
    maxfact = 0;
    maxodd = 0;
    for (uint i = 0; i < k; ++i) {
        uint t = know_target(i);
#if defined(TYPE_r)
        target_tau[i] = t;
        ulong g = simple_gcd(target_lcm, t);
        target_lcm *= t / g;
#endif

        uint thisfact = 0;
        uint thisodd = 0;
        f.count = 0;
        simple_fact(t, &f);
        for (int i = 0; i < f.count; ++i)
            thisfact += f.ppow[i].e;
        thisodd = thisfact;
        if (f.ppow[0].p == 2)
            thisodd -= f.ppow[0].e;
        if (maxfact < thisfact)
            maxfact = thisfact;
        if (maxodd < thisodd)
            maxodd = thisodd;
    }
    free_fact(&f);
    if (target_lcm > DIVISOR_WARN_LIMIT) {
        fprintf(stderr, "Warning, target LCM %lu > warn limit %lu\n",
                (ulong)target_lcm, (ulong)DIVISOR_WARN_LIMIT);
    }
}

/* recurse() wants the list of powers to try: each divisor of t_i (which
 * itself divides n) that is divisible by the highest odd prime factor
 * dividing t_i, in increasing order.
 * prep_forcep() wants the full list of divisors, but in similar order.
 * For each power, recurse() also wants to know which powers to skip
 * if the previous power was a given value, but that's simply:
 * skip x' if x' < x and high(x') == high(x).
 * mintau() wants sumpm, sum{p_j - 1} of the primes dividing t_i with
 * multiplicity.
 * When a square is fixed, walk_v() wants gcddm, the gcd{d_j-1} of all
 * divisors d_j of t_i.
 */
void prep_fact(void) {
    t_fact f;

    divisors = calloc(target_lcm + 1, sizeof(t_divisors));
    init_fact(&f);
    for (uint i = 1; i <= target_lcm; ++i) {
        if (target_lcm % i)
            continue;
        t_divisors *dp = &divisors[i];
        f.count = 0;
        simple_fact(i, &f);
        uint td = simple_tau(&f);
        dp->high = (f.count) ? f.ppow[f.count - 1].p : 1;
        dp->sumpm = dp->high - 1;
        dp->sumpm += divisors[i / dp->high].sumpm;
        uint nd = 0;
        dp->div = malloc(td * sizeof(uint));
        for (uint j = 1; j <= i; ++j) {
            if (i % j)
                continue;
            dp->div[dp->alldiv++] = j;
            if (dp->high > 1 && (j % dp->high) == 0)
                ++dp->highdiv;
        }
        qsort(dp->div, dp->alldiv, sizeof(uint), &cmp_high);

        uint g = dp->div[0] - 1;
        for (uint di = 1; di < dp->alldiv; ++di)
            g = tiny_gcd(g, dp->div[di] - 1);
        dp->gcddm = g;
    }
    free_fact(&f);
}

void prep_maxforce(void) {
    maxforce = malloc(k * sizeof(uint));
#if defined(TYPE_o)
    if ((n & 3) != 0) {
        for (int i = 0; i < k; ++i)
            maxforce[i] = k;
    } else
#endif
        for (int i = 0; i < k; ++i) {
            int mf = k - i - 1;
            if (i > mf)
                mf = i;
            if (force_all > mf)
                mf = force_all;
            maxforce[i] = mf;
        }
}

void prep_primes(void) {
    /* We can certainly not allocate more than (each of the forced primes)
     * plus (one per odd prime factor for each v_i); in practice it will
     * usually be less.
     * In mintau() we may need maxfact primes beyond what may have been
     * allocated in k-1 places. */
    nsprimes = (highpow ? maxfact : maxodd) * k + forcedp + (maxfact - maxodd);
    sprimes = malloc(nsprimes * sizeof(uint));
    if (debugm)
        fprintf(stderr, "nsprimes %u\n", nsprimes);
    uint p = 1;
    for (uint i = 0; i < nsprimes; ++i) {
        p = next_prime(p);
        sprimes[i] = p;
    }
    lastprime = p;
    ptoi = calloc(lastprime + 1, sizeof(uint));
    for (uint i = 0; i < nsprimes; ++i)
        ptoi[sprimes[i]] = i;
}

uint mpz_valuation(mpz_t z, uint n) {
    uint x = 0;
    if (mpz_sgn(z) == 0)
        fail("Cannot take valuation of (0_z, %u)", n);
    mpz_set(Z(temp), z);
    while (1) {
        uint off = mpz_fdiv_q_ui(Z(temp), Z(temp), n);
        if (off)
            return x;
        ++x;
    }
}

static inline t_forcebatch *forcebatch_p(t_forcep *fp, uint i) {
    return (t_forcebatch *)(
        &(((char *)fp->batch)[i * size_forcebatch()])
    );
}

static inline bool is_tail(t_forcebatch *bp) {
    return (bp->x[bp->primary] == 0) ? 1 : 0;
}

static inline bool has_tail(t_forcep *fp) {
    return is_tail(forcebatch_p(fp, fp->count - 1));
}

static inline void fpb_init(t_forcebatch *fpb, uint vi, uint x) {
    fpb->primary = vi;
    memset(&fpb->x[0], 0, k * sizeof(uint));
    if (x)
        fpb->x[vi] = x;
}

typedef enum {
    TFP_BAD = 0,
    TFP_SINGLE,
    TFP_GOOD
} e_tfp;
e_tfp test_forcep(t_forcebatch *fpb, uint p, uint vi, uint x) {
    bool seen_any = 0;
    bool seen_odd = 0;

    fpb_init(fpb, vi, x);
    if (modfix_count) {
        uint pe = x ? x - 1 : x;
        for (uint i = 0; i < modfix_count; ++i) {
            t_modfix *mfp = &modfix[i];
            uint me = mpz_valuation(mfp->mod, p);
            if (me == 0)
                continue;
            mpz_add_ui(Z(tfp_v), mfp->val, TYPE_OFFSET(vi));
            /* v_i := tfp_v (mod mfp->mod), with negate */
            uint ve = mpz_sgn(Z(tfp_v)) ? mpz_valuation(Z(tfp_v), p) : me;
            if (ve > me)
                ve = me;
            if (pe >= me) {
                if (ve == me) {
                    if (mfp->negate)
                        /* v_i != 0 (mod 2^2) contradicts test 2^3 */
                        return TFP_BAD;
                    else
                        /* v_i == 0 (mod 2^2) is fine for test 2^3 */
                        continue;
                } else { /* ve < me */
                    if (mfp->negate)
                        /* v_i != 2 (mod 2^2) is fine for test 2^3 */
                        continue;
                    else
                        /* v_i == 2 (mod 2^2) contradicts test 2^3 */
                        return TFP_BAD;
                }
            } else { /* pe < me */
                if (ve < pe) {
                    if (mfp->negate)
                        /* v_i != 2 (mod 2^3) is fine for test 2^2 */
                        continue;
                    else
                        /* v_i == 2 (mod 2^3) contradicts test 2^2 */
                        return TFP_BAD;
                } else if (ve == pe) {
                    if (mfp->negate) {
                        if (p == 2 && ve + 1 == me)
                            /* v_i != 2^2 (mod 2^3) contradicts test 2^2 */
                            return TFP_BAD;
                        /* v_i != 2^1 (mod 2^3) is fine for test 2^1 */
                        /* v_i != 3^2 (mod 3^3) is fine for test 3^2 */
                        continue;
                    } else {
                        /* v_i == 2^2 (mod 2^3) is fine for test 2^2,
                         * but there may be a secondary that fails */
                        for (uint vj = 0; vj < k; ++vj) {
                            if (vi == vj)
                                continue;
                            uint off = (vi > vj) ? vi - vj : vj - vi;
                            uint pej = simple_valuation(TYPE_OFFSET(off), p);
                            if (pej == 0)
                                continue;
                            mpz_add_ui(Z(tfp_v), mfp->val, TYPE_OFFSET(vj));
                            uint vej = mpz_sgn(Z(tfp_v))
                                    ? mpz_valuation(Z(tfp_v), p) : me;
                            /* the secondary would fail */
                            if (vej > pej)
                                return TFP_BAD;
                        }
                        continue;
                    }
                } else { /* ve > pe */
                    if (mfp->negate)
                        /* v_i != 2^2 (mod 2^3) is fine for test 2^1 */
                        continue;
                    else
                        /* v_i == 2^2 (mod 2^3) contradicts test 2^1 */
                        return TFP_BAD;
                }
            }
        }
    }

    if (x == 0) {
        /* p^0 is valid iff the differences are a multiple of p */
        if (TYPE_OFFSET(1) % p)
            return TFP_BAD;
        return TFP_GOOD;
    }

    if (!ispow2(x))
        seen_odd = 1;

    uint ei = x - 1;
    for (uint j = 1; j <= vi; ++j) {
        uint vj = vi - j;
        uint off = TYPE_OFFSET(j);
        uint ej = simple_valuation(off, p);
        if (ej == 0)
            continue;
        if (target_t(vj) % (ej + 1))
            return TFP_BAD;
        fpb->x[vj] = ej + 1;
        seen_any = 1;
        if (!ispow2(ej + 1))
            seen_odd = 1;
        if (ej < ei)
            continue;
        /* Earlier element cannot have same or higher power of p */
        return TFP_BAD;
    }
    if (p > 8 * sizeof(ulong))
        fail("TODO: cope with p > %u", 8 * sizeof(ulong));
    /* set bits for moduli 1 .. p - 1 */
    ulong seen_same = (1 << p) - 2;
    for (uint j = 1; j + vi < k; ++j) {
        uint vj = vi + j;
        uint off = TYPE_OFFSET(j);
        uint ej = simple_valuation(off, p);
        if (ej == 0)
            continue;
        seen_any = 1;
        if (!ispow2(ej + 1))
            seen_odd = 1;
        if (ej > ei) {
            /* p^e_i + p^e_j will have valuation e_i */
            fpb->x[vj] = ei + 1;
            continue;
        }
        if (target_t(vj) % (ej + 1))
            return TFP_BAD;
        fpb->x[vj] = ej + 1;
        if (ej < ei)
            continue;
        /* p^e_i + p^e_i can have valuation e_i as long as we don't
         * exceed the (p-1) possible values mod p */
        for (uint i = 0; i < ei; ++i)
            off /= p;
        seen_same &= ~(1 << (off % p));
    }
    if (seen_same == 0)
        /* all moduli seen, so one must have a higher power of p */
        return TFP_BAD;

    if (unforce_all && p >= unforce_all && !seen_odd)
        return TFP_SINGLE;
    if (seen_any)
        return TFP_GOOD;
    return TFP_SINGLE;
}

void prep_forcep(void) {
    mpz_t pz;
    uint p;
    uint pi[k];

    forcedp = 0;
    mpz_init_set_ui(pz, 1);
#if defined(TYPE_o) || defined(TYPE_r)
    while (1) {
        _GMP_next_prime(pz);
        p = mpz_get_ui(pz);
        if (p > k)
            break;
        pi[forcedp++] = p;
    }
#elif defined(TYPE_a)
    /* divisors of n must be force_all, so must come before other primes */
    for (uint i = 0; i < nf.count; ++i) {
        p = (uint)nf.ppow[i].p;
        pi[forcedp++] = p;
    }
    while (1) {
        _GMP_next_prime(pz);
        p = mpz_get_ui(pz);
        if (p > k)
            break;
        if (n % p)
            pi[forcedp++] = p;
    }
#endif
    mpz_clear(pz);

    uint maxbatch = 0;
    for (uint i = 0; i < k; ++i)
        maxbatch += divisors[ target_t(i) ].alldiv;

    /* TODO: fix tail handling (see comment in recurse()), then we can
     * remove this block */
    if (unforce_all) {
        uint need = 0;
        for (uint i = forcedp; i > 0; ) {
            --i;
            if (need && pi[i] >= unforce_all)
                fail("-F%u is minimum supported for now", need);
            if (!need && pi[i] < k)
                need = pi[i];
        }
    }

    forcep = malloc(forcedp * sizeof(t_forcep));
    for (uint fpi = 0; fpi < forcedp; ++fpi) {
        p = pi[fpi];
        t_forcep *fp = &forcep[fpi];
        fp->p = p;
        fp->count = 0;
        fp->batch = malloc(maxbatch * size_forcebatch());
        t_forcebatch *fbp = forcebatch_p(fp, 0);

        bool keep_single = (p <= force_all) ? 1 : 0;
#if defined(TYPE_o)
        if (n & 3)
            keep_single = 1;
#elif defined(TYPE_a)
        if ((n % p) == 0)
            keep_single = 1;
#endif
        bool have_unforced_tail = 0;
        for (uint vi = 0; vi < k; ++vi) {
            t_divisors *d = &divisors[ target_t(vi) ];
            for (uint di = 0; di < d->alldiv; ++di) {
                uint fx = d->div[di];
                if (fx == 1)
                    continue;
                uint status = test_forcep(fbp, p, vi, fx);
                if (status == TFP_BAD)
                    continue;
                if (status == TFP_SINGLE && !keep_single) {
                    have_unforced_tail = 1;
                    continue;
                }
                /* else status == TFP_GOOD */
                fbp = forcebatch_p(fp, ++fp->count);
            }
        }
#if defined(TYPE_a)
        uint status = test_forcep(fbp, p, 0, 0);
        if (status != TFP_BAD)
            fbp = forcebatch_p(fp, ++fp->count);
#endif
        if (fp->count == 0) {
            if (have_unforced_tail) {
                forcedp = fpi;
                free(fp->batch);
                break;
            }
            if (seen_best)
                break;
            report(
                "406 Error: no valid arrangement of powers for p=%u (%.2fs)\n",
                p, seconds(utime())
            );
            fail_silent();
        }
        if (have_unforced_tail) {
            fpb_init(fbp, 1, 0);
            fbp = forcebatch_p(fp, ++fp->count);
        }
        fp->batch = realloc(fp->batch, fp->count * size_forcebatch());
    }
}

void disp_forcep(void) {
    uint plen;
    for (uint fi = 0; fi < forcedp; ++fi) {
        t_forcep *fp = &forcep[fi];
        printf("204 p=%u count %u\n", fp->p, fp->count);
        for (uint bi = 0; bi < fp->count; ++bi) {
            t_forcebatch *fbp = forcebatch_p(fp, bi);
            printf("204 %u: primary %u [", bi, fbp->primary);
            for (uint xi = 0; xi < k; ++xi) {
                if (xi != 0)
                    printf(" ");
                if (fbp->x[xi])
                    printf("%u", fbp->x[xi] - 1);
                else
                    printf(".");
            }
            printf("]\n");
        }
    }
}

void ston(mpz_t targ, char *s) {
    char *t = strchr(s, 'e');
    if (t) {
        *t = 0;
        if (mpz_set_str(targ, s, 10) != 0)
            fail("Expected '%s' to be a valid number", s);
        ulong exp = strtoul(&t[1], NULL, 10);
        mpz_ui_pow_ui(Z(s_exp), 10, exp);
        mpz_mul(targ, targ, Z(s_exp));
        *t = 'e';
    } else {
        if (mpz_set_str(targ, s, 10) != 0)
            fail("Expected '%s' to be a valid number", s);
    }
}

ulong ulston(char *s) {
    ston(Z(uls_temp), s);
    if (mpz_fits_ulong_p(Z(uls_temp)))
        return mpz_get_ui(Z(uls_temp));
    fail("value '%s' out of range of ulong", s);
}

void do_prep_mp(ulong **mp, char *sp, char *spx) {
    *mp = calloc(n, sizeof(ulong));
    if (sp) {
        char *t = strchr(sp, '^');
        t_divisors *dp = &divisors[n];
        if (t) {
            *t = 0;
            ulong p = ulston(sp);
            uint e = ulston(t + 1);
            *t = '^';
            mpz_ui_pow_ui(Z(temp), p, e);
            for (uint di = 0; di < dp->alldiv; ++di) {
                uint dm = dp->div[di] - 1;
                if (highpow ? dm == 0 : ispow2(dm + 1))
                    break;
                mpz_root(Z(wv_cand), Z(temp), dm);
                if (mpz_fits_ulong_p(Z(wv_cand)))
                    (*mp)[dm] = mpz_get_ui(Z(wv_cand));
                else
                    fail("%lu^%u does not fit 64-bit for p^%u", p, e, dm);
            }
        } else {
            ulong p = ulston(sp);
            for (uint di = 0; di < dp->alldiv; ++di) {
                uint dm = dp->div[di] - 1;
                if (highpow ? dm == 0 : ispow2(dm + 1))
                    break;
                (*mp)[dm] = p;
            }
        }
    }
    char *sp2 = spx;
    while (sp2 && *sp2) {
        char *tc = strchr(sp2, ',');
        if (tc)
            *tc = 0;
        char *t = strchr(sp2, '^');
        if (!t) {
            if (tc)
                *tc = ',';
            fail("missing '^' in '%s'", spx);
        }
        *t = 0;
        ulong p = ulston(sp2);
        uint e = ulston(t + 1);
        *t = '^';
        if (tc)
            *tc = ',';
        if (n % (e + 1))
            fail("invalid power %u in '%s'", e, spx);
        (*mp)[e] = p;
        if (tc)
            sp2 = tc + 1;
        else
            break;
    }
}

void disp_px(char *name, ulong *mp) {
    report("311 %s: [ ", name);
    t_divisors *dp = &divisors[n];
    for (uint di = 0; di < dp->alldiv; ++di) {
        uint dm = dp->div[di] - 1;
        if (highpow ? dm == 0 : ispow2(dm + 1))
            break;
        if (di)
            report("; ");
        report("%lu^%u", mp[dm], dm);
    }
    report(" ]\n");
}

void prep_mp(void) {
    do_prep_mp(&minp, sminp, sminpx);
    if (need_midp) {
        /* when -W is used, we set maxp from smidp to mark the upper
         * limit for normal allocation, and midp from smaxp to mark the
         * upper limit for walk_midp() */
        do_prep_mp(&maxp, smidp, smidpx);
        do_prep_mp(&midp, smaxp, smaxpx);
    } else
        do_prep_mp(&maxp, smaxp, smaxpx);
    need_maxp = (smaxp || smaxpx || need_midp) ? 1 : 0;

    if (debugx) {
        disp_px("minp", minp);
        if (need_midp) {
            disp_px("midp", maxp);
            disp_px("maxp", midp);
        } else
            disp_px("maxp", maxp);
    }
}

/* Record a new square at v_i; return FALSE if invalid.
 * Finds the quadratic (or higher-order) residues; stash them for later
 * propagation if this is the first square; fail if there are none.
 */
bool alloc_square(t_level *cur, uint vi) {
    t_value *v = &value[vi];
    uint vlevel = cur->vlevel[vi];
    t_allocation *ap = &v->alloc[vlevel - 1];
    uint sqi = cur->have_square++;
    uint g = divisors[ap->t].gcddm;
    if (sqi == 0) {
        sq0 = vi;
        sqg[vlevel - 1] = g;
    }

    /* if this is first square, store in the level for further propagation;
     * else use level 0 as temporary */
    uint stash_level = (sqi == 0) ? cur->level : 0;
    /* o = (rq + i) / q */
    mpz_add_ui(Z(asq_o), cur->rq, TYPE_OFFSET(vi));
    mpz_divexact(Z(asq_o), Z(asq_o), ap->q);
    /* qq = aq / q */
    mpz_divexact(Z(asq_qq), cur->aq, ap->q);

    allrootmod(stash_level, Z(asq_o), g, Z(asq_qq));
    t_results *rp = res_array(stash_level);
    if (rp->count == 0)
        return 0;
    return 1;
}

/* If any value is forced to be square even before any allocations,
 * we must insert a dummy level (so there is a unique place to hold
 * the set of valid residues), and then call alloc_square() to
 * initialize things correctly.
 */
void prep_presquare(void) {
    bool saw_square = 0;
    for (uint vi = 0; vi < k; ++vi)
        if (target_t(vi) & 1)
            saw_square = 1;
    if (saw_square) {
        /* we rely on resarray(0) being available for other uses, so we
         * must use a dummy level here before allocating the square(s)
         */
        t_level *prev = &levels[level - 1];
        t_level *cur = &levels[level];
        cur->have_min = prev->have_min;
        cur->nextpi = prev->nextpi;
        cur->maxp = prev->maxp;
        cur->fp_need = prev->fp_need;
        memcpy(cur->vlevel, prev->vlevel, k * sizeof(uint));
        memcpy(cur->pfreev, prev->pfreev, pfree_vecsize * sizeof(uint));
        mpz_set(cur->aq, prev->aq);
        mpz_set(cur->rq, prev->rq);
        cur->is_forced = 2;     /* special value for dummy entry */
        cur->p = 0;
        cur->have_square = 0;
        for (uint vi = 0; vi < k; ++vi)
            if (target_t(vi) & 1)
                alloc_square(cur, vi);
        ++level;
        ++final_level;
    }
}

void init_post(void) {
    init_tau(rough, opt_flake);
    init_stats(k);
    alloc_taum(k);
    if (randseed != 1) {
        /* hard to guarantee we haven't used any randomness before this.
         * note also that this will give different results for a run that
         * is stopped and recovered.
         */
        clear_randstate();
        init_randstate(randseed);
    }
    if (rpath) {
        printf("path %s\n", rpath);
        if (!skip_recover) {
            FILE *fp = fopen(rpath, "r");
            if (fp) {
                recover(fp);
                fclose(fp);
            }
        }

        rfp = fopen(rpath, "a");
        if (rfp == NULL)
            fail("%s: %s", rpath, strerror(errno));
        setlinebuf(rfp);
    }
    if (init_pattern)
        parse_305(init_pattern, &istack);
#ifdef HAVE_SETPROCTITLE
    setproctitle("-D(%u %u)", n, k);
#endif
    simple_fact(n, &nf);
    prep_target();
    /* level[0] is special, level[1] is special if any target_t is odd;
     * then we can have forcedp batch allocations and maxodd * k normal
     * allocations; however we don't know forcedp yet, only that it will
     * be at most |{ p: p < k }| for TYPE_o and TYPE_r, and
     * |{ p: p < k or p | n }| for TYPE_a.
     * So pick something conservative enough for all cases.
     */
    maxlevel = 1 + 1 + k * (highpow ? maxfact : maxodd) + k
#if defined(TYPE_a)
            + nf.count
#endif
            ;

    /* Strategy 1 is preferred when n is divisible by two or more
     * distinct odd primes. Otherwise, strategy 0 always gives the same
     * results, and is a bit faster. */
    if (!strategy_set)
        strategy = (nf.count > (highpow ? 1 : 2)) ? 1 : 0;

    init_rootmod(maxlevel);
    prep_fact();
    prep_maxforce();
    prep_forcep();
    if (debugf)
        disp_forcep();
    prep_primes();  /* needs forcedp */
    prep_mintau();
    prep_mp();  /* maxp[], minp[], midp[] */
    sqg = malloc(maxfact * sizeof(uint));

    uint maxmidpp = 0;
    for (uint i = 0; i < k; ++i)
        maxmidpp += divisors[ target_t(i) ].alldiv;
    midpp = malloc(sizeof(t_midpp) * maxmidpp);

    if (debugw) {
        if (!debugw_count)
            diag_delay = 0;
        need_work = 1;
        need_diag = 1;
    }
    diagt = diag_delay;
    if (rfp)
        logt = log_delay;
    else
        logt = log_delay = 0;
    init_time();

    init_levels();
    init_value();
    countr = 0;
    countw = 0;
    countwi = 0;

    wv_o = malloc(k * sizeof(mpz_t));
    wv_qq = malloc(k * sizeof(mpz_t));
    for (uint i = 0; i < k; ++i) {
        mpz_init(wv_o[i]);
        mpz_init(wv_qq[i]);
    }
    diag_buf = malloc(DIAG_BUFSIZE);
    init_diag();    /* ignore result: worst case we lose ^Z handling */

    if (gain2 == 0 && antigain2 == 0) {
        gain2 = gain;
        antigain2 = antigain;
    }
}

void report_init(FILE *fp, char *prog) {
    fprintf(fp, "001 %spc%cul(%u %u)",
            (start_seen ? "recover " : ""), typename(), n, k);

    if (strategy) {
        if (strategy == STRATEGY_FIXED) {
            fprintf(fp, "-js");
            for (uint i = 0; i < fixed_level; ++i) {
                if (i)
                    fprintf(fp, ",");
                fprintf(fp, "%u", fixed_v[i]);
            }
        } else
            fprintf(fp, " -j%u", strategy);
    }
    if (opt_print)
        fprintf(fp, " -o");
    if (limp_cap)
        fprintf(fp, " -P%lu", limp_cap);
    if (sminp || smaxp) {
        fprintf(fp, " -p");
        if (sminp)
            fprintf(fp, "%s:", sminp);
        if (smaxp)
            fprintf(fp, "%s", smaxp);
    }
    if (sminpx || smaxpx) {
        fprintf(fp, " -px");
        if (sminpx)
            fprintf(fp, "%s:", sminpx);
        if (smaxpx)
            fprintf(fp, "%s", smaxpx);
    }
    if (smidp) {
        char *ww = midp_only ? "W" : "";
        fprintf(fp, " -W%s%s", ww, smidp);
    }
    if (smidpx) {
        char *ww = midp_only ? "W" : "";
        fprintf(fp, " -W%sx%s", ww, smidpx);
    }
    if (force_all)
        fprintf(fp, " -f%u", force_all);
    if (unforce_all) {
        fprintf(fp, " -F");
        if (unforce_all > 1)
            fprintf(fp, "%u", unforce_all);
    }
    if (gain > 1 || antigain > 1) {
        fprintf(fp, " -g");
        if (antigain > 1)
            fprintf(fp, "%lu:", antigain);
        if (gain > 1)
            fprintf(fp, "%lu", gain);
    }
    if (gain2 != gain || antigain2 != antigain) {
        fprintf(fp, " -G");
        if (antigain2 > 1)
            fprintf(fp, "%lu:", antigain2);
        if (gain2 > 1)
            fprintf(fp, "%lu", gain2);
    }
    if (mpz_sgn(zmin) || mpz_sgn(zmax)) {
        fprintf(fp, " -x");
        if (mpz_sgn(zmin))
            gmp_fprintf(fp, "%Zu:", zmin);
        if (mpz_sgn(zmax))
            gmp_fprintf(fp, "%Zu", zmax);
    }
    if (randseed != 1)
        fprintf(fp, " -s%lu", randseed);
    if (rough)
        fprintf(fp, " -h%u", rough);
    if (opt_batch_min >= 0) {
        fprintf(fp, " -b%u", opt_batch_min);
        if (opt_batch_min != opt_batch_max) {
            fprintf(fp, ":");
            if (opt_batch_max < INT_MAX)
                fprintf(fp, "%u", opt_batch_max);
        }
    }
    if (check > 1) {
        fprintf(fp, " -c%u", check);
        if (check_prime)
            fprintf(fp, " -cp%u", check_prime);
        if (check_ratio > 1.0)
            fprintf(fp, " -cr%f", check_ratio);
        if (check_chunk)
            fprintf(fp, " -cc%u", check_chunk);
    }
    if (modfix) {
        for (uint i = 0; i < modfix_count; ++i) {
            t_modfix *mfp = &modfix[i];
            gmp_fprintf(fp, " -m%Zu%c%Zu",
                    mfp->mod, mfp->negate ? '!' : '=', mfp->val);
        }
    }
    if (clock_is_realtime)
        fprintf(fp, " *RT*");
    fprintf(fp, "\n");
    if (debugt) {
        fprintf(fp, "312 target tau: [");
        for (uint i = 0; i < k; ++i) {
            if (i)
                fprintf(fp, " ");
            fprintf(fp, "%d", target_t(i));
        }
        fprintf(fp, "]\n");
    }
    fflush(fp);
}

void set_minmax(char *s) {
    char *t = strchr(s, ':');
    if (t) {
        *t = 0;
        if (*s)
            ston(zmin, s);
        else
            mpz_set_ui(zmin, 0);
        if (t[1])
            ston(zmax, &t[1]);
        else
            mpz_set_ui(zmax, 0);
    } else {
        mpz_set_ui(zmin, 0);
        ston(zmax, s);
    }
}

void set_gain(char *s) {
    char *t = strchr(s, ':');
    if (t) {
        *t = 0;
        antigain = *s ? ulston(s) : 0;
        gain = t[1] ? ulston(&t[1]) : 0;
    } else {
        antigain = 0;
        gain = ulston(s);
    }
}

void set_gain2(char *s) {
    char *t = strchr(s, ':');
    if (t) {
        *t = 0;
        antigain2 = *s ? ulston(s) : 0;
        gain2 = t[1] ? ulston(&t[1]) : 0;
    } else {
        antigain2 = 0;
        gain2 = ulston(s);
    }
}

void set_cap(char *s) {
    bool is_x = (*s == 'x');
    if (is_x)
        ++s;
    char *t = strchr(s, ':');
    if (t) {
        *t = 0;
        *(is_x ? &sminpx : &sminp) = s;
        *(is_x ? &smaxpx : &smaxp) = t + 1;
    } else {
        *(is_x ? &smaxpx : &smaxp) = s;
    }
}

void set_batch(char *s) {
    char *t = strchr(s, ':');
    if (t) {
        *t = 0;
        opt_batch_min = *s ? strtoul(s, NULL, 10) : 0;
        opt_batch_max = t[1] ? strtoul(&t[1], NULL, 10) : INT_MAX;
    } else {
        opt_batch_min = strtoul(s, NULL, 10);
        opt_batch_max = opt_batch_min;
    }
    opt_alloc |= 1;
}

void done_modfix(void) {
    for (uint mfi = 0; mfi < modfix_count; ++mfi) {
        mpz_clear(modfix[mfi].mod);
        mpz_clear(modfix[mfi].val);
    }
    free(modfix);
}

void set_modfix(char *s) {
    bool negate = 0;
    char *t = strchr(s, '=');
    if (!t) {
        negate = 1;
        t = strchr(s, '!');
        if (!t)
            fail("-m option must be of form '-m<modulus>=<value>'"
                    " or '-m<modulus>!<value>'");
    }
    *t++ = 0;
    uint mfi = modfix_count++;
    modfix = realloc(modfix, modfix_count * sizeof(t_modfix));
    t_modfix *mfp = &modfix[mfi];
    mpz_init(mfp->mod);
    mpz_init(mfp->val);
    ston(mfp->mod, s);
    ston(mfp->val, t);
    mfp->negate = negate;
}

/* Return p if no inverse exists.
 * TODO: mod to ulong, use the fast 64-bit mulmod from MPU-mulmod.h.
 */
ulong small_divmod(mpz_t za, mpz_t zb, ulong p) {
    mpz_set_ui(Z(sdm_p), p);
    mpz_mod_ui(Z(sdm_r), zb, p);
    if (!mpz_invert(Z(sdm_r), Z(sdm_r), Z(sdm_p)))
        return p;
    mpz_mul(Z(sdm_r), Z(sdm_r), za);
    mpz_mod_ui(Z(sdm_r), Z(sdm_r), p);
    return mpz_get_ui(Z(sdm_r));
}

/* Return FALSE if no inverse exists, else sets result = (a / b) mod m.
 */
bool divmod(mpz_t result, mpz_t a, mpz_t b, mpz_t m) {
    mpz_mod(Z(dm_r), b, m);
    if (!mpz_invert(Z(dm_r), Z(dm_r), m))
        return 0;
    mpz_mul(result, Z(dm_r), a);
    mpz_mod(result, result, m);
    return 1;
}

/* This allocation uses what was the next unused prime, to find the
 * index of the new next unused prime.
 */
uint find_nextpi(t_level *cur, uint pi) {
    uint *pv = cur->pfreev;
    uint off = pi >> 5;
    uint bit = pi & 0x1f;
    while (off < pfree_vecsize) {
        uint v = pv[off] & ~((1 << bit) - 1);
        int ffs = __builtin_ffs((int)v);
        if (ffs)
            return (off << 5) + ffs - 1;
        ++off;
        bit = 0;
    }
    fail("panic: find_nextpi() fell off end of bit vector");
}

/* Find index of next unused forced prime */
static inline uint next_fpi(t_level *prev) {
    return __builtin_ffs((signed int)prev->fp_need) - 1;
}

uint taum_fail(char *legend, mpz_t target, uint count, t_tm *tm) {
    keep_diag();

    /* log to file only if opt_print */
    FILE *was_rfp;
    if (!opt_print) {
        was_rfp = rfp;
        rfp = NULL;
    }

    /* FIXME: use a real code for these, and cope with that.
     * That means that candidates lower the upper limit as usual, but
     * if any of these targets lie below the best candidate we cannot be
     * final.
     */
    report("000 tmf %s %Zu (%.2fs)\n", legend, target, seconds(utime()));
    for (uint i = 0; i < count; ++i)
        report("000 (%u) %u -> %u: %Zu\n", i, tm[i].vi, tm[i].t, tm[i].n);

    if (!opt_print) {
        rfp = was_rfp;
        fail_silent();
    }
    return count;
}
uint walk_1_failure(uint count, t_tm *tm) {
    return taum_fail("walk_1", Z(w1_v), count, tm);
}
uint walk_v_failure(uint count, t_tm *tm) {
    mpz_mul_ui(Z(wv_cand), wv_qq[0], g_ati);
    mpz_add(Z(wv_cand), Z(wv_cand), wv_o[0]);
    mpz_mul(Z(wv_cand), Z(wv_cand), *g_q0);
    return taum_fail("walk_v", Z(wv_cand), count, tm);
}
uint walk_zv_failure(uint count, t_tm *tm) {
    mpz_mul(Z(wv_cand), wv_qq[0], Z(wv_ati));
    mpz_add(Z(wv_cand), Z(wv_cand), wv_o[0]);
    mpz_mul(Z(wv_cand), Z(wv_cand), *g_q0);
    return taum_fail("walk_v", Z(wv_cand), count, tm);
}

bool test_prime(mpz_t qq, mpz_t o, ulong ati) {
    mpz_mul_ui(Z(wv_cand), qq, ati);
    mpz_add(Z(wv_cand), Z(wv_cand), o);
    return _GMP_is_prob_prime(Z(wv_cand));
}

bool test_zprime(mpz_t qq, mpz_t o, mpz_t ati) {
    mpz_mul(Z(wv_cand), qq, ati);
    mpz_add(Z(wv_cand), Z(wv_cand), o);
    return _GMP_is_prob_prime(Z(wv_cand));
}

bool test_1primes(uint *need, uint nc) {
    uint good = 0;
    test_multi_reset();
    for (uint i = 0; i < nc; ++i) {
        uint vi = need[i];
        mpz_set(Z(temp), wv_o[vi]);
        if (!test_prime_append(Z(temp), vi)) {
            TRACK_BAD(good, vi);
            return 0;
        }
#ifdef TRACK_STATS
        if (taum[tm_count - 1].state == 0)
            ++good;
#endif
    }
    uint remain = test_prime_run();
    if (remain) {
        TRACK_BAD(nc - remain, taum[0].vi);
        return 0;
    }
    return 1;
}

bool test_1multi(uint *need, uint nc, uint *t, tau_failure_handler tfh) {
    uint good = 0;
    test_multi_reset();
    for (uint i = 0; i < nc; ++i) {
        uint vi = need[i];
        mpz_set(Z(temp), wv_o[vi]);
        if (!test_multi_append(Z(temp), vi, t[vi], 1)) {
            TRACK_BAD(k - nc + good, vi);
            return 0;
        }
#ifdef TRACK_STATS
        if (taum[tm_count - 1].state == 0)
            ++good;
#endif
    }
    uint remain = test_multi_run(tfh);
    TRACK_MULTI(remain, need, taum);
    return remain ? 0 : 1;
}

bool test_primes(uint *need, uint nc, ulong ati) {
    uint good = 0;
    test_multi_reset();
    for (uint i = 0; i < nc; ++i) {
        uint vi = need[i];
        mpz_mul_ui(Z(temp), wv_qq[vi], ati);
        mpz_add(Z(temp), Z(temp), wv_o[vi]);
        if (!test_prime_append(Z(temp), vi)) {
            TRACK_BAD(good, vi);
            return 0;
        }
#ifdef TRACK_STATS
        if (taum[tm_count - 1].state == 0)
            ++good;
#endif
    }
    uint remain = test_prime_run();
    if (remain) {
        TRACK_BAD(nc - remain, taum[0].vi);
        return 0;
    }
    return 1;
}

bool test_zprimes(uint *need, uint nc, mpz_t ati) {
    uint good = 0;
    test_multi_reset();
    for (uint i = 0; i < nc; ++i) {
        uint vi = need[i];
        mpz_mul(Z(temp), wv_qq[vi], ati);
        mpz_add(Z(temp), Z(temp), wv_o[vi]);
        if (!test_prime_append(Z(temp), vi)) {
            TRACK_BAD(good, vi);
            return 0;
        }
#ifdef TRACK_STATS
        if (taum[tm_count - 1].state == 0)
            ++good;
#endif
    }
    uint remain = test_prime_run();
    if (remain) {
        TRACK_BAD(nc - remain, taum[0].vi);
        return 0;
    }
    return 1;
}

bool test_multi(
    uint *need, uint nc, ulong ati, uint *t, tau_failure_handler tfh
) {
    uint good = 0;
    test_multi_reset();
    for (uint i = 0; i < nc; ++i) {
        uint vi = need[i];
        mpz_mul_ui(Z(temp), wv_qq[vi], ati);
        mpz_add(Z(temp), Z(temp), wv_o[vi]);
        if (!test_multi_append(Z(temp), vi, t[vi], 1)) {
            TRACK_BAD(k - nc + good, vi);
            return 0;
        }
#ifdef TRACK_STATS
        if (taum[tm_count - 1].state == 0)
            ++good;
#endif
    }
    uint remain = test_multi_run(tfh);
    TRACK_MULTI(remain, need, taum);
    return remain ? 0 : 1;
}

bool test_zmulti(
    uint *need, uint nc, mpz_t ati, uint *t, tau_failure_handler tfh
) {
    uint good = 0;
    test_multi_reset();
    for (uint i = 0; i < nc; ++i) {
        uint vi = need[i];
        mpz_mul(Z(temp), wv_qq[vi], ati);
        mpz_add(Z(temp), Z(temp), wv_o[vi]);
        if (!test_multi_append(Z(temp), vi, t[vi], 1)) {
            TRACK_BAD(k - nc + good, vi);
            return 0;
        }
#ifdef TRACK_STATS
        if (taum[tm_count - 1].state == 0)
            ++good;
#endif
    }
    uint remain = test_multi_run(tfh);
    TRACK_MULTI(remain, need, taum);
    return remain ? 0 : 1;
}

bool test_other(mpz_t qq, mpz_t o, ulong ati, uint t) {
    mpz_mul_ui(Z(wv_cand), qq, ati);
    mpz_add(Z(wv_cand), Z(wv_cand), o);
    return is_taux(Z(wv_cand), t, 1);
}
bool test_zother(mpz_t qq, mpz_t o, mpz_t ati, uint t) {
    mpz_mul(Z(wv_cand), qq, ati);
    mpz_add(Z(wv_cand), Z(wv_cand), o);
    return is_taux(Z(wv_cand), t, 1);
}

/* Sort need_prime by qq multiplier ascending */
int prime_comparator(const void *va, const void *vb) {
    uint a = *(uint *)va;
    uint b = *(uint *)vb;
    return mpz_cmp(wv_qq[a], wv_qq[b]);
}

/* Sort need_other by tau (power of 2 ascending, then size ascending),
 * then by qq multiplier ascending
 * TODO: if we implement trial division to higher levels to show
 * a given tau is not reachable, we may want tau by size descending.
 */
uint *oc_t;
int other_comparator(const void *va, const void *vb) {
    uint a = *(uint *)va;
    uint b = *(uint *)vb;
    uint at2 = oc_t[a] ^ (oc_t[a] - 1);
    uint bt2 = oc_t[b] ^ (oc_t[b] - 1);
    if (at2 < bt2)
        return -1;
    if (at2 > bt2)
        return 1;
    if (oc_t[a] < oc_t[b])
        return -1;
    if (oc_t[a] > oc_t[b])
        return 1;
    return mpz_cmp(wv_qq[a], wv_qq[b]);
}

/* Sort inverses by modulus ascending */
int inv_comparator(const void *va, const void *vb) {
    t_mod *a = (t_mod *)va;
    t_mod *b = (t_mod *)vb;
    return (b->m < a->m) - (a->m < b->m);
}

void walk_v(t_level *cur_level, mpz_t start) {
#ifdef SQONLY
    if (!cur_level->have_square)
        return;
#endif
    if (!cur_level->have_min) {
        uint min = minp[cur_level->x - 1];
        if (min)
            level_setp(cur_level, min);
        return;
    }

    mpz_t *q[k];
    mpz_t *m = &cur_level->rq;
    uint t[k];
    mpz_t *aq = &cur_level->aq;
    t_mod inv[maxfact * k];
    uint inv_count = 0;
    uint need_prime[k];
    uint need_square[k];
    uint need_other[k];
    uint npc = 0, nqc = 0, noc = 0;

    ++countw;

    mpz_sub(Z(wv_end), zmax, *m);
    mpz_fdiv_q(Z(wv_end), Z(wv_end), *aq);
    if (mpz_sgn(Z(wv_end)) < 0)
        return;

    if (mpz_sgn(start)) {
        mpz_set(Z(wv_ati), start);
    } else {
        mpz_sub(Z(wv_ati), zmin, *m);
        mpz_cdiv_q(Z(wv_ati), Z(wv_ati), *aq);
    }

    for (uint vi = 0; vi < k; ++vi) {
        t_value *vp = &value[vi];
        uint vlevel = cur_level->vlevel[vi];
        q[vi] = &vp->alloc[vlevel - 1].q;
        t[vi] = vp->alloc[vlevel - 1].t;
        mpz_divexact(wv_qq[vi], *aq, *q[vi]);
        mpz_add_ui(wv_o[vi], *m, TYPE_OFFSET(vi));
        mpz_divexact(wv_o[vi], wv_o[vi], *q[vi]);
        for (uint ai = 1; ai < vlevel; ++ai) {
            t_allocation *ap = &vp->alloc[ai];
            /* the case for p=2 is handled in advance by update_chinese */
            if (ap->p == 2)
                continue;
            ulong inverse = small_divmod(wv_o[vi], wv_qq[vi], ap->p);
            if (inverse < ap->p) {
                t_mod *ip = &inv[inv_count++];
                ip->v = (inverse) ? ap->p - inverse : 0;
                ip->m = ap->p;
            }
        }
        if (t[vi] == 2)
            need_prime[npc++] = vi;
        else if (t[vi] & 1 && nqc < 2)
            need_square[nqc++] = vi;
        else
            need_other[noc++] = vi;
    }
    g_q0 = q[0];

#if 0
    qsort(inv, inv_count, sizeof(t_mod), &inv_comparator);
    qsort(need_prime, npc, sizeof(uint), &prime_comparator);
#endif
    oc_t = t;
    qsort(need_other, noc, sizeof(uint), &other_comparator);

    if (nqc) {
        uint sqi = need_square[0];
        mpz_t *oi = &wv_o[sqi];
        mpz_t *qi = q[sqi];
        mpz_t *qqi = &wv_qq[sqi];
        uint ti = t[sqi];
        if (nqc > 1) {
            uint sqj = need_square[1];
            mpz_t *oj = &wv_o[sqj];
            mpz_t *qj = q[sqj];
            mpz_t *qqj = &wv_qq[sqj];
            uint tj = t[sqj];

            mpz_fdiv_q(Z(wv_endr), zmax, *qi);
            mpz_root(Z(wv_endr), Z(wv_endr), 2);
            /* solve Ax^2 - By^2 = C with x <= D */
            int sqoff = (sqi < sqj)
                ? -(int)TYPE_OFFSET(sqj - sqi)
                : (int)TYPE_OFFSET(sqi - sqj);
            new_pell(*qi, *qj, sqoff, Z(wv_endr));
            uint pc = 0;

            mpz_t *pellx[2];
            uint pellt[2];
            if (ti <= tj || (ti == tj && mpz_cmp(*qi, *qj) > 0)) {
                pellx[0] = ZP(wv_x);
                pellx[1] = ZP(wv_y);
                pellt[0] = ti;
                pellt[1] = tj;
            } else {
                pellx[0] = ZP(wv_y);
                pellx[1] = ZP(wv_x);
                pellt[0] = tj;
                pellt[1] = ti;
            }

            /* FIXME: handle recovery too */
            if (mpz_cmp_ui(zmin, 0) > 0) {
                mpz_fdiv_q(Z(temp), zmin, *qi);
                mpz_sqrt(Z(temp), Z(temp));
                while (next_pell(Z(wv_x), Z(wv_y))) {
                    if (mpz_cmp(Z(temp), Z(wv_x)) <= 0)
                        goto continue_pell;
                    ++pc;
                }
                goto done_pell;
            }

            while (next_pell(Z(wv_x), Z(wv_y))) {
              continue_pell:
                /* v_{sqi} = x^2 . q_i; v_{sqj} = y^2 . q_j */
                mpz_mul(Z(wv_x2), Z(wv_x), Z(wv_x));

                /* verify limit */
                mpz_mul(Z(wv_temp), Z(wv_x2), *qi);
                mpz_sub_ui(Z(wv_temp), Z(wv_temp), TYPE_OFFSET(sqi));
                if (mpz_cmp(Z(wv_temp), zmax) > 0)
                    break;  /* CHECKME: should this be an error? */

                ++countwi;
                ++pc;
                if (need_work)
                    diag_walk_pell(cur_level, pc);

                /* verify mod, coprime and tau */
                mpz_fdiv_r(Z(wv_temp), Z(wv_x2), *qqi);
                if (mpz_cmp(Z(wv_temp), *oi) != 0)
                    continue;   /* CHECKME: should this be an error? */
                mpz_mul(Z(wv_y2), Z(wv_y), Z(wv_y));
                mpz_fdiv_r(Z(wv_temp), Z(wv_y2), *qqj);
                if (mpz_cmp(Z(wv_temp), *oj) != 0)
                    continue;   /* CHECKME: should this be an error? */
                mpz_gcd(Z(wv_temp), Z(wv_x), *qqi);
                if (mpz_cmp_ui(Z(wv_temp), 1) != 0)
                    continue;
                mpz_gcd(Z(wv_temp), Z(wv_y), *qqj);
                if (mpz_cmp_ui(Z(wv_temp), 1) != 0)
                    continue;

                test_multi_reset();
                /* note: steals Z(wv_x), Z(wv_y) */
                /* FIXME: order of (sqi, sqj), if we care */
                if (!test_multi_append(*pellx[0], sqi, pellt[0], 2)) {
                    TRACK_BAD(0, sqi);
                    goto next_pell;
                }
                if (!test_multi_append(*pellx[1], sqj, pellt[1], 2)) {
                    TRACK_BAD(1, sqj);
                    goto next_pell;
                }

                mpz_sub(Z(wv_ati), Z(wv_x2), *oi);
                mpz_divexact(Z(wv_ati), Z(wv_ati), *qqi);
                mpz_sub(Z(wv_temp), Z(wv_y2), *oj);
                mpz_divexact(Z(wv_temp), Z(wv_temp), *qqj);
                if (mpz_cmp(Z(wv_ati), Z(wv_temp)) != 0)
                    continue;   /* CHECKME: should this be an error? */

                /* now test the rest */
                for (uint ii = 0; ii < inv_count; ++ii) {
                    t_mod *ip = &inv[ii];
                    if (mpz_fdiv_ui(Z(wv_ati), ip->m) == ip->v)
                        goto next_pell;
                }

                /* note: we may have had more than 2 squares */
                for (uint i = 2; i < nqc; ++i) {
                    uint vi = need_square[i];
                    mpz_mul(Z(wv_cand), wv_qq[vi], Z(wv_ati));
                    mpz_add(Z(wv_cand), Z(wv_cand), wv_o[vi]);
                    if (!is_taux(Z(wv_cand), t[vi], 1))
                        goto next_pell;
                }

                if (!test_zprimes(need_prime, npc, Z(wv_ati)))
                    goto next_pell;
                /* TODO: bail and print somewhere here if 'opt_print' */
                if (!test_zmulti(need_other, noc, Z(wv_ati), t, walk_zv_failure))
                    goto next_pell;
                /* have candidate: calculate and apply it */
                mpz_mul(Z(wv_cand), wv_qq[0], Z(wv_ati));
                mpz_add(Z(wv_cand), Z(wv_cand), wv_o[0]);
                mpz_mul(Z(wv_cand), Z(wv_cand), *q[0]);
                if (candidate(Z(wv_cand)))
                    break;

              next_pell:
                ;
            }
          done_pell:
            /* clear_pell(); */
            return;
        }
        /* gcd(d - 1) for all divisors d of ti */
        uint xi = divisors[ti].gcddm;
        bool prime_power = (divisors[ti].alldiv == 2);

        t_results *xr = res_array(cur_level->level);
        qsort(xr->r, xr->count, sizeof(mpz_t), &_mpz_comparator);
        uint rindex = 0;
        if (mpz_sgn(Z(wv_ati)) > 0) {
            mpz_mul(Z(wv_startr), Z(wv_ati), *qqi);
            mpz_add(Z(wv_startr), Z(wv_startr), *oi);
            /* need ceiling of the root */
            mpz_rootrem(Z(wv_startr), Z(wv_temp), Z(wv_startr), xi);
            if (mpz_sgn(Z(wv_temp)))
                mpz_add_ui(Z(wv_startr), Z(wv_startr), 1);
            mpz_fdiv_qr(Z(wv_startr), Z(wv_temp), Z(wv_startr), *qqi);
            /* Note: on recover, we expect an exact match here, but on
             * normal entry we don't. */
            for (uint xmi = 0; xmi < xr->count; ++xmi) {
                int cmp = mpz_cmp(xr->r[xmi], Z(wv_temp));
                if (cmp == 0) {
                    rindex = xmi;
                    break;
                } else if (cmp > 0) {
                    if (mpz_sgn(start) == 0) {
                        rindex = xmi;
                        break;
                    }
                    fail("from restart %Zu no match found for mod %Zu < %Zu\n",
                        Z(wv_ati), Z(wv_temp), xr->r[xmi]
                    );
                }
                if (xmi + 1 == xr->count) {
                    if (mpz_sgn(start) == 0) {
                        rindex = 0;
                        mpz_add_ui(Z(wv_startr), Z(wv_startr), 1);
                        break;
                    }
                    fail("from start %Zu no match found for mod %Zu > %Zu\n",
                        Z(wv_ati), Z(wv_temp), xr->r[xmi]
                    );
                }
            }
            mpz_mul(Z(wv_qqr), *qqi, Z(wv_startr));
        } else {
            mpz_set_ui(Z(wv_qqr), 0);
        }
        mpz_sub(Z(wv_end), zmax, *m);
        mpz_fdiv_q(Z(wv_end), Z(wv_end), *aq);
        mpz_add_ui(Z(wv_endr), zmax, TYPE_OFFSET(sqi));
        mpz_fdiv_q(Z(wv_endr), Z(wv_endr), *qi);
        mpz_root(Z(wv_endr), Z(wv_endr), xi);

        mpz_add(Z(wv_qqnext), Z(wv_qqr), *qqi);
        bool tester = (mpz_cmp(Z(wv_qqnext), Z(wv_endr)) > 0);
        if (check)
            cvec_prep_test(cx0, m, aq);

        while (1) {
            mpz_add(Z(wv_r), Z(wv_qqr), xr->r[rindex]);
            if (tester && mpz_cmp(Z(wv_r), Z(wv_endr)) > 0)
                return;
            ++countwi;
            mpz_pow_ui(Z(wv_rx), Z(wv_r), xi);
            mpz_sub(Z(wv_ati), Z(wv_rx), *oi);
            /* this could be divexact, since we know the roots are valid,
             * or we could verify validity here */
            mpz_fdiv_q(Z(wv_ati), Z(wv_ati), *qqi);
            if (need_work)
                diag_walk_zv(cur_level, Z(wv_ati), Z(wv_end));
            if (check && !cvec_test_prepped(cx0, ZP(wv_ati)))
                goto next_sqati;
            for (uint ii = 0; ii < inv_count; ++ii) {
                t_mod *ip = &inv[ii];
                if (mpz_fdiv_ui(Z(wv_ati), ip->m) == ip->v)
                    goto next_sqati;
            }

            test_multi_reset();
            /* note: test_multi_append() steals Z(wv_r) */
            if (prime_power) {
                if (!_GMP_is_prob_prime(Z(wv_r))) {
                    TRACK_BAD(0, sqi);
                    goto next_sqati;
                } else
                    TRACK_GOOD(0, sqi);
            } else if (!test_multi_append(Z(wv_r), sqi, ti, xi)) {
                TRACK_BAD(0, sqi);
                goto next_sqati;
            }

            if (!test_zprimes(need_prime, npc, Z(wv_ati)))
                goto next_sqati;
            /* TODO: bail and print somewhere here if 'opt_print' */
            if (!test_zmulti(need_other, noc, Z(wv_ati), t, walk_zv_failure))
                goto next_sqati;
            /* have candidate: calculate and apply it */
            mpz_mul(Z(wv_cand), wv_qq[0], Z(wv_ati));
            mpz_add(Z(wv_cand), Z(wv_cand), wv_o[0]);
            mpz_mul(Z(wv_cand), Z(wv_cand), *q[0]);
            if (candidate(Z(wv_cand)))
                return;
          next_sqati:
            ++rindex;
            if (rindex >= xr->count) {
                mpz_swap(Z(wv_qqr), Z(wv_qqnext));
                mpz_add(Z(wv_qqnext), Z(wv_qqr), *qqi);
                tester = (mpz_cmp(Z(wv_qqnext), Z(wv_endr)) > 0);
                rindex = 0;
            }
        }
    }

    bool would_fail = 0;
    ulong end;
    if (mpz_fits_ulong_p(Z(wv_end)))
        end = mpz_get_ui(Z(wv_end));
    else {
        end = ULONG_MAX;
        would_fail = 1;
    }
#ifdef LARGE_MIN
    if (!mpz_fits_ulong_p(Z(wv_ati)))
        fail("TODO: non-square min > 2^64");
#endif
    if (check)
        cvec_prep_test(cx0, m, aq);
    for (ulong ati = mpz_get_ui(Z(wv_ati)); ati <= end; ++ati) {
        ++countwi;
        if (need_work)
            diag_walk_v(cur_level, ati, end);
        if (check && !cvec_test_ui_prepped(cx0, ati))
            goto next_ati;
        for (uint ii = 0; ii < inv_count; ++ii) {
            t_mod *ip = &inv[ii];
            if (ati % ip->m == ip->v)
                goto next_ati;
        }
#ifdef DEBUG_ALL
        mpz_mul_ui(Z(wv_cand), wv_qq[0], ati);
        mpz_add(Z(wv_cand), Z(wv_cand), wv_o[0]);
        mpz_mul(Z(wv_cand), Z(wv_cand), *q[0]);
        gmp_fprintf(rfp, "D %Zu\n", Z(wv_cand));
        fflush(rfp);
#endif
        /* note: we have no squares */
        if (!test_primes(need_prime, npc, ati))
            goto next_ati;
        /* TODO: bail and print somewhere here if 'opt_print' */
        g_ati = ati;
        if (!test_multi(need_other, noc, ati, t, walk_v_failure))
            goto next_ati;
        /* have candidate: calculate and apply it */
        mpz_mul_ui(Z(wv_cand), wv_qq[0], ati);
        mpz_add(Z(wv_cand), Z(wv_cand), wv_o[0]);
        mpz_mul(Z(wv_cand), Z(wv_cand), *q[0]);
        if (candidate(Z(wv_cand)))
            return;
      next_ati:
        ;
    }
    if (would_fail)
        fail("TODO: walk_v.end > 2^64");
}

/* test the case where v_i has all divisors accounted for */
void walk_1(t_level *cur_level, uint vi) {
#ifdef SQONLY
    if (!cur_level->have_square)
        return;
#endif
    if (!cur_level->have_min) {
        uint min = minp[cur_level->x - 1];
        if (min)
            level_setp(cur_level, min);
        return;
    }

    {
        t_value *vip = &value[vi];
        t_allocation *aip = &vip->alloc[cur_level->vlevel[vi] - 1];
        mpz_sub_ui(Z(w1_v), aip->q, TYPE_OFFSET(vi));
    }

    if (mpz_cmp(Z(w1_v), zmin) < 0)
        return;
    ++countw;
    if (check && !cvec_testv(cx0, Z(w1_v)))
        return;

    uint t[k];
    uint need_prime[k];
    uint need_other[k];
    uint npc = 0, noc = 0;
    for (uint vj = 0; vj < k; ++vj) {
        if (vi == vj)
            continue;
        t_value *vjp = &value[vj];
        uint vjl = cur_level->vlevel[vj];
        t_allocation *ajp = &vjp->alloc[vjl - 1];
        mpz_add_ui(Z(w1_j), Z(w1_v), TYPE_OFFSET(vj));
        if (vjl > 1) {
            /* FIXME: replace this with a single initial check of
             * v_0 == rq mod aq, then use divexact */
            mpz_fdiv_qr(Z(w1_j), Z(w1_r), Z(w1_j), ajp->q);
            if (mpz_sgn(Z(w1_r)) != 0)
                return;
            mpz_gcd(Z(w1_r), Z(w1_j), ajp->q);
            if (mpz_cmp_ui(Z(w1_r), 1) != 0)
                return;
        }
        t[vj] = ajp->t;
        if (t[vj] == 1) {
            if (mpz_cmp_ui(Z(w1_j), 1) != 0)
                return;
        } else if (t[vj] == 2)
            need_prime[npc++] = vj;
        else
            need_other[noc++] = vj;
        mpz_set(wv_o[vj], Z(w1_j));
    }
    ++countwi;
    TRACK_GOOD(0, vi);
    if (!test_1primes(need_prime, npc))
        return;
    oc_t = t;
    qsort(need_other, noc, sizeof(uint), &other_comparator);
    if (!test_1multi(need_other, noc, t, walk_1_failure))
        return;
    candidate(Z(w1_v));
    return;
}

/* test a set of cases where v_i will have all divisors accounted for */
void walk_1_set(
    t_level *prev_level, t_level *cur_level,
    uint vi, ulong plow, ulong phigh, uint x
) {
#ifdef SQONLY
    if (!cur_level->have_square)
        return;
#endif
    if (!cur_level->have_min)
        plow = minp[x - 1];
    if (plow < 2)
        plow = 2;

    t_value *vip = &value[vi];
    uint vil = cur_level->vlevel[vi];
    t_allocation *aip = &vip->alloc[vil - 1];
    if (mpz_sgn(zmin) > 0) {
        mpz_add_ui(Z(temp), zmin, TYPE_OFFSET(vi));
        mpz_cdiv_q(Z(temp), Z(temp), aip->q);
        mpz_root(Z(temp), Z(temp), x - 1);
        if (!mpz_fits_ulong_p(Z(temp)))
            return;
        ulong pmin = mpz_get_ui(Z(temp));
        if (plow < pmin)
            plow = pmin - 1;
    }

    mpz_divexact(Z(w1_m), prev_level->aq, aip->q);
    bool need_mod = (mpz_cmp_ui(Z(w1_m), 1) == 0) ? 0 : 1;
    if (need_mod) {
        mpz_add_ui(Z(w1_mr), prev_level->rq, TYPE_OFFSET(vi));
        mpz_fdiv_r(Z(w1_mr), Z(w1_mr), Z(w1_m));
    }

    uint t[k];
    uint need_prime[k];
    uint need_other[k];
    uint npc = 0, noc = 0;
    for (uint vj = 0; vj < k; ++vj) {
        if (vi == vj)
            continue;
        t_value *vjp = &value[vj];
        uint vjl = cur_level->vlevel[vj];
        t_allocation *ajp = &vjp->alloc[vjl - 1];
        t[vj] = ajp->t;
        if (t[vj] == 1)
            fail("should never see multiple values with t==1");
        if (t[vj] == 2)
            need_prime[npc++] = vj;
        else
            need_other[noc++] = vj;
    }

    level_setp(cur_level, plow - 1);    /* next prime should be plow */
    while (1) {
        ulong p = prime_iterator_next(&cur_level->piter);
        if (p > phigh)
            break;
#if 0
        /* CHECKME: do we gain correctness or speed by including this
         * check that recurse() has? */
        if (p <= levels[ cur_level->level - 1 ]->maxp)
            for (uint li = 1; li < level; ++li)
                if (p == levels[li].p)
                    goto reject_this_one;
#endif
        if (need_work) {
            /* temporarily make this prime power visible to diag code */
            t_allocation *a2ip = &vip->alloc[vil];
            a2ip->p = p;
            a2ip->x = x;
            ++cur_level->vlevel[vi];
            diag_plain(cur_level);
            --cur_level->vlevel[vi];
        }
        mpz_ui_pow_ui(Z(w1_v), p, x - 1);
        if (need_mod) {
            mpz_fdiv_r(Z(temp), Z(w1_v), Z(w1_m));
            if (mpz_cmp(Z(temp), Z(w1_mr)) != 0)
                continue;
        }
        mpz_mul(Z(w1_v), Z(w1_v), aip->q);
        mpz_sub_ui(Z(w1_v), Z(w1_v), TYPE_OFFSET(vi));
        ++countw;
        if (check && !cvec_testv(cx0, Z(w1_v)))
            continue;

        for (uint vj = 0; vj < k; ++vj) {
            t_value *vjp = &value[vj];
            uint vjl = cur_level->vlevel[vj];
            t_allocation *ajp = &vjp->alloc[vjl - 1];
            mpz_add_ui(Z(w1_j), Z(w1_v), TYPE_OFFSET(vj));
            mpz_fdiv_qr(Z(w1_j), Z(w1_r), Z(w1_j), ajp->q);
            if (mpz_sgn(Z(w1_r)) != 0)
                goto reject_this_one;
            mpz_gcd(Z(w1_r), Z(w1_j), ajp->q);
            if (mpz_cmp_ui(Z(w1_r), 1) != 0)
                goto reject_this_one;
            mpz_set(wv_o[vj], Z(w1_j));
        }
        ++countwi;
        if (!test_1primes(need_prime, npc))
            goto reject_this_one;
        oc_t = t;
        qsort(need_other, noc, sizeof(uint), &other_comparator);
        if (!test_1multi(need_other, noc, t, walk_1_failure))
            goto reject_this_one;
        if (candidate(Z(w1_v)))
            return;
      reject_this_one:
        ;
    }
    return;
}

/* When some v_j is known to be of the form m.z^g, we keep a running set
 * of possible values of z: z == ((rq + i)/q_j)^{ 1/g } mod aq/q_j.
 * If no such residues exist, this returns FALSE to signal that this
 * case cannot lead to a solution.
 * For a batch allocation where we apply p^x at v_i and a secondary
 * p^x' at v_j, we call this twice: first with (j, p, x') and then
 * with (i, p, x - x'). For the second call we set retry=1.
 * This function was originally designed around the assumption that,
 * other than for the retry=1 case, p would not previously have been
 * seen; however modular fixes via -m or -c change that, requiring a
 * rethink of the logic as a whole.
 */
bool update_residues(t_level *old, t_level *new,
        uint vi, ulong p, uint x, mpz_t px, uint retry) {
    uint vj = sq0;
    t_value *vjp = &value[vj];
    uint jlevel = new->vlevel[vj] - 1;
    if (x == 0) {
        res_copy(new->level, old->level);
        return 1;
    }
    if (vi == vj) {
        /* Another allocation on our square. In the simple case, when
         * aq = aq' p^e, we must divide the known residues by
         * p^(e/g) mod aq/q_j, and if the required power g has
         * changed take roots again. Complex cases arise if -m or -c
         * options mean that p | aq', or for p=2 when p^{e+1} | aq.
         */
        uint oldg = sqg[jlevel - 1];
        uint newg = divisors[vjp->alloc[jlevel].t].gcddm;
        uint divpow = (x - 1) / oldg;
        uint source = old->level;

        /* note: if this is the secondary of a batch, new may have
         * inappropriate values for this stage */
        mpz_divexact(Z(ur_m), old->aq, vjp->alloc[jlevel - 1].q);
        /* if this prime was already represented in the modulus,
         * get a downgraded copy of the residues and rebuild */
        uint aqe = 0;
        while (mpz_fdiv_ui(Z(ur_m), p) == 0) {
            ++aqe;
            mpz_divexact_ui(Z(ur_m), Z(ur_m), p);
        }
        if (aqe) {
            t_results *rsrc = res_array(source);
            source = 0;
            t_results *rdest = res_array(source);
            resize_results(rdest, rsrc->count);
            for (uint i = 0; i < rsrc->count; ++i)
                mpz_mod(rdest->r[i], rsrc->r[i], Z(ur_m));
            rdest->count = rsrc->count;
        }
        mpz_ui_pow_ui(Z(ur_ipg), p, divpow);
        if (!mpz_invert(Z(ur_ipg), Z(ur_ipg), Z(ur_m)))
            fail("Cannot find mandatory inverse for %lu^%u", p, divpow);

        t_results *rsrc = res_array(source);
        t_results *rdest = res_array(new->level);
        resize_results(rdest, rsrc->count);
        for (uint i = 0; i < rsrc->count; ++i) {
            mpz_mul(rdest->r[i], rsrc->r[i], Z(ur_ipg));
            mpz_mod(rdest->r[i], rdest->r[i], Z(ur_m));
        }
        rdest->count = rsrc->count;

        if (p == 2) {
            /* We have residues mod p^e x, but we need them mod p^{e+1} x.
             * So we take the odd one of (r, r + m) before doubling m. */
            for (uint i = 0; i < rdest->count; ++i) {
                if (mpz_odd_p(rdest->r[i]))
                    continue;
                mpz_add(rdest->r[i], rdest->r[i], Z(ur_m));
            }
            /* update ur_m for passing to root_extract */
            if (oldg != newg)
                mpz_mul_2exp(Z(ur_m), Z(ur_m), 1);
        }

        sqg[jlevel] = newg;
        if (oldg == newg)
            return 1;

        /* we want to upgrade the roots from oldg to newg
         * It is guaranteed that oldg | newg. */
        root_extract(new->level, new->level, newg / oldg, Z(ur_m));
        if (res_array(new->level)->count == 0)
            return 0;
        return 1;
    }

    /* propagate the existing roots */
    uint g = sqg[jlevel];
    int off = (vj < vi)
        ? -(int)TYPE_OFFSET(vi - vj)
        : (int)TYPE_OFFSET(vj - vi);
    mpz_set_si(Z(ur_a), off);
    mpz_t *ppx;
    if (p == 2) {
        ++x;
        mpz_add(Z(ur_a), Z(ur_a), px);
        mpz_mul_2exp(Z(ur_ipg), px, 1);
        ppx = ZP(ur_ipg);
    } else {
        ppx = PARAM_TO_PTR(px);
    }

    /* in the non-retry case, m = old->aq * 2c(p==2) / q_j; in the retry
     * case, we need to take the previous value of q_j */
    uint mlevel = retry ? jlevel - 1 : jlevel;
    if (retry) {
        mpz_ui_pow_ui(Z(ur_m), p, retry);
        mpz_divexact(Z(ur_a), Z(ur_a), Z(ur_m));
    }
    if (!divmod(Z(ur_a), Z(ur_a), vjp->alloc[mlevel].q, *ppx))
        return 0;
    mpz_divexact(Z(ur_m), old->aq, vjp->alloc[mlevel].q);

    /* on retry, residues to update are already at new */
    uint from = retry ? new->level : old->level;

    /* we may have a modfix */
    if (have_modfix && mpz_divisible_ui_p(levels[0].aq, p)) {
        /* root_extend() needs coprime moduli to deal with, so we must
         * downgrade the input roots before calling it */
        uint fix = 0;
        mpz_set(Z(temp), levels[0].aq);
        while (mpz_fdiv_q_ui(Z(temp), Z(temp), p) == 0) {
            ++fix;
            mpz_divexact_ui(Z(ur_m), Z(ur_m), p);
        }
        if (!retry) {
            res_copy(new->level, old->level);
            from = new->level;
        }
        /* nothing more to do if we had already fixed what is asked for */
        if (fix >= x - 1)
            return 1;

        /* downgrade the roots */
        t_results *r = res_array(from);
        for (uint rc = 0; rc < r->count; ++rc)
            mpz_fdiv_r(r->r[rc], r->r[rc], Z(ur_m));
        /* deduplicate */
        qsort(r->r, r->count, sizeof(mpz_t), &_mpz_comparator);
        mpz_t *prev = NULL;
        uint rd = 0;
        for (uint rs = 0; rs < r->count; ++rs)
            if (prev == NULL || mpz_cmp(*prev, r->r[rs]) != 0) {
                prev = &r->r[rs];
                if (rs > rd)
                    mpz_set(r->r[rd], r->r[rs]);
                ++rd;
            }
        r->count = rd;
    }

    root_extend(new->level, from, Z(ur_m), Z(ur_a), g, p, x - 1, *ppx);
    if (res_array(new->level)->count == 0)
        return 0;
    return 1;
}

bool update_chinese(t_level *old, t_level *new, uint vi, mpz_t px) {
    mpz_t zarray[4];
    mpz_t *pxp = PARAM_TO_PTR(px);
    mpz_set_si(Z(uc_minusvi), -(long)TYPE_OFFSET(vi));

    /* v_0 == -i (mod 2^e) can be upgraded to v_0 = 2^e - i (mod 2^{e + 1}) */
    if (mpz_even_p(px)) {
        mpz_add(Z(uc_minusvi), Z(uc_minusvi), px);
        mpz_mul_2exp(Z(uc_px), px, 1);
        pxp = ZP(uc_px);
    }

    /* TODO: write a custom chinese() */
    memcpy(&zarray[0], old->rq, sizeof(mpz_t));
    memcpy(&zarray[1], Z(uc_minusvi), sizeof(mpz_t));
    memcpy(&zarray[2], old->aq, sizeof(mpz_t));
    memcpy(&zarray[3], *pxp, sizeof(mpz_t));
    if (chinese(new->rq, new->aq, &zarray[0], &zarray[2], 2))
        return 1;
    return 0;
}

/* Allocate p^{x-1} to v_{vi}. Returns FALSE if it is invalid.
 * Updates value[vi], and checks if this creates a new square.
 * Does not update existing square residues, see update_residues() for that.
 */
bool apply_allocv(t_level *prev_level, t_level *cur_level,
        uint vi, ulong p, uint x, mpz_t px) {
    t_value *v = &value[vi];
    uint vlevel = cur_level->vlevel[vi]++;
    t_allocation *prev = &v->alloc[vlevel - 1];
    t_allocation *cur = &v->alloc[vlevel];

    /* invalid if x does not divide remaining tau */
    if (prev->t % x)
        return 0;

    cur->p = p;
    cur->x = x;
    cur->t = prev->t / x;
    mpz_mul(cur->q, prev->q, px);

    if (highpow && ispow2(cur->t)) {
        mpz_add_ui(cur->lim, zmax, TYPE_OFFSET(vi));
        if (cur->t > 1) {
            mpz_fdiv_q(cur->lim, cur->lim, cur->q);
            mpz_root(cur->lim, cur->lim, divisors[cur->t].sumpm);
        }
    }

    /* is this newly a square? */
    if ((cur->t > 1) && (cur->t & 1) && !(prev->t & 1))
        if (!alloc_square(cur_level, vi))
            return 0;

    return 1;
}

void apply_pfreev(t_level *prev_level, t_level *cur_level, ulong p) {
    uint *pfreev = cur_level->pfreev;
    memcpy(pfreev, prev_level->pfreev, pfree_vecsize * sizeof(uint));
    if (p == 0 || p > lastprime)
        return;
    uint pi = ptoi[p];
    pfreev[pi >> 5] &= ~(1 << (pi & 0x1f));
}

/* Update level structure for the allocation of p^{x-1} to v_{vi}.
 * Does not update level.rq, level.aq: see update_chinese() for that.
 */
void apply_level(t_level *prev, t_level *cur, uint vi, ulong p, uint x) {
    cur->vi = vi;
    cur->p = p;
    cur->x = x;
    cur->have_square = prev->have_square;
    cur->nextpi = prev->nextpi;
    cur->fp_need = prev->fp_need;
    apply_pfreev(prev, cur, p);
    if (p == sprimes[cur->nextpi])
        cur->nextpi = find_nextpi(cur, cur->nextpi);
    cur->maxp = (p > prev->maxp) ? p : prev->maxp;
}

/* Apply a notional level of p^0 at v_0.
 * Also sets level.rq, level.aq and residues.
 */
void apply_null(t_level *prev, t_level *cur, ulong p) {
    apply_level(prev, cur, 0, p, 1);
    cur->have_min = prev->have_min;
    if (p == 2 && mpz_odd_p(prev->aq)) {
        if (mpz_odd_p(prev->rq))
            mpz_set(cur->rq, prev->rq);
        else
            mpz_add(cur->rq, prev->aq, prev->rq);
        mpz_mul_2exp(cur->aq, prev->aq, 1);
    } else {
        mpz_set(cur->rq, prev->rq);
        mpz_set(cur->aq, prev->aq);
    }
    if (prev->have_square)
        update_residues(prev, cur, 0, p, 0, Z(zone), 0);
}

/* Allocate a non-fixed (non-batch) prime p^{x-1} to v_{vi}. Returns FALSE
 * if it is invalid, or if no work to do.
 * Updates level and value, updates or propagates square residues.
 */
bool apply_single(t_level *prev, t_level *cur, uint vi, ulong p, uint x) {
    apply_level(prev, cur, vi, p, x);
    cur->have_min = prev->have_min || (minp[x - 1] && p > minp[x - 1]);
    mpz_ui_pow_ui(px, p, x - 1);
    if (!update_chinese(prev, cur, vi, px)) {
        ++cur->vlevel[vi];
        return 0;
    }

/* CHECKME: this appears to cost more than it saves in almost all cases */
#ifdef CHECK_OVERFLOW
    /* if rq > zmax, no solution <= zmax is possible */
    if (mpz_cmp(cur->rq, zmax) > 0) {
        /* caller expects vlevel to have been incremented on failure */
        ++cur->vlevel[vi];
        return 0;
    }
#endif

    /* this can fail only by requiring an impossible square */
    if (!apply_allocv(prev, cur, vi, p, x, px))
        return 0;

    t_value *vp = &value[vi];
    uint t = vp->alloc[ cur->vlevel[vi] - 1 ].t;
    if (t == 1) {
        walk_1(cur, vi);
        /* nothing more to do */
        return 0;
    }

    /* did we already have a square? */
    if (prev->have_square) {
        if (!update_residues(prev, cur, vi, p, x, px, 0))
            return 0;
    }
    return 1;
}

bool apply_secondary(t_level *prev, t_level *cur, uint vi, ulong p, uint x) {
    mpz_ui_pow_ui(px, p, x - 1);
    if (!apply_allocv(prev, cur, vi, p, x, px))
        return 0;
#if defined(TYPE_o)
    if (p == 2 && x == 2 && vi >= 2 && (n % 4) == 2 && cur->have_square == 1) {
        /* n_i = 2x^2 -> n_{i-2} = 2(x-1)(x+1)
         * switch to a strategy that takes advantage of this; the strategy
         * itself will revert when the conditions no longer hold.
         */
        if (strategy != STRATEGY_6X)
            prev_strategy = strategy;
        strategy = STRATEGY_6X;
    }
#endif
    return 1;
}

bool apply_primary(t_level *prev, t_level *cur, uint vi, ulong p, uint x) {
    apply_level(prev, cur, vi, p, x);
    mpz_ui_pow_ui(px, p, x - 1);
    /* this is wasted effort if x does not divide v_i.t, but we need it
     * for the alloc_square() calculation */
    if (!update_chinese(prev, cur, vi, px)) {
        ++cur->vlevel[vi];
        return 0;
    }
    if (!apply_allocv(prev, cur, vi, p, x, px))
        return 0;

    /* check if we overshot */
    if (mpz_cmp(cur->rq, zmax) > 0)
        return 0;

    return 1;
}

static inline void mint_init_state(t_level *cur_level) {
    t_mint_state *s = &mint_state;
    s->pfreev = cur_level->pfreev;
    s->pfreenext = 0;
    s->pfreedepth = 0;
}

static inline void state_extend(signed short i) {
    t_mint_state *s = &mint_state;
    uint *pv = s->pfreev;
    uint next = s->pfreenext;
    uint nextoff = next >> 5;
    uint nextbit = next & 0x1f;
    uint depth = s->pfreedepth;
    while (depth <= i) {
        assert(nextoff < pfree_vecsize);
        uint v = pv[nextoff] & ~((1 << nextbit) - 1);
        nextbit = __builtin_ffs((int)v);
        if (nextbit) {
            s->pfreei[depth] = (nextoff << 5) + (nextbit - 1);
            ++depth;
        } else {
            ++nextoff;
            nextbit = 0;
        }
    }
    s->pfreenext = (nextoff << 5) + nextbit;
    s->pfreedepth = depth;
}
static inline signed short state_pfi(signed short i) {
    t_mint_state *s = &mint_state;
    assert(i >= 0);
    if (i >= s->pfreedepth)
        state_extend(i);
    return s->pfreei[i];
}

static inline bool mintau_check_known(
    t_mint *mtp, mpz_t mint, uint depth0, uint maxdepth
) {
    t_mint_state *s = &mint_state;
    for (uint depth = depth0; mtp && depth <= maxdepth; ++depth) {
        ushort off = state_pfi(depth)
                - ((depth == depth0) ? 0 : s->pfreei[depth - 1]);
        t_mint_capped *capped = mint_capped(mtp, off, 0);
        if (capped && capped->valid && (
            depth == maxdepth || state_pfi(depth + 1) >= capped->from
        )) {
            mpz_set(mint, capped->v);
            return 1;
        }
        mtp = mint_branch(mtp, off, 0);
    }
    return 0;
}

static inline void mintau_cache_result(
    t_mint *mtp, mpz_t *mbest, uint depth0, uint maxdepth
) {
    t_mint_state *s = &mint_state;
    for (uint depth = depth0; mtp && depth <= maxdepth; ++depth) {
        ushort off = state_pfi(depth)
                - ((depth == depth0) ? 0 : s->pfreei[depth - 1]);
        signed short next = (depth < maxdepth) ? state_pfi(depth + 1) : -1;
        if (next < 0
            || !mpz_divisible_ui_p(*mbest, (ulong)sprimes[next])
        ) {
            t_mint_capped *capped = mint_capped(mtp, off, 1);
            if (!capped->valid) {
                mpz_init_set(capped->v, *mbest);
                capped->valid = 1;
            }
            capped->from = (next < 0) ? 0 : next;
            break;
        }
        mtp = mint_branch(mtp, off, 1);
    }
}

/* Calculate the minimum contribution from unused primes satisfying
 * the given tau.
 *
 * If h(n) is the highest prime dividing n, this may be called for
 * any t: t | n/h(n).
 *
 * Sets mint to the result - there is always a valid value.
 */
void mintau_r(ushort depth0, mpz_t mint, uint t) {
    if (t == 1) {
        mpz_set_ui(mint, 1);
        return;
    }

    t_divisors *dp = &divisors[t];
    t_mint_state *s = &mint_state;
    ushort maxdepth = depth0 - 1 + dp->sumpm;

    /* check if we already know this mintau */
    if (mintau_check_known(mint_base[t], mint, depth0, maxdepth))
        goto mintau_done;

    /* calculate this mintau */
    ulong p = (ulong)sprimes[state_pfi(depth0)];
    bool have_best = 0;
    mpz_t *mpx = &mint_px[depth0];  /* array protects against recursive calls */
    mpz_t *mbest = &mint_best[depth0];
    for (uint di = 0; di < dp->alldiv; ++di) {
        /* TODO: have a variant .div[] starting from .high in ascending order,
         * so that the 'd < dp->high' check is not needed, and the 'have_best
         * && best <= mpx' can lead to 'break' instead of 'continue'.
         */
        uint d = dp->div[di];
        if (d < dp->high)
            continue;
        mpz_ui_pow_ui(*mpx, p, (ulong)d - 1);
        if (have_best && mpz_cmp(*mbest, *mpx) <= 0)
            continue;
        mintau_r(depth0 + 1, mint, t / d);
        mpz_mul(mint, mint, *mpx);
        if (!have_best || mpz_cmp(*mbest, mint) > 0) {
            mpz_set(*mbest, mint);
            have_best = 1;
        }
    }
    if (debugm)
        track_mintau(*mbest, t, depth0);

    /* work out where to cache the result */
    mintau_cache_result(mint_base[t], mbest, depth0, maxdepth);
    mpz_set(mint, *mbest);
  mintau_done:
    ;
}

/* Calculate the minimum contribution from unused primes satisfying
 * the given tau.
 *
 * If h(n) is the highest prime dividing n, this may be called for
 * any t: t | n/h(n).
 *
 * Sets mint to the result - there is always a valid value.
 *
 * We only initialize the state structure once, any recursive calls
 * share it via the depth0 parameter.
 */
void mintau(t_level *cur_level, mpz_t mint, uint t) {
    if (t == 1) {
        mpz_set_ui(mint, 1);
        return;
    }
    mint_init_state(cur_level);
    mintau_r(0, mint, t);
}

/* Calculate the minimum contribution from unused primes satisfying
 * the given tau, while avoiding powers p^x: h(x) == h(r), x <= r.
 *
 * If h(n) is the highest prime dividing n, this may be called for
 * any t: t | n/h(n).
 *
 * Sets mint to the result, or to zero if no valid value.
 */
void mintau_restricted_r(ushort depth0, mpz_t mint, uint t, uint r, uint ri) {
    if (t == 1) {
        mpz_set_ui(mint, 1);
        return;
    }
    if (t % divisors[r].high)
        return mintau_r(depth0, mint, t);

    t_divisors *dp = &divisors[t];
    t_mint_state *s = &mint_state;
    ushort maxdepth = depth0 - 1 + dp->sumpm;

    /* check if we already know this mintau */
    if (mintau_check_known(mint_base_restricted[ri][t], mint, depth0, maxdepth))
        goto mintau_done;

    /* calculate this mintau */
    ulong p = (ulong)sprimes[state_pfi(depth0)];
    bool have_best = 0;
    mpz_t *mpx = &mint_px[depth0];  /* array protects against recursive calls */
    mpz_t *mbest = &mint_best[depth0];
    for (uint di = 0; di < dp->alldiv; ++di) {
        /* see also TODO in mintau_r() */
        uint d = dp->div[di];
        if (d < dp->high)
            continue;
        if (d <= r && divisors[d].high == divisors[r].high)
            continue;
        mpz_ui_pow_ui(*mpx, p, (ulong)d - 1);
        if (have_best && mpz_cmp(*mbest, *mpx) <= 0)
            continue;
        mintau_restricted_r(depth0 + 1, mint, t / d, r, ri);
        if (mpz_sgn(mint) == 0)
            continue;
        mpz_mul(mint, mint, *mpx);
        if (!have_best || mpz_cmp(*mbest, mint) > 0) {
            mpz_set(*mbest, mint);
            have_best = 1;
        }
    }
    if (!have_best)
        mpz_set_ui(*mbest, 0);
    if (debugm)
        track_mintau(*mbest, t, depth0);

    /* work out where to cache the result */
    mintau_cache_result(mint_base_restricted[ri][t], mbest, depth0, maxdepth);
    mpz_set(mint, *mbest);
  mintau_done:
    ;
}

/* Calculate the minimum contribution from unused primes satisfying
 * the given tau, while avoiding powers p^x: h(x) == h(r), x <= r.
 *
 * If h(n) is the highest prime dividing n, this may be called for
 * any t: t | n/h(n).
 *
 * Sets mint to the result, or to zero if no valid value.
 *
 * We only initialize the state structure once, any recursive calls
 * share it via the depth0 parameter.
 */
void mintau_restricted(t_level *cur_level, mpz_t mint, uint t, uint r) {
    if (t == 1) {
        mpz_set_ui(mint, 1);
        return;
    }
    uint ri = restricted_count;
    for (uint i = 0; i < restricted_count; ++i) {
        if (restricted[i] != r)
            continue;
        ri = i;
        break;
    }
    assert(ri < restricted_count);
    mint_init_state(cur_level);
    mintau_restricted_r(0, mint, t, r, ri);
}

/* order by maxp descending */
int midpp_comparator(const void *va, const void *vb) {
    t_midpp *ma = (t_midpp *)va;
    t_midpp *mb = (t_midpp *)vb;
    return mb->maxp - ma->maxp;
}

/* Populate midpp[] with the capped min and max p for each possible
 * allocation of p^{x-1} at each v_i.
 */
void prep_midp(t_level *cur_level) {
    t_level *prev_level = &levels[cur_level->level - 1];
    for (uint vi = 0; vi < k; ++vi) {
        t_value *vp = &value[vi];
        uint vil = cur_level->vlevel[vi];
        t_allocation *ap = &vp->alloc[vil - 1];
        uint t = ap->t;
        if (highpow ? t == 1 : ispow2(t))
            continue;
        t_divisors *dp = &divisors[t];
        /* try all divisors until we reach the powers of 2 */
        for (uint di = 0; di < dp->alldiv; ++di) {
            uint x = dp->div[di];
            if (highpow ? x == 1 : ispow2(x))
                break;
            if (maxp[x - 1] == 0)
                continue;
            /* find range of p for allocating p^e at v_i */
            mpz_add_ui(Z(temp), zmax, TYPE_OFFSET(vi));
            mintau(prev_level, Z(wv_cand), t / x);
            mpz_fdiv_q(Z(temp), Z(temp), Z(wv_cand));
            mpz_fdiv_q(Z(temp), Z(temp), ap->q);
            mpz_root(Z(temp), Z(temp), x - 1);

            /* our range of interest is p: midp[e] <= p < maxp[e] */
            ulong target_maxp = midp[x - 1];
            ulong target_minp = maxp[x - 1];
            if (mpz_fits_ulong_p(Z(temp))) {
                ulong target_limit = mpz_get_ui(Z(temp));
                if (!target_maxp || target_limit < target_maxp)
                    target_maxp = target_limit;
                /* if the range is empty, no entry needed for this x */
                if (target_maxp <= target_minp)
                    continue;
            } else if (!target_maxp)
                fail("prep_midp target %Zu out of range for %u:%u",
                        Z(temp), vi, x - 1);

            t_midpp *this = &midpp[midppc++];
            this->vi = vi;
            this->x = x;
            this->maxp = target_maxp;
            this->minp = target_minp;
        }
    }
    /* sort by descending maxp */
    qsort(midpp, midppc, sizeof(t_midpp), &midpp_comparator);
    return;
}

/* Try all ways of allocating p^{x-1} at v_i for any p above the selected
 * -W limit.
 */
void walk_midp(t_level *prev_level, bool recover) {
    t_level *cur_level = &levels[prev_level->level + 1];
    reset_vlevel(cur_level);

    uint vi, x, mi;
    ulong p;
    t_midpp *mp;

    in_midp = 1;
    cur_level->is_forced = 0;
    midppc = 0;
    prep_midp(cur_level);
    if (midppc == 0)
        goto walk_midp_done;

    level_setp(cur_level, midpp[0].maxp);
    /* setp has set to a prime <= target */
    prime_iterator_next(&cur_level->piter);

    if (recover) {
        p = midp_recover.p;
        x = midp_recover.x;
        vi = midp_recover.vi;

        level_setp(cur_level, p);
        mi = midppc;    /* guard */
        for (mi = 0 ; mi < midppc; ++mi) {
            mp = &midpp[mi];
            if (mp->vi == vi && mp->x == x)
                goto do_recover;
        }
        fail("midp recovery x=%u vi=%u invalid", x, vi);
    }

    while (midppc) {
        p = prime_iterator_prev(&cur_level->piter);
        for (mi = 0; mi < midppc; ++mi) {
          redo_mi:
            mp = &midpp[mi];
            /* ordered by maxp descending */
            if (p > mp->maxp)
                break;
            if (p <= mp->minp) {
                uint mj = mi + 1;
                --midppc;
                if (mi < midppc) {
                    memmove(mp, &midpp[mj], (midppc - mi) * sizeof(t_midpp));
                    goto redo_mi;
                }
                continue;
            }
            vi = mp->vi;
            x = mp->x;
          do_recover:
            if (apply_single(prev_level, cur_level, vi, p, x)) {
                if (need_work)
                    diag_plain(cur_level);
                walk_v(cur_level, Z(zero));
            }
            /* unallocate */
            --cur_level->vlevel[vi];
        }
    }
  walk_midp_done:
    in_midp = 0;
}

uint relative_valuation(uint i, ulong p, uint e) {
    uint re = simple_valuation(TYPE_OFFSET(i), p);
    if (re < e)
        return re;
    return e;
}

bool apply_batch(
    t_level *prev_level, t_level *cur_level, uint fpi, uint bi
) {
    t_forcep *fp = &forcep[fpi];
    assert(fp->count > bi);
    t_value *vp;
    cur_level->is_forced = 1;
    cur_level->bi = bi;
    t_forcebatch *bp = forcebatch_p(fp, bi);
    uint terminal = k;
    uint vi = bp->primary;

    if (bp->x[vi] == 0) {
        apply_null(prev_level, cur_level, fp->p);
        cur_level->fp_need &= ~(1 << fpi);
        return 1;
    }
    cur_level->have_min = prev_level->have_min;

    uint ep = bp->x[vi] - 1;
    if (!apply_primary(prev_level, cur_level, vi, fp->p, ep + 1))
        return 0;
    vp = &value[vi];
    if (vp->alloc[ cur_level->vlevel[vi] - 1 ].t == 1)
        terminal = vi;

    for (uint vj = 0; vj < k; ++vj) {
        if (vi == vj || bp->x[vj] == 0)
            continue;
        if (!apply_secondary(prev_level, cur_level, vj, fp->p, bp->x[vj]))
            return 0;
        vp = &value[vj];
        if (vp->alloc[ cur_level->vlevel[vj] - 1 ].t == 1)
            terminal = vj;
    }
    cur_level->fp_need &= ~(1 << fpi);

    if (terminal < k) {
        /* we have a value fully allocated, so test it unless we are
         * in a mode only to report batches.
         */
        if (opt_alloc & 4)
            return 1;
        bool valid = 1;
        if (mpz_sgn(zmin)) {
            vp = &value[terminal];
            uint vlevel = cur_level->vlevel[terminal];
            mpz_sub_ui(Z(temp), vp->alloc[vlevel - 1].q, terminal);
            if (mpz_cmp(Z(temp), zmin) <= 0)
                valid = 0;
        }
        if (valid) {
            walk_1(cur_level, terminal);
            if (seen_best)
                seen_valid = 1;
        }
        /* nothing more to do */
        return 0;
    }

    /* did we already have a square? */
    if (prev_level->have_square) {
        /* need extra care only when a secondary hits the square */
        /* so not if a) the primary hits it, or b) nothing hits it */
        if (vi == sq0 || bp->x[sq0] == 0) {
            mpz_ui_pow_ui(px, fp->p, ep);
            if (!update_residues(
                prev_level, cur_level, vi, fp->p, ep + 1, px, 0
            ))
                return 0;
        } else {
            /* apply the secondary first, then the primary */
            uint eq = bp->x[sq0] - 1;
            mpz_ui_pow_ui(px, fp->p, eq);
            if (!update_residues(
                prev_level, cur_level, sq0, fp->p, eq + 1, px, 0
            ))
                return 0;
            uint e2 = ep - eq;
            if (e2 > 0) {
                mpz_ui_pow_ui(px, fp->p, e2);
                if (!update_residues(
                    prev_level, cur_level, vi, fp->p, e2 + 1, px, eq
                ))
                    return 0;
            }
        }
    }
    if (!defer_pell && !(opt_alloc & 4) && cur_level->have_square > 1) {
        seen_valid = 1;
        walk_v(cur_level, Z(zero));
        return 0;
    }
    return 1;
}

/* A complete set of forced primes has been allocated. We may process
 * this batch or skip it, according to batch options; we also handle
 * midp ("-W") here, and skip the rest (i.e. allocation of unforced
 * primes) if midp_only.
 */
bool process_batch(t_level *cur_level) {
    uint batch_id = batch_alloc++;
    cur_batch_level = cur_level->level;
    seen_valid = 1;
    if (debugB)
        disp_batch();
    if (opt_alloc) {
        /* check if this is a batch we want to process */
        if ((opt_alloc & 4) == 0
            && opt_batch_min >= 0
            && batch_id >= opt_batch_min
            && batch_id <= opt_batch_max
        )
            goto do_process;
        if (opt_batch_min < 0)
            disp_batch();
        return 0;
    }
  do_process:
    if (need_midp) {
        walk_midp(cur_level, 0);
        if (midp_only)
            return 0;
    }
    if (cur_level->have_square > 1) {
        seen_valid = 1;
        walk_v(cur_level, Z(zero));
        return 0;
    }
    return 1;
}

uint best_v(t_level *cur_level);

/* Choose that v_i with the highest t_i still to fulfil, or (on equality)
 * with the highest q_i, but having at least one factor to allocate.
 * If there is no best entry, returns k.
 */
uint best_v0(t_level *cur_level) {
    uint vi, ti = 0;
    mpz_t *qi;

    assume(k > 0);
    for (uint vj = 0; vj < k; ++vj) {
        t_value *vpj = &value[vj];
        uint vjl = cur_level->vlevel[vj];
        t_allocation *apj = &vpj->alloc[vjl - 1];
        uint tj = apj->t;
        mpz_t *qj = &apj->q;

        /* skip if no odd prime factor */
        if (divisors[tj].high <= (highpow ? 1 : 2))
            continue;
        /* skip prime powers when capped */
        if (need_maxp && (tj & 1) && divisors[tj].alldiv == 2)
            continue;
        if (ti) {
            /* skip if not higher tau, or same tau with higher q */
            if (tj < ti)
                continue;
            if (tj == ti && mpz_cmp(*qj, *qi) <= 0)
                continue;
        }
        vi = vj;
        ti = tj;
        qi = qj;
    }
    return ti ? vi : k;
}

/* Choose that v_i with the highest prime dividing t_i still to fulfil,
 * or on equality with the highest t_i, or on equality with the highest
 * q_i.
 * If there is no best entry, returns k.
 */
uint best_v1(t_level *cur_level) {
    uint vi, ti = 0;
    mpz_t *qi;

    assume(k > 0);
    for (uint vj = 0; vj < k; ++vj) {
        t_value *vpj = &value[vj];
        uint vjl = cur_level->vlevel[vj];
        t_allocation *apj = &vpj->alloc[vjl - 1];
        uint tj = apj->t;
        mpz_t *qj = &apj->q;

        /* skip if no odd prime factor */
        if (divisors[tj].high <= (highpow ? 1 : 2))
            continue;
        /* skip prime powers when capped */
        if (need_maxp && (tj & 1) && divisors[tj].alldiv == 2)
            continue;
        if (ti) {
            uint hi = divisors[ti].high;
            uint hj = divisors[tj].high;
            if (hj < hi)
                continue;
            if (hj == hi && tj < ti)
                continue;
            if (tj == ti && mpz_cmp(*qj, *qi) <= 0)
                continue;
        }
        vi = vj;
        ti = tj;
        qi = qj;
    }
    return ti ? vi : k;
}

/* Choose that v_i with the lowest t_i still to fulfil, or (on equality)
 * with the highest q_i, but having at least one factor to allocate.
 * If there is no best entry, returns k.
 */
uint best_v2(t_level *cur_level) {
    uint vi, ti = 0;
    mpz_t *qi;

    assume(k > 0);
    for (uint vj = 0; vj < k; ++vj) {
        t_value *vpj = &value[vj];
        uint vjl = cur_level->vlevel[vj];
        t_allocation *apj = &vpj->alloc[vjl - 1];
        uint tj = apj->t;
        mpz_t *qj = &apj->q;

        /* skip if no odd prime factor */
        if (divisors[tj].high <= (highpow ? 1 : 2))
            continue;
        /* skip prime powers when capped */
        if (need_maxp && (tj & 1) && divisors[tj].alldiv == 2)
            continue;
        if (ti) {
            /* skip if not lower tau, or same tau with higher q */
            if (tj > ti)
                continue;
            if (tj == ti && mpz_cmp(*qj, *qi) <= 0)
                continue;
        }
        vi = vj;
        ti = tj;
        qi = qj;
    }
    return ti ? vi : k;
}

/* Same as best_v0, except that if the last power allocated on some v_i
 * was the square root of the remaining tau (and unforced), always take it.
 */
uint best_v3(t_level *cur_level) {
    uint vi, ti = 0;
    mpz_t *qi;

    assume(k > 0);
    for (uint vj = 0; vj < k; ++vj) {
        t_value *vpj = &value[vj];
        uint vjl = cur_level->vlevel[vj];
        t_allocation *apj = &vpj->alloc[vjl - 1];
        uint tj = apj->t;
        mpz_t *qj = &apj->q;

        /* skip if no odd prime factor */
        if (divisors[tj].high <= (highpow ? 1 : 2))
            continue;
        /* skip prime powers when capped */
        if (need_maxp && (tj & 1) && divisors[tj].alldiv == 2)
            continue;
        /* shortcircuit if single allocation of (even) sqrt(n) */
        if ((tj & 1) == 0 && apj->x == apj->t) {
            /* shortcircuit if last allocation was of sqrt(t) */
            /* but only if it was unforced */
            ulong p = apj->p;
            for (uint li = 1; li < cur_level->level; ++li) {
                t_level *lp = &levels[li];
                if (lp->is_forced == 0)
                    break;
                if (lp->p == p)
                    goto best_v3_unforced;
            }
            return vj;
          best_v3_unforced:
            ;
        }
        if (ti) {
            /* skip if not higher tau, or same tau with higher q */
            if (tj < ti)
                continue;
            if (tj == ti && mpz_cmp(*qj, *qi) <= 0)
                continue;
        }
        vi = vj;
        ti = tj;
        qi = qj;
    }
    return ti ? vi : k;
}

/* Choose that v_i with the highest prime dividing t_i still to fulfil,
 * or on equality with the highest t_i, or on equality with the highest
 * q_i. If all qualifying t_i are a power of 2, instead choose the one
 * with the smallest range.
 * If there is no best entry, returns k.
 */
uint best_v4(t_level *cur_level) {
    uint vi, ti = 0, hi;
    ulong mini;
    mpz_t *qi, *limi;

    assume(k > 0);
    for (uint vj = 0; vj < k; ++vj) {
        t_value *vpj = &value[vj];
        uint vjl = cur_level->vlevel[vj];
        t_allocation *apj = &vpj->alloc[vjl - 1];
        uint tj = apj->t;
        mpz_t *qj = &apj->q;
        mpz_t *limj = &apj->lim;
        ulong minj;

        /* skip if no odd prime factor */
        if (divisors[tj].high <= (highpow ? 1 : 2))
            continue;
        /* skip prime powers when capped */
        if (need_maxp && (tj & 1) && divisors[tj].alldiv == 2)
            continue;
        uint hj = divisors[tj].high;
        if (ti) {
            if (hj < hi)
                continue;
            if (hj == hi) {
                if (hi > 2) {
                    if (tj < ti || (tj == ti && mpz_cmp(*qj, *qi) <= 0))
                        continue;
                } else {
                    minj = ispow2(apj->x) ? apj->p : maxforce[vj];
                    if (mini > minj)
                        mpz_sub_ui(Z(temp), *limi, mini - minj);
                    else
                        mpz_add_ui(Z(temp), *limi, minj - mini);
                    if (mpz_cmp(Z(temp), *limj) <= 0)
                        continue;
                }
            }
        } else if (hj == 2) {
            minj = ispow2(apj->x) ? apj->p : maxforce[vj];
        }
        vi = vj;
        ti = tj;
        qi = qj;
        hi = divisors[ti].high;
        if (hi == 2) {
            limi = limj;
            mini = minj;
        }
    }
    return ti ? vi : k;
}

/* STRATEGY_6X: if we have ...2^{3+} . 2x^2..., the former is of the
 * form 2(x-1)(x+1), which is very restrictive.
 */
uint best_6x(t_level *cur_level) {
    /* check if we still hold */
    t_level *prev_level = &levels[ cur_level->level - 1 ];
    if (!prev_level->have_square || sq0 < 2) {
        strategy = prev_strategy;
        return best_v(cur_level);
    }

    uint vi = sq0 - 2;
    t_value *vp = &value[vi];
    uint vlevel = cur_level->vlevel[vi];
    t_allocation *ap_last = &vp->alloc[vlevel - 1];
    if (ap_last->t != 2)
        return vi;  /* allocate some more */

    /* we can fully handle this here */
    t_allocation *ap_next = &vp->alloc[vlevel], *ap;
    ap_next->t = 1;
    ap_next->p = 0; /* the real value may well not fit */
    ap_next->x = 2;
    cur_level->vlevel[vi] = vlevel + 1;
    cur_level->have_min = 1;
    mpz_fdiv_q_2exp(Z(j4q), ap_last->q, 3);

    /* we need prime p: v_0 = 8abp, bp +/- 1 == a */
    uint l2 = 0;
    for (uint i = 1; i < vlevel; ++i) {
        ap = &vp->alloc[i];
        if (ap->p == 2) {
            if (ap->x < 5)
                fail("panic: STRATEGY_6X in use but have only 2^%u assigned",
                        ap->x - 1);
            l2 = i;
            break;
        }
    }
    if (l2 == 0)
        fail("panic: STRATEGY_6X in use but no power of 2 found");
    if (vlevel > sizeof(uint) * 8 - 1)
        fail("FIXME: too many factors for STRATEGY_6X");
    /* we don't need to check the a = 0 case, since it gives Z(j4a) = 1 */
    for (uint a = (1 << vlevel) - 2; a; a -= 2) {
        mpz_set_ui(Z(j4a), 1);
        for (uint i = 1; i < vlevel; ++i) {
            if ((a & (1 << i)) == 0)
                continue;
            ap = &vp->alloc[i];
            if (ap->p == 2)
                mpz_mul_2exp(Z(j4a), Z(j4a), ap->x - 4);
            else {
                mpz_ui_pow_ui(Z(temp), ap->p, ap->x - 1);
                mpz_mul(Z(j4a), Z(j4a), Z(temp));
            }
        }
        mpz_divexact(Z(j4b), Z(j4q), Z(j4a));
        if (mpz_cmp(Z(j4a), Z(j4b)) < 0)
            continue;
        mpz_sub_ui(Z(temp), Z(j4a), 1);
        mpz_fdiv_qr(Z(j4p), Z(j4m), Z(temp), Z(j4b));
        if (mpz_cmp_ui(Z(j4m), 2) <= 0) {
            if (_GMP_is_prob_prime(Z(j4p))) {
                /* p = Z(j4p) is prime and yields v_{i+2} = 2x^2 */
                mpz_mul(ap_next->q, ap_last->q, Z(j4p));
                walk_1(cur_level, vi);
            }
            if (mpz_cmp_ui(Z(j4b), 2) <= 0) {
                mpz_add_ui(Z(j4p), Z(j4p), 2 / mpz_get_ui(Z(j4b)));
                if (_GMP_is_prob_prime(Z(j4p))) {
                    mpz_mul(ap_next->q, ap_last->q, Z(j4p));
                    walk_1(cur_level, vi);
                }
            }
        }
    }
    cur_level->vlevel[vi] = vlevel;
    return k + 1;   /* all done */
}

void set_fixed_strategy(char *s) {
    fixed_level = 0;
    char *e;
    while (*s) {
        ulong vi = strtoul(s, &e, 10);
        if (s == e)
            break;
        s = e;
        uint i = fixed_level++;
        fixed_v = realloc(fixed_v, fixed_level * sizeof(uint));
        fixed_v[i] = vi;
        if (*s == ',')
            ++s;
    }
    strategy = STRATEGY_FIXED;
    strategy_set = 1;
    highpow = 1;    /* in case this asks us to set powers of 2^x */
}

/* STRATEGY_FIXED: user-specified order, with minor sanity checks
 */
uint best_fixed(t_level *cur_level) {
    uint effective_level = cur_level->level - (cur_batch_level + 1);
    if (effective_level >= fixed_level)
        return k;
    uint vi = fixed_v[effective_level];
    t_value *vp = &value[vi];
    uint vlevel = cur_level->vlevel[vi];
    t_allocation *ap_last = &vp->alloc[vlevel - 1];
    if (ap_last->t == 1)
        return k;
    return vi;
}

/* Find the best entry to progress, using the selected strategy
 * If there is no best entry, returns k.
 */
uint best_v(t_level *cur_level) {
    return strategies[strategy](cur_level);
}

/* return the maximum prime to iterate to */
ulong limit_p(t_level *cur_level, uint vi, uint x, uint nextt) {
    t_value *vp = &value[vi];
    uint vil = cur_level->vlevel[vi];
    t_allocation *ap = &vp->alloc[vil - 1];
    mpz_add_ui(Z(lp_x), zmax, TYPE_OFFSET(vi));
    mpz_div(Z(lp_x), Z(lp_x), ap->q);

    if (ispow2(x)) {
        /* This implies highpow = true.
         * We will allocate p^{x - 1} leaving nextt = 2^b, knowing that
         * we are not divisible by any smaller p. So the contributions
         * of remaining primes will be at least p^{x - 1} . p^{b},
         * and the limit will be zmax ^ {1 / (x - 1 + b)}.
         * Usefully, divisors[nextt].highdiv gives b.
         */
        uint root = x - 1 + divisors[nextt].highdiv;
        mpz_root(Z(lp_x), Z(lp_x), root);
    } else if (x == nextt && divisors[x].high == x) {
        /* We are allocating p^{x-1} with x prime, leaving x as the
         * remaining tau; so this and the remaining allocation will
         * be of the form p^{x-1}.q^{x-1}, and we can set the limit
         * to zmax^{1/2(x-1)}.
         */
        mpz_root(Z(lp_x), Z(lp_x), 2 * (x - 1));
#if defined(TYPE_o)
    } else if (strategy == STRATEGY_6X && nextt == 2) {
        /* v_i = q_i p^{x-1} r => q_i p^{x-1} = 8ab such that br = a +/- 1,
         * so for large p we have r >= (p^{x-1} - 1)/q_i so
         * v_i > 8 p^{x-1} (p^{x-1} - 1), and we can therefore constrain
         * p to be less than 1 + root(zmax / 8, 2(x-1))
         */
        mpz_add_ui(Z(lp_x), zmax, TYPE_OFFSET(vi));
        mpz_fdiv_q_2exp(Z(lp_x), Z(lp_x), 3);
        mpz_root(Z(lp_x), Z(lp_x), 2 * (x - 1));
        mpz_add_ui(Z(lp_x), Z(lp_x), 1);
#endif
    } else if (restricted_count && divisors[x].high == divisors[nextt].high) {
        /* Let h = x.high, x = ha, then the power of the next allocation can
         * be ha (in which case it must use a higher prime than this one),
         * or hb: b > a.
         */
        t_level *prev_level = &levels[cur_level->level - 1];
        /* this is mintau using hb: b > a */
        mintau_restricted(prev_level, Z(lp_mint), nextt, x);
        bool have_value = 0;
        if (mpz_sgn(Z(lp_mint))) {
            have_value = 1;
            mpz_div(Z(lp_mint), Z(lp_x), Z(lp_mint));
        }
        uint itert = nextt, iter = 1;
        while ((itert % x) == 0) {
            ++iter;
            itert /= x;
            mintau_restricted(prev_level, Z(lp_mint2), itert, x);
            if (mpz_sgn(Z(lp_mint2))) {
                mpz_div(Z(lp_mint2), Z(lp_x), Z(lp_mint2));
                mpz_root(Z(lp_mint2), Z(lp_mint2), iter);
                if (!have_value || mpz_cmp(Z(lp_mint), Z(lp_mint2)) < 0) {
                    mpz_set(Z(lp_mint), Z(lp_mint2));
                    have_value = 1;
                }
            }
        }
        if (have_value)
            mpz_root(Z(lp_x), Z(lp_mint), x - 1);
        else
            mpz_set_ui(Z(lp_x), 0);
    } else {
        /* divide through by the minimum contribution that could supply the
         * remaining tau */
        if (nextt > 1) {
            t_level *prev_level = &levels[cur_level->level - 1];
            mintau(prev_level, Z(lp_mint), nextt);
            mpz_div(Z(lp_x), Z(lp_x), Z(lp_mint));
        }
        mpz_root(Z(lp_x), Z(lp_x), x - 1);
    }

    if (maxp[x - 1] && mpz_cmp_ui(Z(lp_x), maxp[x - 1]) > 0)
        return maxp[x - 1];
    if (!mpz_fits_ulong_p(Z(lp_x)))
        return 0;
    if (mpz_sgn(Z(lp_x)) <= 0)
        return 1;
    return mpz_get_ui(Z(lp_x));
}

typedef enum {
    PUX_NOTHING_TO_DO = 0,
    PUX_SKIP_THIS_X,
    PUX_DO_THIS_X
} e_pux;

/* returns:
 *   PUX_NOTHING_TO_DO if nothing more to do at this level for any x;
 *   PUX_SKIP_THIS_X if nothing more to do for this x;
 *   PUX_DO_THIS_X if prepped for this x with work to do.
 */
e_pux prep_unforced_x(
    t_level *prev_level, t_level *cur_level, ulong p, bool forced
) {
    uint ti = cur_level->ti;
    uint x = divisors[ti].div[cur_level->di];
    uint vi = cur_level->vi;
    t_value *vp = &value[vi];
    uint vil = cur_level->vlevel[vi];
    t_allocation *ap = &vp->alloc[vil - 1];
    ulong limp = 0;
    /* if part of an init_pattern, we don't care about the checks,
     * we will never continue from this allocation */
    if (forced)
        goto force_unforced;

    /* pick up any previous unforced x */
    uint nextt = ti / x;
    if (p == 0) {
        uint prevx = (ap->p > maxforce[vi]
#ifdef TYPE_a
            && (n % ap->p)
#endif
        ) ? ap->x : 0;
        if (ispow2(x)) {
            /* powers of 2: increasing p, not decreasing powers */
            if (prevx && ispow2(prevx))
                p = ap->p;  /* skip smaller p */
            else
                p = maxforce[vi];
        } else {
            if (x == prevx)
                p = ap->p;      /* skip smaller p, we already did the reverse */
            else if (x <= prevx && divisors[x].high == divisors[prevx].high)
                return PUX_SKIP_THIS_X; /* we already did the reverse */
            else if (x > nextt && divisors[x].high == divisors[nextt].high)
                /* skip this x, we already did any possible continuation in
                 * reverse. */
                return PUX_SKIP_THIS_X;
            else
                p = maxforce[vi];
        }
    } /* else we're continuing from known p */

    /* try p^{x-1} for all p until q_i . p^{x-1} . minrest > zmax + i */
    limp = limit_p(cur_level, vi, x, nextt);
    if (limp == 0) {
        /* force walk */
#ifdef SQONLY
        if (prev_level->have_square)
            walk_v(prev_level, Z(zero));
#else
        walk_v(prev_level, Z(zero));
#endif
        return PUX_NOTHING_TO_DO;
    } else if (limp < p)
        return PUX_SKIP_THIS_X; /* nothing to do here */
    if (nextt == 1) {
        cur_level->have_min = prev_level->have_min;
        walk_1_set(prev_level, cur_level, vi, p, limp, x);
        return PUX_SKIP_THIS_X;
    }

    /* apply gain heuristics to decide whether to walk or recurse */
    mpz_add_ui(Z(r_walk), zmax, vi);
#ifdef LARGE_MIN
    mpz_sub(Z(r_walk), Z(r_walk), zmin);
#endif
    mpz_fdiv_q(Z(r_walk), Z(r_walk), prev_level->aq);
    if (prev_level->have_square) {
        if (prev_level->have_square == 1) {
            /* if we fix a square, expect to actually walk only the g'th
             * roots of rq mod aq */
            uint sql = cur_level->vlevel[sq0];
            uint g = sqg[sql - 1];
            mpz_root(Z(r_walk), Z(r_walk), g);
            mpz_mul_ui(Z(r_walk), Z(r_walk),
                    res_array(prev_level->level)->count);
        } else {
            /* if we fix multiple squares, we'll solve a Pell equation;
             * treat that as effectively free */
            mpz_set_ui(Z(r_walk), 0);
        }
        if (gain2 > 1)
            mpz_mul_ui(Z(r_walk), Z(r_walk), gain2);
        if (antigain2 > 1)
            mpz_fdiv_q_ui(Z(r_walk), Z(r_walk), antigain2);
    } else {
        if (gain > 1)
            mpz_mul_ui(Z(r_walk), Z(r_walk), gain);
        if (antigain > 1)
            mpz_fdiv_q_ui(Z(r_walk), Z(r_walk), antigain);
    }
    uint cap = (limp_cap && limp_cap < limp) ? limp_cap : limp;
    if (mpz_fits_ulong_p(Z(r_walk))
        && mpz_get_ui(Z(r_walk)) < ((cap < p) ? 0 : cap - p)
    ) {
#ifdef SQONLY
        if (prev_level->have_square)
            walk_v(prev_level, Z(zero));
        else if (!prev_level->is_forced)
            level_setp(prev_level, prev_level->limp);
#else
        walk_v(prev_level, Z(zero));
#endif
        return PUX_NOTHING_TO_DO;
    }
  force_unforced:
    level_setp(cur_level, p);
    cur_level->x = x;
    cur_level->limp = limp;
    cur_level->max_at = seen_best;
    /* TODO: do some constant alloc stuff in advance */
    return PUX_DO_THIS_X;
}

/* Remove the specified p^e at vi in stack s (where it will be the last
 * factor at that position). Remove it also from the stack s2 if provided
 * (where it may be at any position).
 * It is a fatal error if p^e is not specified in any provided stack.
 */
void stack_remove(t_fact *s, t_fact *s2, uint vi, ulong p, uint e) {
    t_fact *rs = &s[vi];
    t_ppow *rsp = rs->count ? &rs->ppow[rs->count - 1] : NULL;
    if (!rsp || rsp->p != p || rsp->e != e)
        fail("Missing %lu^%u at %u in stack", p, e, vi);
    --rs->count;
    if (s2) {
        t_fact *rs2 = &s2[vi];
        for (uint i = 0; i < rs2->count; ++i) {
            t_ppow *rsp2 = &rs2->ppow[i];
            if (rsp2->p != p)
                continue;
            if (rsp2->e != e)
                fail("Expected %lu^%u at %u in recovery, but found %lu^%u",
                        p, e, vi, p, rsp2->e);
            if (i + 1 < rs2->count)
                memmove(rsp2, &rs2->ppow[i + 1],
                        sizeof(t_ppow) * (rs2->count - i - 1));
            --rs2->count;
            return;
        }
        fail("Expected %lu^%u at %u in recovery, but none found", p, e, vi);
    }
}

/* e_is indicates where we should pick up when we enter recurse() */
typedef enum {
    /* Current level is good, try to recurse deeper.
     * There may also be a partial walk to complete first.
     */
    IS_DEEPER = 0,
    IS_FINISH,  /* Everything is done */
    IS_NEXTX,   /* Current power is done, try the next power */
    IS_NEXT,    /* Current prime is done, try the next prime */
    IS_MIDP     /* Finish a partial midp walk before continuing */
} e_is;

/* Given an init or recovery stack, check for the specified forced prime
 * and any related batch, and apply it removing the corresponding factors
 * from the stack.
 * Returns true if we are ok to continue, or false if we reached the end
 * of the stack.
 * May update *jump to IS_NEXT if we fail to apply a found element.
 */
bool insert_forced(
    t_fact *stack, t_fact *stack2, uint fpi, e_is *jump, bool init
) {
    t_forcep *fp = &forcep[fpi];
    t_forcebatch *bp;
    uint p = fp->p;
    uint maxx = 0, mini;
    bool more = 0;
    /* find highest power of this prime */
    for (uint vi = 0; vi < k; ++vi) {
        t_fact *rs = &stack[vi];
        if (rs->count) {
            if (rs->ppow[rs->count - 1].p == p) {
                uint x = rs->ppow[rs->count - 1].e + 1;
                if (maxx < x) {
                    maxx = x;
                    mini = vi;
                }
                if (rs->count > 1)
                    more = 1;
            } else
                more = 1;
        }
    }
    /* find the batch */
    uint bi;
    if (maxx == 0) {
        /* do not apply tail for prime missing in init pattern */
        if (init)
            return more ? 1 : 0;
        bi = fp->count - 1;
        bp = forcebatch_p(fp, bi);
        if (more && has_tail(fp))
            goto have_batch;
#if defined(TYPE_a)
        if (bp->primary == 0) {
            mini = 0;
            goto have_batch;
        }
#endif
        /* either the previous forced prime was the last thing that is
         * specified, or this forced prime is invalidly missing */
        return 0;
    }

    for (bi = 0; bi < fp->count; ++bi) {
        bp = forcebatch_p(fp, bi);
        if (bp->primary == mini && bp->x[bp->primary] == maxx)
            break;
    }
    if (bi >= fp->count) {
        if (!has_tail(fp))
            fail("521 no batch found for %u^{%u-1} at v_%u", p, maxx, mini);
        /* the power present doesn't match a batch, so it must be a floating
         * prime on the tail */
        bi = fp->count - 1;
        bp = forcebatch_p(fp, bi);
        maxx = 0;
    }

  have_batch: ;
    if (!init || !is_tail(bp)) {
        t_level *prev_level = &levels[level - 1];
        t_level *cur_level = &levels[level];
        reset_vlevel(cur_level);
        /* progress is shown just before we apply, so on recovery it is
         * legitimate for the last one to fail */
        if (apply_batch(prev_level, cur_level, fpi, bi))
            ++level;
        else
            *jump = IS_NEXT;
        cur_batch_level = level;    /* from process_batch */
    }

    /* remove from stack */
    if (maxx) {
        stack_remove(stack, stack2, mini, p, maxx - 1);
        for (uint j = 1; j <= mini; ++j) {
            uint vj = mini - j;
            uint e = relative_valuation(j, p, maxx - 1);
            if (e)
                stack_remove(stack, stack2, vj, p, e);
        }
        for (uint j = 1; mini + j < k; ++j) {
            uint vj = mini + j;
            uint e = relative_valuation(j, p, maxx - 1);
            if (e)
                stack_remove(stack, stack2, vj, p, e);
        }
    }
    return 1;
}

/* Given an init or recovery stack, check for a floating prime to insert
 * at the specified position, and apply it removing the corresponding factor
 * from the stack.
 * Returns true if we are ok to continue, or false if no further inserts
 * should be done.
 * May update *jump if we fail to apply a found element to the appropriate
 * selection of IS_NEXTX or IS_NEXT.
 */
static inline bool insert_float(
    t_fact *stack, t_fact *stack2, uint vi, e_is *jump, bool init
) {
    t_fact *rs = &stack[vi];
    if (rs->count == 0)
        return 0;
    t_ppow *rsp = &rs->ppow[rs->count - 1];
    ulong p = rsp->p;
    uint x = rsp->e + 1;
    stack_remove(stack, stack2, vi, p, x - 1);

    t_level *prev_level = &levels[level - 1];
    t_level *cur_level = &levels[level];
    reset_vlevel(cur_level);

    t_value *vp = &value[vi];
    uint vil = cur_level->vlevel[vi];
    uint ti = vp->alloc[vil - 1].t;
    t_divisors *dp = &divisors[ti];
    if (!init && dp->high <= (highpow ? 1 : 2))
        fail("tried to insert %lu^%u at %u, but nothing to do there",
                p, x, vi);

    uint di;
    uint high = init ? dp->alldiv : dp->highdiv;
    for (di = 0; di <= high; ++di) {
        if (di == high)
            fail("522 x=%u is not a highdiv of t=%u\n", x, ti);
        if (dp->div[di] == x)
            break;
    }
    cur_level->vi = vi;
    cur_level->ti = ti;
    cur_level->di = di;

    e_pux pux = prep_unforced_x(prev_level, cur_level, p, init);
    switch (pux) {
      case PUX_SKIP_THIS_X:
        if (ti == x) {
            /* legitimate skip after walk_1_set */
            *jump = IS_NEXTX;
            return 0;
        }
        fail("prep_nextt %u for %lu^%u at %u\n", pux, p, x, vi);
      case PUX_NOTHING_TO_DO:
        /* we have now acted on this */
        *jump = IS_NEXT;
        return 0;
    }

    level_setp(cur_level, p);
    /* progress is shown just before we apply, so on recovery it is
     * legitimate for the last one to fail */
    if (!apply_single(prev_level, cur_level, vi, p, x)) {
        --cur_level->vlevel[cur_level->vi];
        *jump = IS_NEXT;
        return 0;
    }
    ++level;
    return 1;
}

/* On recovery, set up the recursion stack to the point we had reached.
 * Returns IS_DEEPER if we should continue by recursing deeper from this
 * point; returns IS_NEXTX if we should continue by advancing the power
 * applied at the current position; returns IS_NEXT if we should continue
 * by advancing the current level; and returns IS_MIDP if we should continue
 * via walk_midp(). If the entire run is already complete, returns IS_FINISH.
 */
e_is insert_stack(void) {
    e_is jump = IS_DEEPER;

    if (istack) {
        /* insert any init forced primes */
        for (uint fpi = 0; fpi < forcedp; ++fpi)
            insert_forced(istack, rstack, fpi, &jump, 1);

        /* insert anything else */
        for (uint vi = 0; vi < k; ++vi) {
            t_fact *rs = &istack[vi];
            while (rs->count) {
                if (insert_float(istack, rstack, vi, &jump, 1))
                    continue;
                /* failure should mean that there is nothing more to do */
                if (jump == IS_DEEPER)
                    fail("panic: init_pattern complete, but going deeper");
                return IS_FINISH;
            }
        }

        for (uint l = final_level + 1; l < level; ++l)
            levels[l].is_forced = 1;
        /* do not recurse back into elements set by init_pattern */
        final_level = level - 1;
    }

    if (rstack) {
        /* insert recovery forced primes */
        for (uint fpi = 0; fpi < forcedp; ++fpi) {
            /* skip if already inserted via init pattern */
            if ((levels[level - 1].fp_need & (1 << fpi)) == 0)
                continue;
            if (!insert_forced(rstack, NULL, fpi, &jump, 0))
                goto insert_check;
        }

        /* insert the rest, in strategy-allocated order */
        while (1) {
            uint vi = best_v(&levels[level - 1]);
            if (vi >= k)
                break;
            if (!insert_float(rstack, NULL, vi, &jump, 0))
                break;
        }

      insert_check:
        /* check we have them all */
        for (uint vi = 0; vi < k; ++vi) {
            t_fact *rs = &rstack[vi];
            uint c = rs->count;
            while (c) {
                t_ppow pp = rs->ppow[--c];
                fail("failed to inject %lu^%u at v_%u", pp.p, pp.e, vi);
            }
        }
    }

    if (need_midp && midp_recover.valid) {
        if (jump != IS_DEEPER)
            fail("data mismatch");
        jump = IS_MIDP;
    }
    return jump;
}

/* we emulate recursive calls via the levels[] array */
void recurse(e_is jump_continue) {
    ulong p;
    uint x, bi;
    t_level *prev_level = &levels[level - 1];
    t_level *cur_level = &levels[level];
    reset_vlevel(cur_level);
    t_forcep *fp;

    if (jump_continue == IS_NEXT)
        goto continue_recurse;
    else if (jump_continue == IS_NEXTX)
        goto continue_unforced_x;
    else if (jump_continue == IS_MIDP) {
        /* (FIXME) discard any partial walk */
        have_rwalk = 0;
        /* finish the walk_midp call with midp_recover */
        walk_midp(prev_level, 1);
        /* then continue as main code would have, after process_batch() */
        if (midp_only) {
            /* process_batch() returns false in this case */
            if (level - 1 < forcedp)
                goto derecurse;
            reset_vlevel(cur_level);
            goto continue_recurse;
        }
        if (level - 1 < forcedp)
            goto unforced;
        /* else go deeper */
    }
    /* else jump_continue == IS_DEEPER */

    if (have_rwalk) {
        walk_v(prev_level, rwalk_from);
        goto derecurse;
    }
    /* if we just completed a batch, must have a chance to trigger midp */
    if (need_midp && prev_level->is_forced && !prev_level->fp_need
            && !process_batch(prev_level))
        goto derecurse;

    while (1) {
        ++countr;
        prev_level = &levels[level - 1];
        cur_level = &levels[level];

        /* recurse deeper */
        if (prev_level->fp_need && prev_level->is_forced) {
            fp = &forcep[next_fpi(prev_level)];
            if (fp->count == 0)
                goto unforced;
            bi = 0;
            goto continue_forced;
        }
      unforced:
        {
            /* note: cur_level->is_forced is either always 0 by calloc(),
             * or gets set to 0 on the tail of a batch */
            /* cur_level->is_forced = 0; */

            if (cur_level->next_best)
                goto walk_now;
            uint vi = best_v(cur_level);
            if (vi >= k) {
                /* signal that best_v() already handled it */
                if (vi > k)
                    goto derecurse;

                /* failure result is stable if last allocation was unforced */
                if (!prev_level->is_forced)
                    cur_level->next_best = 1;
              walk_now:
#ifdef SQONLY
                if (prev_level->have_square)
                    walk_v(prev_level, Z(zero));
                else if (!prev_level->is_forced)
                    level_setp(prev_level, prev_level->limp);
#else
                walk_v(prev_level, Z(zero));
#endif
                goto derecurse;
            }
            t_value *vp = &value[vi];
            uint vil = cur_level->vlevel[vi];
            uint ti = vp->alloc[vil - 1].t;
            t_divisors *dp = &divisors[ti];
            if (dp->high <= (highpow ? 1 : 2))
                fail("best_v() returned %u, but nothing to do there", vi);
            cur_level->vi = vi;
            cur_level->ti = ti;
            cur_level->di = 0;
            goto have_unforced_x;
        }
      continue_unforced_x:
        ++cur_level->di;
      have_unforced_x:
        {
            if (cur_level->di >= divisors[cur_level->ti].highdiv)
                goto derecurse;
            switch (prep_unforced_x(prev_level, cur_level, 0, 0)) {
                case PUX_NOTHING_TO_DO:
                    goto derecurse;
                case PUX_SKIP_THIS_X:
                    goto continue_unforced_x;
                case PUX_DO_THIS_X:
                    ;
            }
            goto continue_unforced;
        }
        break;
      /* entry point, must set prev_level/cur_level before using */
      derecurse:
        levels[level + 1].next_best = 0;
        --level;
        if (level <= final_level)
            break;
        prev_level = &levels[level - 1];
        cur_level = &levels[level];
        if (cur_level->is_forced)
            reset_vlevel(cur_level);    /* unapply the batch */
        else
            --cur_level->vlevel[cur_level->vi];
        /* goto continue_recurse; */
      continue_recurse:
        if (cur_level->is_forced) {
            fp = &forcep[next_fpi(prev_level)];
            bi = cur_level->bi + 1;
          continue_forced:
            if (bi >= fp->count)
                goto derecurse;
            /* If apply succeeds, continue if the batch is still partial,
             * or if it is complete and we are ok to process it. Note that
             * process_batch directly invokes walk_midp() under -W.
             */
            if (apply_batch(prev_level, cur_level, next_fpi(prev_level), bi)
                && (cur_level->fp_need || process_batch(cur_level))
            ) {
                if (need_work)
                    diag_plain(cur_level);
                ++level;
                reset_vlevel(&levels[level]);
                continue;
            }
            /* unapply a possible partial batch */
            reset_vlevel(cur_level);
            goto continue_recurse;
        }
      continue_unforced:
        {
            /* recalculate limit if we have an improved maximum */
            if (improve_max && seen_best > cur_level->max_at)
                switch (prep_unforced_x(
                    prev_level, cur_level, cur_level->p, 0
                )) {
                  case PUX_NOTHING_TO_DO:
                  case PUX_SKIP_THIS_X:
                    goto continue_unforced_x;
                }
            /* note: only valid to use from just below here */
          redo_unforced: ;
            ulong p = prime_iterator_next(&cur_level->piter);
            if (p > cur_level->limp)
                goto continue_unforced_x;
            if (p <= prev_level->maxp)
                for (uint li = 1; li < level; ++li)
                    if (p == levels[li].p)
                        goto redo_unforced;
            /* note: this returns 0 if t=1 */
            if (!apply_single(prev_level, cur_level, cur_level->vi, p, cur_level->x)) {
                if (need_work)
                    diag_plain(cur_level);
                --cur_level->vlevel[cur_level->vi];
                /* not redo_unforced, we may have improved zmax */
                goto continue_unforced;
            }
            if (need_work)
                diag_plain(cur_level);
            ++level;
            reset_vlevel(&levels[level]);
            continue;   /* deeper */
        }
    }
}

int main(int argc, char **argv, char **envp) {
    int i = 1;
#ifdef HAVE_SETPROCTITLE
    setproctitle_init(argc, argv, envp);
#endif
    init_pre();
    while (i < argc && argv[i][0] == '-') {
        char *arg = argv[i++];
        if (arg[1] == '-')
            break;
        if (arg[1] == 'x')
            set_minmax(&arg[2]);
        else if (arg[1] == 'X')
            improve_max = 0;
        else if (arg[1] == 'g')
            set_gain(&arg[2]);
        else if (arg[1] == 'G')
            set_gain2(&arg[2]);
        else if (arg[1] == 'p')
            set_cap(&arg[2]);
        else if (arg[1] == 'P')
            limp_cap = strtoul(&arg[2], NULL, 10);
        else if (arg[1] == 'W') {
            need_midp = 1;
            char *w = &arg[2];
            if (*w == 'W') {
                midp_only = 1;
                ++w;
            }
            if (*w == 'x')
                smidpx = w + 1;
            else
                smidp = w;
        } else if (strncmp("-Ls", arg, 3) == 0)
            diag_delay = strtoul(&arg[3], NULL, 10);
        else if (strncmp("-Lf", arg, 3) == 0)
            log_delay = strtoul(&arg[3], NULL, 10);
        else if (strncmp("-Ld", arg, 3) == 0)
            death_delay = strtoul(&arg[3], NULL, 10);
        else if (arg[1] == 'r') {
            rpath = malloc(strlen(&arg[2]) + 1);
            strcpy(rpath, &arg[2]);
        } else if (arg[1] == 'R')
            skip_recover = 1;
        else if (arg[1] == 'I')
            init_pattern = &arg[2];
        else if (arg[1] == 'f')
            force_all = strtoul(&arg[2], NULL, 10);
        else if (arg[1] == 'F') {
            unforce_all = strtoul(&arg[2], NULL, 10);
            if (unforce_all == 0)
                unforce_all = 1;
        } else if (arg[1] == 'm')
            set_modfix(&arg[2]);
        else if (arg[1] == 's')
            randseed = strtoul(&arg[2], NULL, 10);
        else if (arg[1] == 'h')
            rough = strtoul(&arg[2], NULL, 10);
        else if (arg[1] == 'a') {
            if (arg[2])
                opt_alloc = strtoul(&arg[2], NULL, 10);
            else
                opt_alloc = 1;
        } else if (arg[1] == 'b')
            set_batch(&arg[2]);
        else if (arg[1] == 'o') {
            opt_print = 1;
            if (arg[2])
                opt_flake = strtoul(&arg[2], NULL, 10);
        } else if (arg[1] == 'c') {
            if (arg[2] == 'p')
                check_prime = strtoul(&arg[3], NULL, 10);
            else if (arg[2] == 'r')
                check_ratio = strtod(&arg[3], NULL);
            else if (arg[2] == 'c')
                check_chunk = strtoul(&arg[3], NULL, 10);
            else
                check = strtoul(&arg[2], NULL, 10);
        }
        else if (arg[1] == 'd') {
            switch (arg[2]) {
              case 0: {
                /* legacy: once for dw, twice for dW */
                if (debugw)
                    debugW = 1;
                else
                    debugw = 1;
              }
              case 'w':
                debugw = 1;
                debugw_count = strtoul(&arg[3], NULL, 10);
                break;
              case 'W':
                debugw = 1;
                debugW = 1;
                debugw_count = strtoul(&arg[3], NULL, 10);
                break;
              case 'b':
                debugb = 1;
                break;
              case 'B':
                debugb = 1;
                debugB = 1;
                break;
              case 'f':
                debugf = 1;
                break;
              case 'x':
                debugx = 1;
                break;
              case 't':
                debugt = 1;
                break;
              case 'v':
                debugv = 1;
                break;
              case 'V':
                debugV = 1;
                debugv = 1;
                break;
              case 'm':
                debugm = 1;
              case 'l':
                log_full = 1;
                break;
              default:
                fail("Unknown debug option '%s'", arg);
            }
        } else if (arg[1] == 'v')
            vt100 = 1;
        else if (arg[1] == 'j') {
            if (arg[2] == 'p')
                defer_pell = 1;
            else if (arg[2] == 's') {
                set_fixed_strategy(&arg[3]);
            } else {
                strategy = strtoul(&arg[2], NULL, 10);
                if (strategy >= NUM_STRATEGIES)
                    fail("Invalid strategy %u", strategy);
                strategy_set = 1;
                if (strategy == 4)
                    highpow = 1;
            }
        } else if (arg[1] == 'y') {
            if (arg[2] != typename())
                fail("Invalid type option '%s'", arg);
            /* else ok */
        } else
            fail("unknown option '%s'", arg);
    }
    if (i + 2 == argc) {
        n = strtoul(argv[i++], NULL, 10);
        if (n < 1)
            fail("require n >= 1, not %lu", n);
        k = strtoul(argv[i++], NULL, 10);
        if (k < 1)
            fail("require k >= 1, not %lu", k);
    } else
        fail("wrong number of arguments");
    if (force_all > k)
        fail("require force_all <= k");

    init_post();
    if (opt_alloc & 2)
        diag_csv_head();
    else {
        report_init(stdout, argv[0]);
        if (rfp) report_init(rfp, argv[0]);
    }

    if (check || modfix) {
        uint *tt = calloc(k, sizeof(uint));
        for (uint i = 0; i < k; ++i)
            tt[i] = target_t(i);
        cx0 = cvec_init(n, k, &zmin, tt);

        for (uint mfi = 0; mfi < modfix_count; ++mfi) {
            t_modfix *mfp = &modfix[mfi];
            apply_modfix(cx0, mfp->mod, mfp->val, mfp->negate, check);
        }

        t_fact f;
        init_fact(&f);
        for (uint m = 2; m <= check; ++m) {
            f.count = 0;
            simple_fact(m, &f);
            if (check_prime && f.ppow[f.count - 1].p > check_prime)
                continue;
            apply_m(cx0, m, &f);
        }
        free_fact(&f);
        cvec_pack(cx0, check_chunk ? check_chunk : check, check_ratio);
        free(tt);

        cvec_mult(cx0, &levels[0].rq, &levels[0].aq);
        if (mpz_cmp_ui(levels[0].aq, 1) > 0)
            have_modfix = 1;
        done_modfix();
        if (!check)
            check = 1;
    }
    prep_presquare();

    e_is jump = IS_DEEPER;
    if (rstack || istack)
        jump = insert_stack();
    if (jump != IS_FINISH)
        recurse(jump);
    keep_diag();

    if ((opt_alloc & 2) == 0) {
        double tz = utime();
        report("367 c%cul(%u, %u): recurse %lu, walk %lu, walkc %lu (%.2fs)",
                typename(), n, k, countr, countw, countwi, seconds(tz));
#ifdef TRACK_STATS
        report(" [");
        for (uint i = 0; i < k; ++i) {
            if (i)
                report(" ");
            report("%lu", count_bad[i]);
        }
        report("]\n");
#else
        report("\n");
#endif
        if (!seen_valid && !seen_best)
            report("406 Error: no valid arrangement of powers\n");
        else if (log_full)
            report_prefinal(tz);
        if (seen_best)
            report("200 f(%u, %u) = %Zu (%.2fs)\n", n, k, best, seconds(tz));
    }
    done();
    return 0;
}
