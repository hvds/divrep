#include "ptypes.h"

#include "coul.h"
#include "coultau.h"
#include "coulfact.h"
#include "trace.h"
#include "factor.h"
#include "gmp_main.h"
#include "primality.h"
#include "utility.h"
#include "squfof126.h"
#include "ecm.h"
#ifdef MPUG_SIQS
#   include "siqs.h"
#else
#   include "pbrent63.h"
#   include "tinyqs.h"
#   include "simpqs.h"
#endif

#include <time.h>
#include <string.h>
#include <errno.h>
#include <math.h>

t_tm *taum = NULL;
uint taum_alloc = 0;
uint taum_size;
uint test_rough = 0;
mpz_t tmf, tmf2, tmp_lim;
#ifndef MPUG_SIQS
#define SIMPQS_SIZE 66
mpz_t simpqs_array[SIMPQS_SIZE];
#endif

/* B2 < B1 gives the default stage 2 bound */
#ifdef MPUG_SIQS
/* as in MPUG's factor(), each call takes fresh curves from MPUG's ISAAC */
#define _GMP_ECM_FACTOR(n, f, b1, b2, ncurves) \
     _GMP_ecm_factor_projective(n, f, b1, b2, ncurves, \
            irand_u64(), get_verbose_level())
#else
#define _GMP_ECM_FACTOR(n, f, b1, b2, ncurves) \
     _GMP_ecm_factor_projective(n, f, b1, b2, ncurves)
#endif

/* Avoid CLOCK_PROCESS_CPUTIME_ID, which is ratcheted by 300Hz scheduler
 * ticks once coul.c:init_time() has armed its timers.
 */
#define CG_CLOCK CLOCK_THREAD_CPUTIME_ID
struct timespec cg_tp0;
struct timespec cg_tp1;
#ifdef VERBOSE
uint verbose = 0;   /* -dv<bits>, see trace.h */
#endif
#define GIG 1000000000
static inline ulong cgdiff(struct timespec *t0) {
    clock_gettime(CG_CLOCK, &cg_tp1);
    return (cg_tp1.tv_sec - t0->tv_sec) * GIG
            + cg_tp1.tv_nsec - t0->tv_nsec;
}
#ifdef VERBOSE
#define dz(format, ...) do { \
    if (VB(VB_TRACE)) \
        gmp_printf("(%ld) " format "\n", cgdiff(&cg_tp0), ## __VA_ARGS__); \
} while (0)
#else
#define dz(...) 1
#endif

/* Primality: a value of a single limb is tested in single limbs, with
 * the same result (see bpsw_u64(), pretest_u64()).
 */
static inline bool ct_isprime(mpz_t n) {
    return (mpz_size(n) <= 1) ? bpsw_u64(mpz_get_ui(n))
            : _GMP_is_prob_prime(n) != 0;
}
static inline bool ct_isbpsw(mpz_t n) {
    return (mpz_size(n) <= 1) ? bpsw_u64(mpz_get_ui(n)) : _GMP_BPSW(n) != 0;
}
static inline uint ct_ispretest(mpz_t n) {
    return (mpz_size(n) <= 1) ? pretest_u64(mpz_get_ui(n))
            : primality_pretest(n);
}

#ifdef VERBOSE
static inline bool ct_prime(mpz_t n) {
    if (!VB(VB_TRACE))
        return ct_isprime(n);
    clock_gettime(CG_CLOCK, &cg_tp0);
    bool r = ct_isprime(n);
    gmp_printf("(%ld) p: %Zd %u\n", cgdiff(&cg_tp0), n, r ? 1 : 0);
    return r;
}
static inline ulong ct_power(mpz_t n) {
    if (!VB(VB_TRACE))
        return power_factor(n, n);
    clock_gettime(CG_CLOCK, &cg_tp0);
    ulong r = power_factor(n, n);
    gmp_printf("(%ld) pow: %Zd^%lu\n", cgdiff(&cg_tp0), n, r);
    return r;
}
static inline int ct_pretest(mpz_t n) {
    if (!VB(VB_TRACE))
        return ct_ispretest(n);
    clock_gettime(CG_CLOCK, &cg_tp0);
    int r = ct_ispretest(n);
    gmp_printf("(%ld) pretest: %Zd %d\n", cgdiff(&cg_tp0), n, r);
    return r;
}
static inline bool ct_bpsw(mpz_t n) {
    if (!VB(VB_TRACE))
        return ct_isbpsw(n);
    bool r = ct_isbpsw(n);
    gmp_printf("(%ld) bpsw: %Zd %u\n", cgdiff(&cg_tp0), n, r ? 1 : 0);
    return r;
}
extern int fs_trial(factor_state* fs);
static inline bool ct_trial(factor_state *fs) {
    if (!VB(VB_TRACE))
        return fs_trial(fs);
    clock_gettime(CG_CLOCK, &cg_tp0);
    bool r = fs_trial(fs);
    gmp_printf("(%ld) div: %Zu %d", cgdiff(&cg_tp0), fs->n, r);
    if (r)
        gmp_printf(" %Zu", fs->f);
    gmp_printf("\n");
    return r;
}
#else
#   define ct_prime(n) ct_isprime(n)
#   define ct_power(n) power_factor(n, n)
#   define ct_trial(fs) fs_trial(fs)
#   define ct_pretest(n) ct_ispretest(n)
#   define ct_bpsw(n) ct_isbpsw(n)
#endif

#define NPRIMES_SMALL 6500
/* MPUG declares this static, so we must copy it */
static unsigned short primes_small[NPRIMES_SMALL];

#ifdef MPUG_054
/* GCD-batched trial division: each batch can rule out divisibility by
 * a batch of primes with a single gcd test against a precomputed product.
 */
#   define TRIAL_BAND_A_END 169     /* primes 3 to 997 */
#   define TRIAL_BAND_B_END 551     /* next to 3989 */
#   define TRIAL_BAND_C_END 1863    /* next to 15991 */
#   define TRIAL_BAND_D_END 3433    /* next to 31991 */
#   define TRIAL_BAND_E_END 6414    /* next to 63997 */
#   define TRIAL_BAND_FEW 64        /* scan fewer than this without a gcd */
static mpz_t gcd_1k, gcd_4k, gcd_16k, gcd_32k, gcd_64k, gcd_scratch;

/* Set *band_end and *gcdp to the next band iff sp lies exactly on a band
 * boundary.
 */
static inline bool next_trial_band(UV sp, UV *band_end, mpz_t **gcdp) {
    if (sp == 2) {
        *band_end = TRIAL_BAND_A_END;
        *gcdp = &gcd_1k;
    } else if (sp == TRIAL_BAND_A_END) {
        *band_end = TRIAL_BAND_B_END;
        *gcdp = &gcd_4k;
    } else if (sp == TRIAL_BAND_B_END) {
        *band_end = TRIAL_BAND_C_END;
        *gcdp = &gcd_16k;
    } else if (sp == TRIAL_BAND_C_END) {
        *band_end = TRIAL_BAND_D_END;
        *gcdp = &gcd_32k;
    } else if (sp == TRIAL_BAND_D_END) {
        *band_end = TRIAL_BAND_E_END;
        *gcdp = &gcd_64k;
    } else {
        return 0;
    }
    return 1;
}

/* Skip as many whole bands as possible from sp, returning the new sp.
 * A band is skipped when its GCD with n is 1, which is tested whenever
 * at least TRIAL_BAND_FEW of its primes are within sqrt(lim), even if
 * the band extends beyond it: then none of the primes still needed divide
 * n, and trial division ends as soon as it resumes past the band.
 * iter is optional: when given, it's kept in sync with the new sp.
 */
static inline UV skip_trial_bands(
    UV sp, mpz_t n, UV lim, prime_iterator *iter
) {
    while (1) {
        UV band_end;
        mpz_t *gcdp;
        if (!next_trial_band(sp, &band_end, &gcdp))
            break;
        /* The band's gcd is worthwhile even if the band extends beyond
         * sqrt(lim), unless only a few of its primes are needed; if the
         * gcd is 1, none of them divide n. */
        UV few = sp + TRIAL_BAND_FEW;
        if (few < band_end && (UV)primes_small[few] * primes_small[few] > lim)
            break;
        mpz_gcd(gcd_scratch, n, *gcdp);
        if (mpz_cmp_ui(gcd_scratch, 1) != 0)
            break;
        sp = band_end;
        if (iter)
            prime_iterator_setprime(iter, primes_small[sp - 1]);
    }
    return sp;
}
#endif

/* The factoring ladder: the methods tau_multi_run() and factor_one() try
 * in turn on a value with no factor below the trial division limit, in
 * the order of MPUG's factor() of the time, each with its parameters;
 * from MPUGMP 32fcf54782, those of factor_pretests[] then factor_ladder[]
 * in its factor.c, after tinyecm64 for values of up to 64 bits.
 * Each rung applies to values of minbits to maxbits bits (maxbits 0 for
 * no limit); a value is the cofactor being factored when a rung is
 * tried, so that a rung's size limits and parameters are found from the
 * value being tested at the time.
 * Rungs before TM_INIT are unused, so that a rung's index is its bit in
 * the bitsets of rungs to try (tmfbl[], t_tm.bits).
 */
typedef enum {
    RM_NONE = 0,    /* unused */
    RM_BRENT63,     /* pbrent63 with arg1 rounds */
    RM_SQUFOF,      /* squfof126 with arg1 rounds */
    RM_TINYQS,      /* tinyqs */
    RM_PM1,         /* p-1 with B1 = arg1, B2 = arg2 */
    RM_ECM,         /* ECM with B1 = arg1, arg2 curves */
    RM_ECM_SCALED,  /* ECM with B1 = arg1 * rung_ecm_b1(), arg2 curves */
    RM_QS,          /* quadratic sieve, see do_qs() */
    RM_PBRENT,      /* Pollard-Brent rho with a = arg1, arg2 rounds */
    RM_HOLF,        /* Hart's one line factorization, arg1 rounds */
    RM_CHEB,        /* Chebyshev method with B = arg1, x0 = arg2 */
    RM_TINYECM,     /* tinyecm64 */
    RM_EARLY_PM1,   /* p-1 with bounds by size, see rung_try() */
    RM_ECM_PRE,     /* ECM with B1 = arg1, arg2 curves, B2 by size */

    RM_MAX
} e_rung_method;

typedef struct s_rung {
    uint minbits;
    uint maxbits;
    e_rung_method method;
    ulong arg1;
    ulong arg2;
    uint flags;
} t_rung;
#define RF_LAST 1   /* last resort: tried only under TRY_HARDER */
#define RF_054 2    /* tried only from MPUGMP v0.54 */
#define RF_ONCE 4   /* after a miss, not tried on any cofactor */

static const t_rung rungs[] = {
    { 0, 0, RM_NONE }, { 0, 0, RM_NONE },
#ifdef MPUG_SIQS
    /* As in factor(), QS is tried at most once on a value: each of its
     * rungs applies only to sizes above the previous one's limit.
     */
    /* minbits maxbits method           arg1       arg2  flags */
    {    0,   64, RM_TINYECM,             0,         0 },
    /* factor_pretests[] */
    {   88,    0, RM_EARLY_PM1,           0,         0, RF_ONCE },
    {  128,    0, RM_ECM_PRE,           200,         4 },
    {  160,    0, RM_ECM_PRE,           600,         4 },
    {  176,    0, RM_ECM_PRE,           600,        12 },
    {  192,    0, RM_ECM_PRE,          2000,        10 },
    {  208,    0, RM_PM1,            200000,   3000000 },
    {  208,    0, RM_ECM_PRE,         20000,         2 },
    {  240,    0, RM_ECM_PRE,         30000,        20 },
    {  256,    0, RM_ECM_PRE,         40000,        40 },
    {  270,    0, RM_ECM_PRE,         80000,        40 },
    {  288,    0, RM_ECM_PRE,        160000,        80 },
    /* factor_ladder[] */
    {    0,  320, RM_QS,                  0,         0 },
    {    0,    0, RM_ECM_SCALED,          2,        20 },
    {  321,  360, RM_QS,                  0,         0 },
    {    0,    0, RM_PBRENT,              1,   1048576 },
    {    0,    0, RM_ECM_SCALED,          4,        20 },
    {    0,    0, RM_ECM_SCALED,          8,        20 },
    {  361,  400, RM_QS,                  0,         0 },
    {    0,    0, RM_HOLF,          1048576,         0 },
    {    0,    0, RM_CHEB,            50000,         0 },
    {    0,    0, RM_PM1,           5000000, 100000000 },
    {    0,    0, RM_ECM_SCALED,         32,        40 },
    {    0,    0, RM_ECM_SCALED,          8,       100 },
    {    0,    0, RM_ECM_SCALED,         16,       100 },
    {    0,    0, RM_ECM_SCALED,         32,       100 },
    {  401, MPU_SIQS_MAX_BITS, RM_QS,     0,         0 },
    {    0,    0, RM_ECM_SCALED,         64,       100 },
    {    0,    0, RM_ECM_SCALED,        128,       100 },
    /* last resort, beyond factor() */
    {    0,    0, RM_ECM_SCALED,        256,       100, RF_LAST },
    {    0,    0, RM_ECM_SCALED,        512,       100, RF_LAST },
    {    0,    0, RM_ECM_SCALED,       1024,       100, RF_LAST },
    {    0,    0, RM_ECM_SCALED,       2048,       100, RF_LAST },
    {    0,    0, RM_ECM_SCALED,       4096,       100, RF_LAST }
#else
    /* minbits maxbits method           arg1       arg2  flags */
    {    0,   63, RM_BRENT63,        400000,         0 },
    {   65,  126, RM_PM1,              5000,      5000 },
    {   65,  126, RM_TINYQS,              0,         0 },
    {    0,   53, RM_SQUFOF,         400000,         0 },
    {   54,   58, RM_PM1,              1000,     10000 },
    {   59,   63, RM_PM1,              2000,     20000 },
    {   64,   72, RM_PM1,              4000,     40000 },
    {   65,   77, RM_PM1,             10000,    100000 },
    {    0,   77, RM_SQUFOF,        1000000,         0 },
    {    0,    0, RM_PM1,             20000,    200000 },
    {    0,    0, RM_ECM,               200,         4 },
    {    0,    0, RM_ECM,               600,        20 },
    {    0,    0, RM_ECM,              2000,        10 },
    /* MPUG's factor() skips this p-1 for 100 to 159 bits */
    {    0,   99, RM_PM1,            200000,   3000000 },
    {  160,    0, RM_PM1,            200000,   3000000 },
    /* ECM by size, from which rung_ecm_b1() takes its B1; Dana confirms
     * that 2 curves are deliberate for 100 to 159 bits: a quick ECM hit
     * before going to QS.
     */
    {    0,   99, RM_ECM,              5000,        20 },
    {  100,  127, RM_ECM,             10000,         2 },
    {  128,  159, RM_ECM,             20000,         2 },
    {  160,  191, RM_ECM,             30000,        20 },
    {  192,  223, RM_ECM,             40000,        40 },
    {  224,  255, RM_ECM,             80000,        40 },
    {  256,  511, RM_ECM,            160000,        80 },
    {  512,    0, RM_ECM,            320000,       160 },
    {   90,  299, RM_QS,                  0,         0 },
    {    0,    0, RM_ECM_SCALED,          2,        20 },
    {    0,    0, RM_PBRENT,              1,   1048576 },
    {    0,    0, RM_ECM_SCALED,          4,        20 },
    {    0,    0, RM_ECM_SCALED,          8,        20 },
    {    0,    0, RM_HOLF,          1048576,         0 },
    /* available earlier, presumed trustworthy from v0.54 */
    {    0,    0, RM_CHEB,            50000,         0, RF_054 },
    {    0,    0, RM_PM1,           5000000, 100000000 },
    {    0,    0, RM_ECM_SCALED,         32,        40 },
    /* last resort */
    {    0,    0, RM_ECM_SCALED,          8,       100, RF_LAST },
    {    0,    0, RM_ECM_SCALED,         16,       100, RF_LAST },
    {    0,    0, RM_ECM_SCALED,         32,       100, RF_LAST },
    {    0,    0, RM_ECM_SCALED,         64,       100, RF_LAST },
    {    0,    0, RM_ECM_SCALED,        128,       100, RF_LAST },
    {    0,    0, RM_ECM_SCALED,        256,       100, RF_LAST },
    {    0,    0, RM_ECM_SCALED,        512,       100, RF_LAST },
    {    0,    0, RM_ECM_SCALED,       1024,       100, RF_LAST },
    {    0,    0, RM_ECM_SCALED,       2048,       100, RF_LAST },
    {    0,    0, RM_ECM_SCALED,       4096,       100, RF_LAST }
#endif
};
#define TM_TERM 0
/* TM_INIT (see coultau.h) leaves room for possible power check at rung 1 */
#define TM_MAX (sizeof(rungs) / sizeof(t_rung))

#ifdef MPUG_SIQS
/* the base B1 for scaled ECM, as factor_ecm_base_bound() in factor.c */
static inline ulong rung_ecm_b1(uint nbits) {
    return nbits < 65 ? 5000
        : nbits < 160 ? 20000
        : nbits < 192 ? 30000
        : nbits < 224 ? 40000
        : nbits < 256 ? 80000
        : nbits < 512 ? 160000
        : 320000;
}

/* B1 for the early p-1, as factor_early_pm1_bound() in factor.c */
static inline ulong rung_early_pm1_b1(uint nbits) {
    return nbits < 88 ? 0
        : nbits < 112 ? 1000
        : nbits < 176 ? 2000
        : 20000;
}

/* Trial division to a limit tlim (see TLIM_IS_SQUARE) has shown that
 * a value has no factor less than the root of tlim.
 */
static inline uint32_t trial_start(ulong tlim) {
    ulong r = (ulong)sqrt((double)tlim);
    while (r * r > tlim)
        --r;
    while ((r + 1) * (r + 1) <= tlim)
        ++r;
    return (r > UINT32_MAX) ? UINT32_MAX : (uint32_t)r;
}
#else
/* the base B1 for scaled ECM, that of the ECM by size above */
static inline ulong rung_ecm_b1(uint nbits) {
    return nbits < 100 ? 5000
        : nbits < 128 ? 10000
        : nbits < 160 ? 20000
        : nbits < 192 ? 30000
        : nbits < 224 ? 40000
        : nbits < 256 ? 80000
        : nbits < 512 ? 160000
        : 320000;
}
#endif

/* Returns the bitset of rungs that apply to values of nbits bits,
 * including last resort rungs only if last is TRUE.
 */
static ulong rung_mask(uint nbits, bool last) {
    ulong bits = 0;
    for (uint i = TM_INIT; i < TM_MAX; ++i) {
        const t_rung *r = &rungs[i];
        if (nbits < r->minbits || (r->maxbits && nbits > r->maxbits))
            continue;
        if ((r->flags & RF_LAST) && !last)
            continue;
#ifndef MPUG_054
        if (r->flags & RF_054)
            continue;
#endif
        bits |= 1UL << i;
    }
    return bits;
}

/* Invoke QS on n, which has no factor below the root of tlim (see
 * TLIM_IS_SQUARE), and return a prime factor in f. QS gives us a
 * partition of n, of which we use only one part, accepting that we may
 * do extra work to find the other parts again.
 */
static bool do_qs(mpz_t n, mpz_t f, ulong tlim) {
#ifdef MPUG_SIQS
    uint32_t count;
    mpz_t *parts = gmp_siqs(n, &count, trial_start(tlim), 0);
#else
    mpz_t *parts = simpqs_array;
    uint count = _GMP_simpqs(n, parts);
#endif
    bool found = 0;

    if (count >= 2) {
        /* look for a prime among the parts */
        for (uint i = 0; i < count; ++i)
            if (ct_prime(parts[i])) {
                mpz_set(f, parts[i]);
                found = 1;
                break;
            }
    }
    if (count >= 2 && !found) {
        /* all parts composite: find a factor of the first one */
        factor_state fs;
        fs_init(&fs);
        mpz_set(fs.n, parts[0]);
        fs.tlim = tlim;     /* ref TLIM_IS_SQUARE */
        fs.state = FS_POWER;
        if (!factor_one(&fs))
            fail("factor_one(%Zd) failed to find factor in QS composite\n",
                fs.n
            );
        mpz_set(f, fs.f);
        fs_clear(&fs);
        found = 1;
    }
#ifdef MPUG_SIQS
    gmp_siqs_free(parts, count);
#endif
    return found;
}

/* Try rung r on n of nbits bits, with no factor below the root of tlim.
 * Returns TRUE with a proper factor of n in f if it finds one.
 */
static bool rung_try(const t_rung *r, mpz_t n, mpz_t f, uint nbits,
        ulong tlim) {
    switch (r->method) {
#ifdef MPUG_SIQS
    case RM_TINYECM:
        return _GMP_tinyecm64_factor(n, f, 0);
    case RM_EARLY_PM1: {
        ulong b1 = rung_early_pm1_b1(nbits);
        return _GMP_pminus1_factor(n, f, b1, (nbits <= 224 ? 5 : 10) * b1);
    }
    case RM_ECM_PRE:
        return _GMP_ECM_FACTOR(n, f, r->arg1,
                (nbits <= 224) ? 40 * r->arg1 : 0, r->arg2);
#else
    case RM_BRENT63:
        return pbrent63(n, f, r->arg1);
    case RM_TINYQS:
        return tinyqs(n, f);
#endif
    case RM_SQUFOF:
        return squfof126(n, f, r->arg1);
    case RM_PM1:
        return _GMP_pminus1_factor(n, f, r->arg1, r->arg2);
    case RM_ECM:
        return _GMP_ECM_FACTOR(n, f, r->arg1, 0, r->arg2);
    case RM_ECM_SCALED:
        return _GMP_ECM_FACTOR(n, f, r->arg1 * rung_ecm_b1(nbits), 0,
                r->arg2);
    case RM_QS:
        return do_qs(n, f, tlim);
    case RM_PBRENT:
        return _GMP_pbrent_factor(n, f, r->arg1, r->arg2);
    case RM_HOLF:
        return _GMP_holf_factor(n, f, r->arg1);
    case RM_CHEB:
        return _GMP_cheb_factor(n, f, r->arg1, r->arg2);
    default:
        fail("unknown factoring method %u", r->method);
    }
    return 0;
}

#ifdef VERBOSE
static const char *rm_name[] = {
    "none", "brent63", "squfof", "tinyqs", "p-1", "ecm", "ecm", "qs",
    "brent", "holf", "cheb", "tecm", "epm1", "ecm"
};
static inline bool ct_rung(uint i, mpz_t n, mpz_t f, uint nbits,
        ulong tlim) {
    const t_rung *rp = &rungs[i];
    if (!VB(VB_TRACE))
        return rung_try(rp, n, f, nbits, tlim);
    struct timespec t0;
    clock_gettime(CG_CLOCK, &t0);
    bool r = rung_try(rp, n, f, nbits, tlim);
    gmp_printf("(%ld) %s: %Zu [%u: %lu, %lu] %u", cgdiff(&t0),
            rm_name[rp->method], n, i, rp->arg1, rp->arg2, r);
    if (r)
        gmp_printf(" %Zu", f);
    gmp_printf("\n");
    return r;
}
#else
#   define ct_rung(i, n, f, nbits, tlim) \
        rung_try(&rungs[i], n, f, nbits, tlim)
#endif

void init_tmfbl(uint flake);
void done_tmfbl(void);
void init_tau(uint rough, uint flake) {
    UV pn;
    test_rough = rough;
    PRIME_ITERATOR(iter);
    primes_small[0] = 0;
    primes_small[1] = 2;
    for (pn = 2; pn < NPRIMES_SMALL; pn++)
        primes_small[pn] = prime_iterator_next(&iter);
    prime_iterator_destroy(&iter);
    mpz_init(tmf);
    mpz_init(tmf2);
    mpz_init(tmp_lim);
    init_tmfbl(flake);
#ifndef MPUG_SIQS
    for (uint i = 0; i < SIMPQS_SIZE; ++i)
        mpz_init(simpqs_array[i]);
#endif
#ifdef MPUG_054
    mpz_init_set_ui(gcd_1k, 1);
    for (pn = 2; pn < TRIAL_BAND_A_END; ++pn)
        mpz_mul_ui(gcd_1k, gcd_1k, primes_small[pn]);
    mpz_init_set_ui(gcd_4k, 1);
    for (pn = TRIAL_BAND_A_END; pn < TRIAL_BAND_B_END; ++pn)
        mpz_mul_ui(gcd_4k, gcd_4k, primes_small[pn]);
    mpz_init_set_ui(gcd_16k, 1);
    for (pn = TRIAL_BAND_B_END; pn < TRIAL_BAND_C_END; ++pn)
        mpz_mul_ui(gcd_16k, gcd_16k, primes_small[pn]);
    mpz_init_set_ui(gcd_32k, 1);
    for (pn = TRIAL_BAND_C_END; pn < TRIAL_BAND_D_END; ++pn)
        mpz_mul_ui(gcd_32k, gcd_32k, primes_small[pn]);
    mpz_init_set_ui(gcd_64k, 1);
    for (pn = TRIAL_BAND_D_END; pn < TRIAL_BAND_E_END; ++pn)
        mpz_mul_ui(gcd_64k, gcd_64k, primes_small[pn]);
    mpz_init(gcd_scratch);
#endif
}

void done_tau(void) {
#ifndef MPUG_SIQS
    for (uint i = 0; i < SIMPQS_SIZE; ++i)
        mpz_clear(simpqs_array[i]);
#endif
    done_tmfbl();
    if (taum_alloc)
        for (uint i = 0; i < taum_alloc; ++i)
            mpz_clear(taum[i].n);
    free(taum);
    mpz_clear(tmf);
    mpz_clear(tmf2);
    mpz_clear(tmp_lim);
#ifdef MPUG_054
    mpz_clear(gcd_1k);
    mpz_clear(gcd_4k);
    mpz_clear(gcd_16k);
    mpz_clear(gcd_32k);
    mpz_clear(gcd_64k);
    mpz_clear(gcd_scratch);
#endif
}

void alloc_taum(uint size) {
    if (size > taum_alloc) {
        taum = realloc(taum, size * sizeof(t_tm));
        for (uint i = taum_alloc; i < size; ++i)
            mpz_init(taum[i].n);
        taum_alloc = size;
    }
}

void fs_init(factor_state* fs) {
    fs->state = FS_INIT;
    mpz_init(fs->n);
    mpz_init(fs->f);
    fs->ef = 1;
    fs->sp = 0;
    fs->log = get_verbose_level();
    fs->ntofac = 0;
    fs->tlim = 0;
    fs->missed = 0;
    return;
}

void fs_clear(factor_state* fs) {
    mpz_clear(fs->n);
    mpz_clear(fs->f);
    for (int i = 0; i < fs->ntofac; ++i)
        mpz_clear(fs->tofac_stack[i]);
    return;
}

int fs_trial(factor_state* fs) {
    UV tlim = fs->tlim;
    UV sp = fs->sp;
    UV un = fs->un;
    UV lim, p;

    if (sp == 0) {
        int e2 = 0;
        while (mpz_even_p(fs->n)) {
            mpz_divexact_ui(fs->n, fs->n, 2);
            ++e2;
        }
        sp = 2;
        un = (mpz_cmp_ui(fs->n, 2 * tlim) >= 0) ? 2 * tlim : mpz_get_ui(fs->n);
        if (e2) {
            mpz_set_ui(fs->f, 2);
            fs->e = e2;
            goto found_trial;
        }
    }

    lim = (tlim < un) ? tlim : un;
#ifdef MPUG_054
    /* skip bands of trial primes via gcd if possible */
    sp = skip_trial_bands(sp, fs->n, lim, NULL);
#endif
    for (p = primes_small[sp]; p * p < lim; p = primes_small[++sp]) {
        int ep = 0;
        while (mpz_divisible_ui_p(fs->n, p)) {
            mpz_divexact_ui(fs->n, fs->n, p);
            ++ep;
        }
        if (ep) {
            mpz_set_ui(fs->f, p);
            fs->e = ep;
            un = (mpz_cmp_ui(fs->n, 2 * tlim) > 0)
                    ? 2 * tlim : mpz_get_ui(fs->n);
            goto found_trial;
        }
    }

    if (un < p * p) {
        mpz_set(fs->f, fs->n);
        fs->e = 1;
        mpz_set_ui(fs->n, 1);
        goto found_trial;
    }
    return 0;

found_trial:
    fs->sp = sp;
    fs->un = un;
    return 1;
}

static int _fs_remove(factor_state* fs) {
    int e = 0;
    e += mpz_remove(fs->n, fs->n, fs->f);
    for (int i = 0; i < fs->ntofac; ++i)
        e += mpz_remove(fs->tofac_stack[i], fs->tofac_stack[i], fs->f);
    return e;
}

/* Try to find one more prime factor and its exponent. Returns true if
 * it found one, else factorization is complete.
 */
int factor_one(factor_state* fs) {
    int cmp;

fs_retry:
    if (mpz_cmp_ui(fs->n, 1) == 0) {
        if (fs->ntofac == 0) {
            fs->state = FS_TERM;
            return 0; /* no more factors to find */
        }
        --fs->ntofac;
        mpz_set(fs->n, fs->tofac_stack[fs->ntofac]);
        mpz_clear(fs->tofac_stack[fs->ntofac]);
        fs->state = FS_LARGE;
        goto fs_retry;
    }

    switch (fs->state) {
    default:
        croak("Unknown state\n");
    case FS_TERM:
        return 0;
    case FS_INIT:
        if (mpz_cmp_ui(fs->n, 0) == 0) {
            fs->state = FS_TERM;
            mpz_set_ui(fs->f, 0);
            fs->e = 1;
            return 1;
        }
        fs->sp = 0;
        /* ref TLIM_IS_SQUARE */
#ifdef MPUG_054
        /* new limits justified by gcd-banding support */
        fs->tlim = 64007UL * 64007UL;
#else
        fs->tlim = (nbits > 80) ? 4001 * 4001 : 16001 * 16001;
#endif
        fs->state = FS_TRIAL;
    case FS_TRIAL:
        if (ct_trial(fs))
            return 1;
        fs->state = FS_POWER;
    case FS_POWER:
        fs->ef = ct_power(fs->n);
        if (!fs->ef)
            fs->ef = 1;
        fs->state = FS_LARGE;
/*
 * This set of operations is meant to provide good performance for
 * "random" numbers as input. Hence we stack lots of effort up front
 * looking for small factors: prho and pbrent are ~ O(f^1/2) where
 * f is the smallest factor. SQUFOF is O(N^1/4), so arguably not
 * any better. p-1 and ECM are quite useful for pulling out small
 * factors (6-20 digits).
 *
 * Factoring a 778-digit number consisting of 101 8-digit factors
 * should complete in under 3 seconds. Factoring numbers consisting
 * of many 12-digit or 14-digit primes should take under 10 seconds.
 *
 * For state > 2, all returned exponents should be multiplied by fs->ef,
 * and tofac_stack must be checked (see label fs_retry above).
 */
    case FS_LARGE:
        /* Trial division stops short of the root of tlim, so tlim itself
         * may be left: if so, that root is a prime, squared. Anything less
         * is a prime. Any path responsible for setting tlim (marked by
         * TLIM_IS_SQUARE) must ensure that it is a square.
         */
        cmp = mpz_cmp_ui(fs->n, fs->tlim);
        if (cmp == 0) {
            mpz_sqrt(fs->f, fs->n);
            fs->e = fs->ef * _fs_remove(fs);
            return 1;
        }
        if (cmp < 0 || ct_prime(fs->n)) {
            mpz_set(fs->f, fs->n);
            fs->e = fs->ef * _fs_remove(fs);
            return 1;
        }

        {
            /* the whole ladder, including last resort rungs */
            uint nbits = mpz_sizeinbase(fs->n, 2);
            ulong bits = rung_mask(nbits, 1) & ~fs->missed;
            for (uint i = TM_INIT; i < TM_MAX; ++i) {
                if (!(bits & (1UL << i)))
                    continue;
                if (ct_rung(i, fs->n, fs->f, nbits, fs->tlim))
                    goto found_factor;
                if (rungs[i].flags & RF_ONCE)
                    fs->missed |= 1UL << i;
            }
        }

        /* Last resort failed and we have no interface to signal that,
         * so give up with a fatal error. */
        fail("factor_one(%Zd) gave up without finding a factor\n", fs->n);
    }
found_factor:
    if (!ct_prime(fs->f)) {
        mpz_init(fs->tofac_stack[fs->ntofac]);
        mpz_divexact(fs->tofac_stack[fs->ntofac], fs->n, fs->f);
        ++fs->ntofac;
        mpz_set(fs->n, fs->f);
        goto fs_retry;
    }
    fs->e = fs->ef * _fs_remove(fs);
    return 1;
}

/* Return true if what's left to factor is a prime */
static int _scanp(factor_state* fs) {
    int result = 0;
    if (mpz_cmp_ui(fs->n, 1) != 0) {
        if (ct_prime(fs->n))
            result = 1;
        else
            return 0;
    }
    for (int i = 0; i < fs->ntofac; ++i) {
        if (mpz_cmp_ui(fs->tofac_stack[i], 1) == 0)
            continue;
        if (result)
            return 0;
        if (ct_prime(fs->tofac_stack[i]))
            result = 1;
        else
            return 0;
    }
    return result;
}

/* Return true if tau(n^x) == k */
int is_taux(mpz_t n, uint32_t k, uint32_t x) {
    int cmp = mpz_cmp_ui(n, 1);
    int result = 0;
    factor_state fs;

#ifdef VERBOSE
    if (VB(VB_TRACE))
        gmp_printf("is_taux t=%u (%u) %Zu^%u\n", k, mpz_sizeinbase(n, 2), n, x);
#endif
    if (cmp < 0)
        return 0;
    if (cmp == 0)
        return k == 1 || x == 0;
    if (k == 1 || x == 0)
        return 0;
    if (k == x + 1)
        return ct_prime(n) ? 1 : 0;

    fs_init(&fs);
    mpz_set(fs.n, n);
    while (1) {
        /* we may have extra factors in the stack at any point now. */
        uint xe = x * fs.ef;
        if (k == xe + 1) {
            result = _scanp(&fs);
            break;
        }
        /* MPUG-0.54 has a bug in power_factor when small primes are present,
         * so wait until we've completed trial division before testing.
         */
        if ((k & 1) && (xe & 1) && fs.state == FS_LARGE) {
            for (int i = 0; i < fs.ntofac; ++i) {
                mpz_mul(fs.n, fs.n, fs.tofac_stack[i]);
                mpz_clear(fs.tofac_stack[i]);
            }
            fs.ntofac = 0;
            int e = ct_power(fs.n);
            if (e == 0 || e & 1 || e > k)
                break;
            /* we actually need e divisible by gcd(map $_ - 1, divisors(k)) */
            x *= e;
            continue;
        }
        if (!factor_one(&fs))
            break;
        if (k % (fs.e * x + 1))
            break;
        k /= fs.e * x + 1;
        if (k == 1) {
            result = (mpz_cmp_ui(fs.n, 1) == 0);
            for (int i = 0; i < fs.ntofac; ++i)
                result &= (mpz_cmp_ui(fs.tofac_stack[i], 1) == 0);
            break;
        }
        /* if fs.state == FS_LARGE, we need n >= max_trial_p ^ min_exp, where
         * max_trial_p = sqrt(fs.tlim), min_exp = sum(map $_ - 1, factor(k))
         */
    }
    fs_clear(&fs);
    return result;
}

static inline bool prep_abort(t_tm *tm, bool result) {
    if (result)
        tm->state = 0;  /* done */
    return result;
}

/* primality as tau_multi_prep() tests it, for the benches */
bool tau_isprime(mpz_t n) {
    return ct_prime(n);
}

/* Effectively identical to _GMP_is_prob_prime(), but with VERBOSE
 * diagnostics for debugging/calibration.
 */
bool tau_prime_test(mpz_t n) {
#ifdef VERBOSE
    if (VB(VB_TRACE))
        gmp_printf("tau_prime_test %Zu\n", n);
#endif
    int res = ct_pretest(n);
    if (res == 0)
        return 0;
    if (res != 1)
        return 1;
    return ct_bpsw(n);
}

bool tau_prime_prep(uint i) {
#ifdef VERBOSE
    if (VB(VB_TRACE))
        gmp_printf("tau_prime_prep vi=%u %Zu\n", taum[i].vi, taum[i].n);
#endif
    /* FIXME: break this out further */
    int res = ct_pretest(taum[i].n);
    if (res == 0)
        return 0;
    taum[i].state = (res == 1) ? 1 : 0;
    return 1;
}

/* We'll use trial division the whole way if the minimum number of factors
 * is at least test_rough-1, but only if we can fully test n that way: no
 * point doing the work if we end up falling through to full factorization.
 * TODO: it is not reasonable to ask the user to specify the roughness
 * test, come up with an adaptive way to do this automatically.
 */
static inline UV rough_assisted_tlim(UV default_lim, mpz_t n, uint t) {
    uint roughness = divisors[t].sumpm;
    if (roughness < test_rough - 1)
        return default_lim;
    mpz_root(tmp_lim, n, roughness);
    if (mpz_sizeinbase(tmp_lim, 2) >= 8 * sizeof(UV) / 2)
        return default_lim;
    UV lim = mpz_get_ui(tmp_lim);
    lim = lim * lim;        /* ref TLIM_IS_SQUARE */
    /* need room to double it */
    return (lim > (UV_MAX >> 1)) ? default_lim : lim;
}

/* Given taum[i].{n, t, vi, e}, does initial fast tests that may rule
 * out the possibility that tau(n^e) == t, and prepares for slower tests.
 * Returns 0 if initial tests rule it out, else 1.
 * FIXME: external code also wants to know if we have already shown
 * tau(n^e) == t; it currently checks taum[i].state == 0, but better
 * to expose this in the return value.
 */
bool tau_multi_prep(uint i) {
    t_tm *tm = &taum[i];
    uint t = tm->t;
    uint e = tm->e;
    uint nbits = mpz_sizeinbase(tm->n, 2);
    if (nbits <= 1)
        return 0;
    tm->state = 1;  /* init */

#ifdef VERBOSE
    extern ulong g_ati;
    extern uint g_walkv_call;
    if (VB(VB_TRACE))
        gmp_printf("tau_multi_prep vi=%u t=%u e=%u call=%u ati=%lu (%u) %Zu\n",
                tm->vi, t, e, g_walkv_call, g_ati, nbits, tm->n);
    if (VB(VB_TRACE))
        clock_gettime(CG_CLOCK, &cg_tp0);
#endif
    if (t == 1) {
        dz("div: t=1");
        return prep_abort(tm, mpz_cmp_ui(tm->n, 1) == 0);
    }

    /* do FS_TRIAL stage directly */
    int ep = 0;
    while (mpz_even_p(tm->n)) {
        mpz_divexact_ui(tm->n, tm->n, 2);
        ++ep;
    }
    if (ep) {
        uint et = ep * e + 1;
        if ((t % et) != 0) {
            dz("div: %u ~| t=%u", et, t);
            return 0;
        }
        t /= et;
        if (t == 1) {
            dz("div: t=1");
            return prep_abort(tm, mpz_cmp_ui(tm->n, 1) == 0);
        }
        nbits -= ep;
        ep = 0;
    }

    UV p;
    UV sp = 2;
    /* ref TLIM_IS_SQUARE */
#ifdef MPUG_054
    /* new limits justified by gcd-banding support */
    UV tlim = 64007UL * 64007UL;
#else
    UV tlim = (nbits > 80) ? 4001 * 4001 : 16001 * 16001;
#endif
    if (test_rough)
        tlim = rough_assisted_tlim(tlim, tm->n, t);
    UV un = mpz_cmp_ui(tm->n, 2 * tlim) >= 0
        ? 2 * tlim
        : mpz_get_ui(tm->n);
    UV lim = (tlim < un) ? tlim : un;
    PRIME_ITERATOR(iter);
#ifdef MPUG_054
    /* skip bands of trial primes via gcd if possible, updating iterator */
    sp = skip_trial_bands(sp, tm->n, lim, &iter);
#endif
    while (1) {
        p = prime_iterator_next(&iter);
        if (p * p > lim)
            break;
        while (mpz_divisible_ui_p(tm->n, p)) {
            mpz_divexact_ui(tm->n, tm->n, p);
            ++ep;
        }
        if (ep) {
            uint et = ep * e + 1;
            if ((t % et) != 0) {
                dz("div: %u ~| t=%u", et, t);
                prime_iterator_destroy(&iter);
                return 0;
            }
            t /= et;
            if (t == 1) {
                dz("div: t=1");
                prime_iterator_destroy(&iter);
                return prep_abort(tm, mpz_cmp_ui(tm->n, 1) == 0);
            } else if (t < e + 1) {
                dz("div: t=%u < %u", t, e + 1);
                prime_iterator_destroy(&iter);
                return 0;
            } else if (t == e + 1) {
                dz("div: t=%u", e + 1);
                prime_iterator_destroy(&iter);
                return prep_abort(tm, ct_prime(tm->n));
            } else if (mpz_cmp_ui(tm->n, 1) == 0) {
                dz("div: n=1");
                prime_iterator_destroy(&iter);
                return 0;
            }
            ep = 0;
            if (test_rough)
                tlim = rough_assisted_tlim(tlim, tm->n, t);
            un = mpz_cmp_ui(tm->n, 2 * tlim) > 0
                ? 2 * tlim
                : mpz_get_ui(tm->n);
            lim = (tlim < un) ? tlim : un;
#ifdef MPUG_054
            sp = skip_trial_bands(sp, tm->n, lim, &iter);
#endif
        }
    }
    prime_iterator_destroy(&iter);

    if (un < p * p) {
        dz("div: tail is prime");
        return prep_abort(tm, t == ((mpz_cmp_ui(tm->n, 1) == 0) ? 1 : e + 1));
    } else if (mpz_cmp_ui(tm->n, 1) == 0) {
        dz("div: n = 1");
        return prep_abort(tm, t == 1);
    } else if (t < e + 1) {
        dz("div: t=%u < %u", t, e + 1);
        return 0;
    } else if (t == e + 1) {
        dz("div: t == %u", e + 1);
        return prep_abort(tm, ct_prime(tm->n));
    }
    if (test_rough && t >= test_rough) {
        mpz_ui_pow_ui(tmp_lim, p, divisors[t].sumpm);
        if (mpz_cmp(tm->n, tmp_lim) < 0) {
            dz("div: rough[%u]", divisors[t].sumpm);
            return 0;
        }
    }
    dz("div: done, t=%u, e=%u", t, e);
    if (ct_prime(tm->n))
        return prep_abort(tm, t == 2);
    e = ct_power(tm->n);
    if (e) {
        /* we found a power, did it leave a prime? */
        tm->e *= e;
        if (ct_prime(tm->n))
            return prep_abort(tm, t == tm->e + 1);
    }
    if ((t & 1) && (tm->e & 1))
        return 0;
    if (!(t & 1) && !(tm->e & 1))
        return 0;
    tm->t = t;
    tm->tlim = tlim;
    return 1;
}

/* tmfbl[size] is the bitset of rungs to try on values of size bits, for
 * size up to tmfb_maxb; tmfb_lim the bitset for all larger sizes
 */
ulong *tmfbl = NULL;
uint tmfb_maxb;
ulong tmfb_lim;

void init_tmfbl(uint flake) {
    /* don't flake out for anything before QS */
    ulong no_flake = 0;
    for (uint i = TM_INIT; i < TM_MAX && rungs[i].method != RM_QS; ++i)
        no_flake |= 1UL << i;
#ifdef TRY_HARDER
    bool last = 1;
#else
    bool last = 0;
#endif

    /* beyond tmfb_maxb, the rungs that apply no longer change */
    tmfb_maxb = 0;
    for (uint i = TM_INIT; i < TM_MAX; ++i) {
        const t_rung *r = &rungs[i];
        if (tmfb_maxb < r->maxbits)
            tmfb_maxb = r->maxbits;
        if (r->minbits && tmfb_maxb < r->minbits - 1)
            tmfb_maxb = r->minbits - 1;
    }
    tmfb_lim = rung_mask(tmfb_maxb + 1, last);
    if (flake && tmfb_maxb > flake)
        tmfb_lim &= no_flake;
    tmfbl = malloc((tmfb_maxb + 1) * sizeof(ulong));
    for (uint i = 0; i <= tmfb_maxb; ++i) {
        ulong bits = rung_mask(i, last);
        tmfbl[i] = (flake && i > flake) ? (bits & no_flake) : bits;
    }
}

void done_tmfbl(void) {
    free(tmfbl);
}

static inline ulong _find_tmfb(uint size) {
    if (size <= tmfb_maxb)
        return tmfbl[size];
    return tmfb_lim;
}

/* see also other_comparator() in coul.c */
int taum_comparator(const void *va, const void *vb) {
    t_tm *tma = (t_tm *)va;
    t_tm *tmb = (t_tm *)vb;
    uint at2 = tma->t ^ (tma->t - 1);
    uint bt2 = tmb->t ^ (tmb->t - 1);
    if (at2 < bt2)
        return -1;
    if (at2 > bt2)
        return 1;
    if (tma->t < tmb->t)
        return -1;
    if (tma->t > tmb->t)
        return 1;
    int cmp = mpz_cmp(tma->n, tmb->n);
    return cmp ? cmp : (tma->vi > tmb->vi) - (tma->vi < tmb->vi);
}

mpz_t *tm_factor(t_tm *tm) {
    if (ct_prime(tmf))
        return &tmf;
    /* we have a composite factor */
    mpz_divexact(tmf2, tm->n, tmf);
    if (ct_prime(tmf2))
        return &tmf2;
    /* .. leaving a composite residue */
    factor_state fs;
    fs_init(&fs);
    fs.tlim = tm->tlim;     /* ref TLIM_IS_SQUARE */
    if (mpz_cmp(tmf, tmf2) < 0)
        mpz_set(fs.n, tmf);
    else
        mpz_set(fs.n, tmf2);
    fs.state = FS_POWER;
    if (!factor_one(&fs))
        fail("no factor found for composite %Zd\n", fs.n);
    mpz_set(tmf, fs.f);
    fs_clear(&fs);
    return &tmf;
}

/* Try rung i of the ladder on tm->n, setting tmf to any factor found. */
static inline bool tmf_try(uint i, t_tm *tm) {
    return ct_rung(i, tm->n, tmf, mpz_sizeinbase(tm->n, 2), tm->tlim);
}

/* Record that rung i of the ladder found no factor of tm->n. */
static inline void tmf_miss(uint i, t_tm *tm) {
    tm->state = i + 1;
    if (rungs[i].flags & RF_ONCE)
        tm->missed |= 1UL << i;
}

/* the ladder for the benches (bench.c) */
uint tm_rungs(void) {
    return TM_MAX;
}
bool tm_rung(uint i, t_tm *tm) {
    return tmf_try(i, tm);
}
ulong tm_rungmask(uint bits) {
    return _find_tmfb(bits);
}

/* Returns the number of values still being tested at the point a failure
 * was seen; return value of zero implies success.
 */
uint tau_multi_run(uint count, tau_failure_handler tfh) {
    uint i = 0;
    /* Shuffle the entries that did not complete by trial division to
     * the front. Find size and thus the associated tmfb entry for each. */
    for (uint j = 0; j < count; ++j) {
        if (taum[j].state == 0)
            continue;
        if (i < j) {
            mpz_swap(taum[i].n, taum[j].n);
            taum[i].vi = taum[j].vi;
            taum[i].t = taum[j].t;
            taum[i].e = taum[j].e;
            taum[i].tlim = taum[j].tlim;
        }
        taum[i].state = 2;
        taum[i].bits = _find_tmfb(mpz_sizeinbase(taum[i].n, 2));
        taum[i].missed = 0;
        ++i;
    }
    if (i == 0)
        return 0;
    count = i;

    qsort(taum, count, sizeof(t_tm), &taum_comparator);

    uint next_i;
  tmr_retry:
    for (uint i = TM_INIT; i < TM_MAX; i = next_i) {
        next_i = i + 1;
        for (uint j = 0; j < count; ++j) {
            t_tm *tm = &taum[j];
          tmr_redo:
            if (tm->state > i)
                continue;
            if (!(tm->bits & (1UL << i)))
                continue;
            if (!tmf_try(i, tm)) {
                tmf_miss(i, tm);
                continue;
            }

            /* make sure we have a _prime_ factor */
            mpz_t *f = tm_factor(tm);
            uint e = 0;
            while (mpz_divisible_p(tm->n, *f)) {
                ++e;
                mpz_divexact(tm->n, tm->n, *f);
            }
            if (e == 0)
                fail("state %d found non-divisible factor %Zd for %Zd\n",
                    tm->state, *f, tm->n
                );
            e = e * tm->e + 1;
            if (tm->t % e)
                return count;
            tm->t /= e;
            if (tm->t == 1) {
                if (mpz_cmp_ui(tm->n, 1) != 0)
                    return count;
                goto tmr_splice;
            } else if (tm->t == 2) {
                if (tm->e != 1 || !ct_prime(tm->n))
                    return count;
                goto tmr_splice;
            } else if (mpz_cmp_ui(tm->n, 1) == 0)
                return count;
            else if (tm->t & 1) {
                if (tm->e & 1) {
                    /* we need n^e square, so must have n square */
                    e = ct_power(tm->n);
                    if (e == 0 || e & 1 || tm->e * e >= tm->t)
                        return count;
                    tm->e *= e;
                }
                /* odd tau should be easy, do immediate full check */
                if (!is_taux(tm->n, tm->t, tm->e))
                    return count;
                goto tmr_splice;
            } else if (ct_prime(tm->n)) {
                if (tm->t != tm->e + 1)
                    return count;
                goto tmr_splice;
            }
            tm->state = TM_INIT;
            next_i = TM_INIT;
            tm->bits = _find_tmfb(mpz_sizeinbase(tm->n, 2)) & ~tm->missed;
            goto tmr_retry;

          tmr_splice:
            --count;
            if (count == 0)
                return 0;
            if (j < count) {
                mpz_swap(taum[j].n, taum[count].n);
                taum[j].vi = taum[count].vi;
                taum[j].t = taum[count].t;
                taum[j].e = taum[count].e;
                taum[j].state = taum[count].state;
                taum[j].bits = taum[count].bits;
                taum[j].tlim = taum[count].tlim;
                taum[j].missed = taum[count].missed;
                goto tmr_redo;
            }
            /* don't redo this j, it has fallen off the end */
            continue;
        }
    }
    /* handle failure */
    if (tfh)
        return (*tfh)(count, taum);
    fail("no factors found for %u non-primes starting %Zd (%u)\n",
        count, taum[0].n, taum[0].t
    );
}

/* Same as tau_multi_run() except that all values are required to be prime.
 * It is the caller's responsibility to ensure the precondition is met.
 * We test only the values from 'first' on, leaving any before that as
 * they are; on failure, taum[first].vi is the value that failed.
 */
uint tau_prime_run(uint first, uint count) {
    uint i = first;
    /* Shuffle the entries that did not complete by trial division to
     * the front, and order by size.
     */
    for (uint j = first; j < count; ++j) {
        if (taum[j].state == 0)
            continue;
        if (i < j) {
            mpz_swap(taum[i].n, taum[j].n);
            taum[i].vi = taum[j].vi;
        }
        ++i;
    }
    if (i == first)
        return 0;
    count = i;
    qsort(&taum[first], count - first, sizeof(t_tm), &taum_comparator);
    for (i = first; i < count; ++i) {
        if (!ct_bpsw(taum[i].n)) {
            taum[first].vi = taum[i].vi;
            return count - i;
        }
    }
    return 0;
}

bool tau_single_try(uint i) {
    t_tm *tm = &taum[i];
    for (uint i = TM_INIT; i < TM_MAX; ++i) {
        if (!(tm->bits & (1UL << i)))
            continue;
        if (!tmf_try(i, tm)) {
            tmf_miss(i, tm);
            continue;
        }

        mpz_set(tm->n, tmf);
        return 1;
    }
    return 0;
}
