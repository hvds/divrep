/* The benches behind the cost table (see multibench-table): with
 * MULTIBENCH set in the environment, a VERBOSE build of pcoul runs the
 * bench it names instead of the search.
 * Each bench makes its inputs with a GMP generator of its own, seeded
 * by a constant and the size, so that every run tests the same inputs.
 * That holds for one version of GMP: gmp_randinit_default() need not
 * give the same stream in another. Nothing else here or in the search
 * draws from GMP's generator: the factoring and primality code takes
 * its randomness from MPU::GMP's ISAAC, seeded by init_randstate().
 */

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <math.h>
#include <time.h>

#include "coulint.h"
#include "bench.h"
#include "gmp_main.h"
#include "primality.h"
#include "utility.h"

#ifdef VERBOSE
/* Calibration benchmarks for the cost table (see multibench-table), in
 * VERBOSE builds. With MULTIBENCH set to
 * "bits,t,count,F[,seed[,e]]" in the environment, pcoul initialises as usual
 * for its n and k, then feeds test_multi_append() (tau_multi_prep())
 * count random integers of the given bits, coprime to every prime <= F
 * (as the v_i / q_i a walk tests are coprime to the forced primes), with
 * target tau t and exponent multiplier e (default 1; the root of a fixed
 * power v = q.r^g is tested with e = g), runs test_multi_run() on those
 * prep leaves undecided, and reports the outcome fractions and mean
 * times. "prime,bits,count,F" instead measures a prime test on one
 * value (as for a need_prime position or a fixed power's root), and
 * "scan,bits,count,t" the cost of tests that fail at a trial prime, and
 * "ladder,bits,count,F[,alpha]" the factoring ladder and "qs,bits,count"
 * QS alone (mb_ladder(), mb_qs()). The
 * walk loops' own costs are fitted from -dv2 runs instead (see
 * multibench-table), since a synthetic loop misses too much of them.
 */
static inline double mb_now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static volatile ulong mb_sink;
/* random integer of the given bits coprime to every prime <= F */
static void mb_random(mpz_t m, gmp_randstate_t rs, uint bits, uint F) {
    static mpz_t prim, g;
    static uint primF = 0;
    if (primF != F) {
        if (!primF) {
            mpz_init(prim);
            mpz_init(g);
        }
        mpz_primorial_ui(prim, F);
        primF = F;
    }
    do {
        mpz_urandomb(m, rs, bits - 1);
        mpz_setbit(m, bits - 1);
        mpz_gcd(g, prim, m);
    } while (mpz_cmp_ui(g, 1) != 0);
}

/* "prime,bits,count,F": test_primes() on a single value, as for a
 * need_prime position ("P bits F pass us"), and the plain primality test
 * that tau_multi_prep() makes when only a prime is left to find, on the
 * same inputs and on composites with no factor up to 47 ("R bits us us")
 */
static void mb_prime(char *spec) {
    uint bits, count, F;
    if (sscanf(spec, "%u,%u,%u", &bits, &count, &F) != 3)
        fail("MULTIBENCH: expected prime,bits,count,F");
    gmp_randstate_t rs;
    gmp_randinit_default(rs);
    gmp_randseed_ui(rs, 2654435761UL + bits);
    mpz_t m;
    mpz_init(m);
    ulong npass = 0;
    double tt = 0, tr = 0;
    for (uint i = 0; i < count; ++i) {
        mb_random(m, rs, bits, F);
        double t0 = mb_now();
        mb_sink ^= tau_isprime(m);
        tr += mb_now() - t0;
        test_multi_reset();
        t0 = mb_now();
        bool ok = test_prime_append(m, 0) && test_prime_run(0) == 0;
        tt += mb_now() - t0;
        if (ok)
            ++npass;
    }
    printf("P %u %u %.5f %.4f\n", bits, F, (double)npass / count,
            1e6 * tt / count);
    /* and on composites with no small factor */
    double tc = 0;
    uint nc = 0;
    while (nc < count / 4) {
        mb_random(m, rs, bits, 47);
        if (mpz_probab_prime_p(m, 1))
            continue;
        double t0 = mb_now();
        mb_sink ^= tau_isprime(m);
        tc += mb_now() - t0;
        ++nc;
    }
    printf("R %u %.4f %.4f\n", bits, 1e6 * tr / count, 1e6 * tc / nc);
    mpz_clear(m);
    gmp_randclear(rs);
}

static int mb_dcmp(const void *a, const void *b) {
    double x = *(const double *)a, y = *(const double *)b;
    return (x > y) - (x < y);
}

/* the mean of the lowest 95% of count times, discarding outliers such as
 * interrupted measurements
 */
static double mb_trimmed(double *v, uint count) {
    qsort(v, count, sizeof(double), mb_dcmp);
    uint keep = count - count / 20;
    double sum = 0;
    for (uint i = 0; i < keep; ++i)
        sum += v[i];
    return sum / keep;
}

/* "scan,bits,count,t[,t2]": the cost of tests that fail at a trial prime
 * p, for a range of p: test_multi() prep for tau t of a value whose first
 * factor is p^a with a + 1 not dividing t, and a prime test of a value
 * whose first factor is p; with t2, also the extra cost to prep for tau
 * t2 of finding a factor p that does not end it (with batched trial
 * division, a linear scan of its band up to p), relative to finding one
 * at the first trial prime; one line "S bits p prep_us
 * prime_us [extra_us]" per p, up to the trial division limit, and then
 * "L bits p" giving that limit (the last p for which prep still finds the
 * factor)
 */
static void mb_scan(char *spec) {
    uint bits, count, t, t2 = 0;
    if (sscanf(spec, "%u,%u,%u,%u", &bits, &count, &t, &t2) < 3)
        fail("MULTIBENCH: expected scan,bits,count,t[,t2]");
    if (t2 && (t2 & 1 || t2 < 6))
        fail("MULTIBENCH: scan needs even t2 >= 6");
    uint a = 1;
    while (t % (a + 1) == 0)
        ++a;
    /* including both ends of each band of MPUG_054's batched trial
     * division, within which the cost rises linearly
     */
    static const uint target[] = {
        3, 5, 7, 11, 13, 17, 23, 31, 47, 101, 211, 503, 997, 1009, 2003,
        3989, 4001, 8009, 15991, 16001, 24001, 31991, 32003, 48017, 63997,
        64007
    };
    gmp_randstate_t rs;
    gmp_randinit_default(rs);
    gmp_randseed_ui(rs, 31337 + bits);
    mpz_t m;
    mpz_init(m);
    uint last = 0;
    double *tms = malloc(count * sizeof(double));
    double *tps = malloc(count * sizeof(double));
    double *txs = malloc(count * sizeof(double));
    /* the base for extra: a factor at the first trial prime, which costs
     * no extra scanning, and leaves the same work to follow
     */
    double base = 0;
    /* warm up: the first tests pay one-off setup */
    for (uint i = 0; i < 100; ++i) {
        mb_random(m, rs, bits, 3);
        test_multi_reset();
        test_multi_append(m, 0, t, 1);
    }
    for (uint ti = 0; ti < sizeof(target) / sizeof(target[0]); ++ti) {
        uint p = target[ti];
        uint pb = (uint)ceil(a * log2(p));
        for (uint i = 0; i < count; ++i) {
            /* p^a times a cofactor with no factor up to p */
            mb_random(m, rs, bits > pb + 16 ? bits - pb : 16, p);
            for (uint j = 0; j < a; ++j)
                mpz_mul_ui(m, m, p);
            test_multi_reset();
            double t0 = mb_now();
            bool ok = test_multi_append(m, 0, t, 1);
            tms[i] = mb_now() - t0;
            if (ok)
                goto done;
            mb_random(m, rs, bits > pb + 16 ? bits - (uint)log2(p) : 16, p);
            mpz_mul_ui(m, m, p);
            test_multi_reset();
            t0 = mb_now();
            ok = test_prime_append(m, 0) && test_prime_run(0) == 0;
            tps[i] = mb_now() - t0;
            if (t2) {
                /* p times a cofactor with no factor up to the largest
                 * limit: prep finds p, continues, and fails or passes as
                 * for the base
                 */
                mb_random(m, rs, bits > (uint)log2(p) + 16
                        ? bits - (uint)log2(p) : 16, 64007);
                mpz_mul_ui(m, m, p);
                test_multi_reset();
                t0 = mb_now();
                test_multi_append(m, 0, t2, 1);
                txs[i] = mb_now() - t0;
            }
        }
        printf("S %u %u %.4f %.4f", bits, p, 1e6 * mb_trimmed(tms, count),
                1e6 * mb_trimmed(tps, count));
        if (t2) {
            double tx = mb_trimmed(txs, count);
            if (ti == 0)
                base = tx;
            printf(" %.4f", 1e6 * (tx - base));
        }
        printf("\n");
        last = p;
    }
  done:
    printf("L %u %u\n", bits, last);
    free(tms);
    free(tps);
    free(txs);
    mpz_clear(m);
    gmp_randclear(rs);
}

/* "ladder,bits,count,F[,alpha]" (see multibench()): the
 * factoring ladder of tau_multi_run() on count composites of the given
 * bits with no factor up to F, each alone and stopping at the first
 * factor found, for rows "G bits rung reach us hit fbits cprime": the
 * fraction of inputs reaching the rung, the mean cost of an attempt
 * there (including splitting a composite factor), the fraction of
 * attempts finding a factor, and for those the mean bits of the prime
 * factor and the fraction whose cofactor is prime. A last row
 * "G bits 0 none" gives the fraction for which no rung found a factor.
 *
 * Without alpha, the inputs are random. With alpha, they are built from
 * their factors (mbl_build()), with the smallest factor's size taken
 * from its true distribution with probability alpha, else uniformly in
 * log, and each weighted by the ratio of the densities: the same
 * expected results, but with far more of the inputs whose smallest
 * factor is large, which alone reach the costly high rungs.
 */
#define MBL_RUNGS 64   /* at most, as the rung mask is a ulong */
typedef struct {
    double reach[MBL_RUNGS], cost[MBL_RUNGS], hit[MBL_RUNGS],
            fbits[MBL_RUNGS], cprime[MBL_RUNGS];
    double w, none;
} t_mbl;

/* QS (rung MBL_QS) always finds a factor, at a cost that depends only
 * on the size, but that is large: 12s at 207 bits, 39s at 223, 387s at
 * 255. So for built inputs, whose factors are known, it is run on at
 * most MBL_QSCAP of them per size, the rest charged the mean of those,
 * and credited with finding the smallest factor; the mock takes its
 * cost from the "qs" bench's rows instead where it has them. The rungs
 * after it are then never reached (QS failing was 5% at 144 bits).
 */
#define MBL_QS 24
#define MBL_QSCAP 1
typedef struct {
    uint n, cap;
    double t;
    uint fbits;     /* of the input's smallest factor, if known */
    bool cprime;    /* whether the rest is prime, if known */
} t_mblqs;

/* run the ladder on tm->n alone to the first factor, adding to st
 * with weight w
 */
static void mbl_run(t_mbl *st, t_tm *tm, mpz_t cof, double w, t_mblqs *qs) {
    uint bits = mpz_sizeinbase(tm->n, 2);
    tm->t = 4;
    tm->e = 1;
    tm->vi = 0;
    tm->B1 = 0;
    tm->state = TM_INIT;
    tm->bits = tm_rungmask(bits);
    st->w += w;
    for (uint i = TM_INIT; i < tm_rungs(); ++i) {
        if (!(tm->bits & (1UL << i)))
            continue;
        st->reach[i] += w;
        if (i == MBL_QS && qs && qs->fbits && qs->n >= qs->cap) {
            st->cost[i] += w * qs->t / qs->n;
            st->hit[i] += w;
            st->fbits[i] += w * qs->fbits;
            if (qs->cprime)
                st->cprime[i] += w;
            return;
        }
        double t0 = mb_now();
        bool ok = tm_rung(i, tm);
        mpz_t *f = ok ? tm_factor(tm) : NULL;
        double dt = mb_now() - t0;
        st->cost[i] += w * dt;
        if (i == MBL_QS && qs) {
            ++qs->n;
            qs->t += dt;
        }
        if (!ok)
            continue;
        st->hit[i] += w;
        st->fbits[i] += w * mpz_sizeinbase(*f, 2);
        mpz_set(cof, tm->n);
        while (mpz_divisible_p(cof, *f))
            mpz_divexact(cof, cof, *f);
        if (mpz_cmp_ui(cof, 1) > 0 && _GMP_is_prob_prime(cof))
            st->cprime[i] += w;
        return;
    }
    st->none += w;
}

/* Buchstab's function omega(u) for u >= 1, from u omega(u) = 1 for
 * u <= 2 and (u omega(u))' = omega(u - 1), tabulated at steps of MBB_H:
 * of the integers near x with no prime factor below y = x^(1/u), there
 * are about x omega(u) / ln y per unit
 */
#define MBB_H 0.001
#define MBB_UMAX 64.0
static double *mbb_om = NULL;
static uint mbb_n;
static void mbb_init(void) {
    uint k = (uint)(1 / MBB_H + 0.5);
    mbb_n = (uint)((MBB_UMAX - 1) / MBB_H) + 2;
    mbb_om = malloc(mbb_n * sizeof(double));
    double uw = 1;
    for (uint i = 0; i < mbb_n; ++i) {
        if (i > k)
            uw += MBB_H * (mbb_om[i - 1 - k] + mbb_om[i - k]) / 2;
        mbb_om[i] = uw / (1 + i * MBB_H);
    }
}
static double mbb_omega(double u) {
    if (u < 1)
        return 0;
    double x = (u - 1) / MBB_H;
    uint i = (uint)x;
    if (i + 1 >= mbb_n)
        return mbb_om[mbb_n - 1];
    return mbb_om[i] + (x - i) * (mbb_om[i + 1] - mbb_om[i]);
}

/* The density of the log s of the smallest prime factor of a composite
 * near e^L with no prime factor below e^a: the integers with smallest
 * factor p are p times one with none below p, and there are about
 * e^s ds / s primes in ds, so it goes as omega((L - s) / s) / s^2 for
 * a <= s <= L / 2. Tabulated as a cumulative distribution over MBB_NS
 * steps, for sampling.
 */
#define MBB_NS 2000
typedef struct {
    double a, b, L, cdf[MBB_NS + 1];
} t_mbbs;
static void mbb_sinit(t_mbbs *d, double L, double a) {
    d->L = L;
    d->a = a;
    d->b = L / 2;
    double h = (d->b - d->a) / MBB_NS, prev = 0;
    d->cdf[0] = 0;
    for (uint i = 1; i <= MBB_NS; ++i) {
        double s = d->a + i * h;
        double f = mbb_omega((L - s) / s) / (s * s);
        d->cdf[i] = d->cdf[i - 1] + h * (prev + f) / 2;
        prev = f;
    }
}
/* the density at s, normalized */
static double mbb_sdens(t_mbbs *d, double s) {
    return mbb_omega((d->L - s) / s) / (s * s) / d->cdf[MBB_NS];
}
static double mbb_sample(t_mbbs *d, double r) {
    double v = r * d->cdf[MBB_NS];
    uint lo = 0, hi = MBB_NS;
    while (hi - lo > 1) {
        uint mid = (lo + hi) / 2;
        if (d->cdf[mid] < v)
            lo = mid;
        else
            hi = mid;
    }
    double c0 = d->cdf[lo], c1 = d->cdf[hi];
    double f = (c1 > c0) ? (v - c0) / (c1 - c0) : 0;
    return d->a + (lo + f) * (d->b - d->a) / MBB_NS;
}

/* a random prime of about e^s */
static void mbb_prime(mpz_t p, gmp_randstate_t rs, double s, mpz_t tmp) {
    mpz_set_d(p, exp(s));
    uint b = mpz_sizeinbase(p, 2);
    if (b > 52) {
        mpz_urandomb(tmp, rs, b - 52);
        mpz_add(p, p, tmp);
    }
    _GMP_next_prime(p);
}

static double mbb_uniform(gmp_randstate_t rs) {
    return (double)gmp_urandomb_ui(rs, 53) / 9007199254740992.0;
}

/* Multiply into n a random integer near e^L with no prime factor below
 * e^a, factor by factor: prime with chance 1 / (u omega(u)), u = L / a,
 * else its smallest factor from the density above and the rest likewise.
 * Returns the number of prime factors.
 */
static uint mbb_rough(
    mpz_t n, gmp_randstate_t rs, double L, double a, mpz_t p, mpz_t tmp
) {
    uint np = 0;
    while (1) {
        double u = L / a;
        ++np;
        if (u < 2 || mbb_uniform(rs) * u * mbb_omega(u) < 1) {
            mbb_prime(p, rs, L, tmp);
            mpz_mul(n, n, p);
            return np;
        }
        t_mbbs d;
        mbb_sinit(&d, L, a);
        double s = mbb_sample(&d, mbb_uniform(rs));
        mbb_prime(p, rs, s, tmp);
        mpz_mul(n, n, p);
        double ls = log(mpz_get_d(p));
        L -= ls;
        a = ls;
    }
}

/* "qs,bits,count": the cost of QS (rung MBL_QS) alone on count
 * products of two random primes of about half the bits each, for rows
 * "Q bits us fail". Its parameters step with the decimal digits of the
 * input (see _GMP_simpqs()), so the costs do too.
 */
static void mb_qs(uint bits, uint count) {
    gmp_randstate_t rs;
    gmp_randinit_default(rs);
    gmp_randseed_ui(rs, 40503UL + 11 * bits);
    mpz_t p;
    mpz_init(p);
    t_tm tm;
    mpz_init(tm.n);
    double t = 0;
    uint fail = 0;
    for (uint c = 0; c < count; ++c) {
        do {
            mpz_urandomb(p, rs, bits / 2 - 1);
            mpz_setbit(p, bits / 2 - 1);
            _GMP_next_prime(p);
            mpz_urandomb(tm.n, rs, bits - bits / 2 - 1);
            mpz_setbit(tm.n, bits - bits / 2 - 1);
            mpz_setbit(tm.n, bits - bits / 2 - 2);
            _GMP_next_prime(tm.n);
            mpz_mul(tm.n, tm.n, p);
        } while (mpz_sizeinbase(tm.n, 2) != bits);
        tm.t = 4;
        tm.e = 1;
        tm.B1 = 0;
        double t0 = mb_now();
        if (!tm_rung(MBL_QS, &tm))
            ++fail;
        t += mb_now() - t0;
    }
    printf("Q %u %.1f %.4f\n", bits, 1e6 * t / count, (double)fail / count);
    mpz_clear(p);
    mpz_clear(tm.n);
    gmp_randclear(rs);
}

static void mb_ladder(uint bits, uint count, uint F, double alpha) {
    gmp_randstate_t rs;
    gmp_randinit_default(rs);
    gmp_randseed_ui(rs, 2654435761UL + 7 * bits);
    mpz_t prim, g, cof, p, tmp;
    mpz_init(prim);
    mpz_init(g);
    mpz_init(cof);
    mpz_init(p);
    mpz_init(tmp);
    mpz_primorial_ui(prim, F);
    t_mbl st;
    memset(&st, 0, sizeof(st));
    t_tm tm;
    mpz_init(tm.n);
    tm.tlim = F;
    if (alpha > 0 && !mbb_om)
        mbb_init();
    t_mblqs qs = { .n = 0, .cap = MBL_QSCAP, .t = 0 };
    for (uint c = 0; c < count; ++c) {
        double w = 1;
        qs.fbits = 0;
        if (alpha > 0) {
            /* a composite of about bits bits: its smallest factor from
             * the mixture, the rest with no factor below that
             */
            double L = log(2) * (bits - 1) + log(1 + mbb_uniform(rs));
            t_mbbs d;
            mbb_sinit(&d, L, log(F));
            do {
                double s = (mbb_uniform(rs) < alpha)
                        ? mbb_sample(&d, mbb_uniform(rs))
                        : d.a + mbb_uniform(rs) * (d.b - d.a);
                mbb_prime(p, rs, s, tmp);
                double ls = log(mpz_get_d(p));
                if (ls > d.b)
                    continue;
                double f = mbb_sdens(&d, ls);
                w = f / (alpha * f + (1 - alpha) / (d.b - d.a));
                mpz_set(tm.n, p);
                qs.fbits = mpz_sizeinbase(p, 2);
                qs.cprime = mbb_rough(tm.n, rs, L - ls, ls, p, tmp) == 1;
            } while (mpz_perfect_power_p(tm.n));
        } else {
            do {
                mpz_urandomb(tm.n, rs, bits - 1);
                mpz_setbit(tm.n, bits - 1);
                mpz_gcd(g, prim, tm.n);
            } while (mpz_cmp_ui(g, 1) != 0 || mpz_probab_prime_p(tm.n, 1)
                    || mpz_perfect_power_p(tm.n));
        }
        mbl_run(&st, &tm, cof, w, &qs);
    }
    for (uint i = TM_INIT; i < tm_rungs(); ++i)
        if (st.reach[i] > 0)
            printf("G %u %u %.6f %.4f %.6f %.2f %.4f\n", bits, i,
                    st.reach[i] / st.w, 1e6 * st.cost[i] / st.reach[i],
                    st.hit[i] / st.reach[i],
                    st.hit[i] ? st.fbits[i] / st.hit[i] : 0,
                    st.hit[i] ? st.cprime[i] / st.hit[i] : 0);
    printf("G %u 0 %.6f\n", bits, st.none / st.w);
    mpz_clear(tm.n);
    mpz_clear(prim);
    mpz_clear(g);
    mpz_clear(cof);
    mpz_clear(p);
    mpz_clear(tmp);
    gmp_randclear(rs);
}

void multibench(char *spec) {
    /* start clean after any progress line */
    printf("\n");
    if (strncmp(spec, "prime,", 6) == 0)
        return mb_prime(spec + 6);
    if (strncmp(spec, "scan,", 5) == 0)
        return mb_scan(spec + 5);
    if (strncmp(spec, "ladder,", 7) == 0) {
        uint bits, count, F;
        double alpha = 0;
        if (sscanf(spec + 7, "%u,%u,%u,%lf", &bits, &count, &F, &alpha) < 3)
            fail("MULTIBENCH: expected ladder,bits,count,F[,alpha]");
        return mb_ladder(bits, count, F, alpha);
    }
    if (strncmp(spec, "qs,", 3) == 0) {
        uint bits, count;
        if (sscanf(spec + 3, "%u,%u", &bits, &count) != 2)
            fail("MULTIBENCH: expected qs,bits,count");
        return mb_qs(bits, count);
    }
    uint bits, t, count, F, e = 1;
    ulong seed = 1;
    if (sscanf(spec, "%u,%u,%u,%u,%lu,%u",
            &bits, &t, &count, &F, &seed, &e) < 4)
        fail("MULTIBENCH: expected bits,t,count,F[,seed[,e]]");
    if (t == 0 || n % t)
        fail("MULTIBENCH: t=%u does not divide n=%u", t, n);
    gmp_randstate_t rs;
    gmp_randinit_default(rs);
    gmp_randseed_ui(rs, seed * 2654435761UL + 1);
    mpz_t m;
    mpz_init(m);
    ulong nfail = 0, ndecided = 0, npending = 0, npass = 0;
    double tprep_fail = 0, tprep_ok = 0, trun = 0;
    for (uint i = 0; i < count; ++i) {
        mb_random(m, rs, bits, F);
        test_multi_reset();
        double t0 = mb_now();
        bool ok = test_multi_append(m, 0, t, e);
        double t1 = mb_now();
        if (!ok) {
            ++nfail;
            tprep_fail += t1 - t0;
            continue;
        }
        tprep_ok += t1 - t0;
        if (taum[0].state == 0) {
            ++ndecided;
            continue;
        }
        ++npending;
        uint remain = test_multi_run(NULL);
        trun += mb_now() - t1;
        if (remain == 0)
            ++npass;
    }
    printf("MULTIBENCH n=%u bits=%u t=%u e=%u F=%u count=%u:"
            " fail %.4f decided %.4f pending %.4f (pass %.4f); prep %.3fus (fail %.3fus, ok %.3fus);"
            " run %.3fus per pending\n",
            n, bits, t, e, F, count, (double)nfail / count,
            (double)ndecided / count, (double)npending / count,
            npending ? (double)npass / npending : 0,
            1e6 * (tprep_fail + tprep_ok) / count,
            nfail ? 1e6 * tprep_fail / nfail : 0,
            (count - nfail) ? 1e6 * tprep_ok / (count - nfail) : 0,
            npending ? 1e6 * trun / npending : 0);
    mpz_clear(m);
    gmp_randclear(rs);
}
#endif
