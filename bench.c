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
 * value (as for a need_prime position or a fixed power's root),
 * "bpsw,bits,count,F" BPSW alone on primes and on composites (mb_bpsw()),
 * "scan,bits,count,t" the cost of tests that fail at a trial prime, and
 * "clock" the cost of reading the clock (mb_clock()). The factoring
 * ladder and QS are timed by a program of their own (see ladder.c).
 * The walk loops' own costs are fitted from -dv2 runs instead (see
 * multibench-table), since a synthetic loop misses too much of them.
 */
/* The time in the unit of reported times (see work_clock()), less what
 * reading it costs, so that an interval between two reads leaves out the
 * one read's worth it includes. A read is a system call, ~0.25us, which
 * is as much as the cheapest tests benched (where the old wall clock,
 * read without one, cost ~0.02us).
 */
static double mb_gap = -1;
static ulong mb_reads = 0;
static inline double mb_now(void) {
    if (mb_gap < 0) {
        double t0 = work_clock(), t1 = t0;
        for (uint i = 0; i < 10000; ++i)
            t1 = work_clock();
        mb_gap = (t1 - t0) / 10000;
    }
    return work_clock() - mb_gap * ++mb_reads;
}

static volatile ulong mb_sink;
/* random integer of the given bits coprime to every prime <= F */
static void mb_random(mpz_t m, gmp_randstate_t rs, uint bits, uint F) {
    static mpz_t prim, g;
    static uint primF = 0;
    /* else every value of these bits is at most F, so none is coprime */
    if (bits < 64 && (1UL << bits) - 1 <= F)
        fail("MULTIBENCH: no %u-bit value has no factor up to %u", bits, F);
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
 * same inputs and on composites with no factor up to 47 ("R bits us us").
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

/* The mean of the lowest 95% of count times, discarding outliers such as
 * interrupted measurements.
 */
static double mb_trimmed(double *v, uint count) {
    qsort(v, count, sizeof(double), mb_dcmp);
    uint keep = count - count / 20;
    double sum = 0;
    for (uint i = 0; i < keep; ++i)
        sum += v[i];
    return sum / keep;
}

/* Print a D row (see coulcost.c) for count times of the series name at
 * the given bits: their count, mean and standard deviation in us, over
 * the lowest 98%, discarding outliers such as interrupted measurements.
 */
static void mb_drow(const char *name, uint bits, double *v, uint count) {
    qsort(v, count, sizeof(double), mb_dcmp);
    uint keep = count - count / 50;
    double sum = 0, ss = 0;
    for (uint i = 0; i < keep; ++i)
        sum += v[i];
    double mean = sum / keep;
    for (uint i = 0; i < keep; ++i)
        ss += (v[i] - mean) * (v[i] - mean);
    printf("D %s %u %u %.5f %.5f\n", name, bits, keep, 1e6 * mean,
            (keep > 1) ? 1e6 * sqrt(ss / (keep - 1)) : 0);
}

/* "bpsw,bits,count,F": BPSW alone, as tau_prime_run() makes it, timed
 * on count primes of the given bits and on count composites of those
 * bits with no factor up to F, giving the D rows bpsw.prime and
 * bpsw.comp (see mb_drow()). A composite usually fails at the first
 * strong probable prime test, so costs much less than a prime, which
 * pays for the whole test.
 * Such a composite is at least (F + 1)^2. Where that is not below half
 * the range there are none, or too few to find in reasonable time (one
 * draw in tens of thousands at 32 bits, F = 64007), and they are not
 * representative, so no bpsw.comp row is made for those bits.
 */
static void mb_bpsw(char *spec) {
    uint bits, count, F;
    if (sscanf(spec, "%u,%u,%u", &bits, &count, &F) != 3)
        fail("MULTIBENCH: expected bpsw,bits,count,F");
    if (bits < 8)
        fail("MULTIBENCH: bpsw needs at least 8 bits");
    gmp_randstate_t rs;
    gmp_randinit_default(rs);
    gmp_randseed_ui(rs, 2246822519UL + bits);
    mpz_t m;
    mpz_init(m);
    double *v = malloc(count * sizeof(double));
    uint got = 0;
    while (got < count) {
        mpz_urandomb(m, rs, bits - 1);
        mpz_setbit(m, bits - 1);
        mpz_nextprime(m, m);
        if (mpz_sizeinbase(m, 2) != bits)
            continue;
        double t0 = mb_now();
        mb_sink ^= tau_bpsw(m);
        v[got++] = mb_now() - t0;
    }
    mb_drow("bpsw.prime", bits, v, count);
    /* the least composite with no factor up to F, against half the range */
    mpz_set_ui(m, F);
    mpz_add_ui(m, m, 1);
    mpz_mul(m, m, m);
    if (mpz_sizeinbase(m, 2) < bits) {
        got = 0;
        while (got < count) {
            mb_random(m, rs, bits, F);
            if (mpz_probab_prime_p(m, 1))
                continue;
            double t0 = mb_now();
            mb_sink ^= tau_bpsw(m);
            v[got++] = mb_now() - t0;
        }
        mb_drow("bpsw.comp", bits, v, count);
    }
    free(v);
    mpz_clear(m);
    gmp_randclear(rs);
}

/* "scan,bits,count,t[,t2]": the cost of tests that fail at a trial prime
 * p, for a range of p: test_multi() prep for tau t of a value whose first
 * factor is p^a with a + 1 not dividing t, and a prime test of a value
 * whose first factor is p; with t2, also the extra cost to prep for tau
 * t2 of finding a factor p that does not end it (with batched trial
 * division, a linear scan of its band up to p), relative to finding one
 * at the first trial prime; one line "S bits p prep_us prime_us
 * [extra_us]" per p, up to the trial division limit, and then "L bits p"
 * giving that limit (the last p for which prep still finds the factor).
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
    /* Including both ends of each band of MPUG_054's batched trial
     * division, within which the cost rises linearly.
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
    /* The base for extra: a factor at the first trial prime, which costs
     * no extra scanning, and leaves the same work to follow.
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
                 * for the base.
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

/* "clock": what a read of the clock costs, which the -dv6 records the
 * walk section is fitted from carry: each interval timed takes in one
 * read's worth, as does the time outside it (see multibench-table's
 * fit_walks()). The median of 5 runs of 100000 reads, for a line
 * "MULTIBENCH clock read <us>".
 */
static void mb_clock(void) {
    double per[5];
    for (uint i = 0; i < 5; ++i) {
        double t0 = work_clock(), t1 = t0;
        for (uint j = 0; j < 100000; ++j)
            t1 = work_clock();
        per[i] = (t1 - t0) / 100000;
    }
    qsort(per, 5, sizeof(double), mb_dcmp);
    printf("MULTIBENCH clock read %.5fus\n", per[2] * 1e6);
}

void multibench(char *spec) {
    /* start clean after any progress line */
    printf("\n");
    if (strncmp(spec, "prime,", 6) == 0)
        return mb_prime(spec + 6);
    if (strncmp(spec, "bpsw,", 5) == 0)
        return mb_bpsw(spec + 5);
    if (strncmp(spec, "scan,", 5) == 0)
        return mb_scan(spec + 5);
    if (strcmp(spec, "clock") == 0)
        return mb_clock();
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
            " fail %.4f decided %.4f pending %.4f (pass %.4f);"
            " prep %.3fus (fail %.3fus, ok %.3fus);"
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
