/* rungbench.c - successor to ftest.c (throwaway testing code, per hvds -
 * freely rewritten/renamed here for the walk_v() cost-model work).
 *
 * Benchmarks ONE named tmfa[] rung (see coultau.c's tmf_2..tmf_42) across
 * MANY independently-generated hard inputs, all within a single process -
 * unlike ftest.c, which paid a fresh _GMP_init()/etc startup cost on every
 * invocation. That mattered once we started calling this in a loop across
 * many (rung, bitsize) cells.
 *
 * Each trial generates n = p*q for random primes p, q, with p and q's
 * bit-lengths independently controllable (see smallbits below) - this
 * matters because cost and success-probability are driven by DIFFERENT
 * things: cost scales with n's total size (the modular arithmetic is done
 * mod n, regardless of factor structure), but a method's chance of
 * actually finding a factor (for ECM/P-1 specifically) depends primarily
 * on the SIZE OF THE SMALLEST FACTOR relative to the method's own
 * parameters (roughly a Dickman's-rho smoothness-probability question,
 * the same theory behind standard optimal-B1-by-factor-size tables) -
 * NOT on n's overall size. Varying total bits alone (as an earlier version
 * of this tool did) conflates the two effects. To separate them: fix
 * <bits> (drives cost) and sweep <smallbits> (drives success probability)
 * independently.
 *
 * n's composite structure also matters for the "would tau_multi_prep()
 * even hand this to the escalation ladder" question, but that's a
 * separate, tau-dependent question this tool doesn't address - see
 * WalkCost.pm's "known gaps" for where that fits in.
 *
 * Usage:
 *   rungbench <rung> <bits> <count> [seed_base] [B1] [smallbits]
 *
 *   rung      tmfa[] index to test (e.g. 31 = p-1 B1=5M/B2=100M)
 *   bits      target TOTAL bit-length of n = p*q (drives cost)
 *   count     number of independent trials
 *   seed_base starting seed for the factoring method's own randomness
 *             (incremented per trial; default 1) - input generation uses
 *             a derived-but-separate seed so runs stay reproducible
 *   B1        optional override for methods that read tm->B1 as a
 *             multiplier base (tmf_25/27/28/32/33-42) - matches whichever
 *             tmf_16..tmf_23 variant is enabled in the bracket you're
 *             modelling; see coultau.c's tmfb[] table. Defaults to 160000
 *             (tmf_22's own value) if not given.
 *   smallbits optional: size of the SMALLER factor p (the other factor q
 *             gets bits-smallbits). Defaults to bits/2 (balanced - the
 *             hardest case, useful for pure cost measurement). Set this
 *             explicitly, holding bits fixed, to sweep SUCCESS
 *             PROBABILITY as a function of factor size at constant cost
 *             context.
 *
 * Output: one line per trial (success/ns), then a summary line with
 * n, n_success, mean_ns (all trials) and mean_ns (failures only - the
 * more useful number for modelling typical escalation cost, since a
 * lucky early success understates what a full failed attempt costs).
 */
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>
#include <time.h>

#include "coul.h"
#include "coultau.h"

#include "factor.h"
#include "gmp_main.h"
#include "utility.h"
#include "primality.h"

extern bool (*const tmfa[])(t_tm *tm);
extern mpz_t *tm_factor(t_tm *tm);
t_divisors *divisors = NULL;
double t0 = 0;

/* not used for timing (we use clock_gettime below), but fail()/other
 * linked code may reference these */
double seconds(double t1) { return t1 - t0; }

void fail(char *format, ...) {
    va_list ap;
    va_start(ap, format);
    gmp_vfprintf(stderr, format, ap);
    fprintf(stderr, "\n");
    va_end(ap);
    exit(1);
}

static inline double elapsed_ns(struct timespec *t0, struct timespec *t1) {
    return (double)(t1->tv_sec - t0->tv_sec) * 1e9
         + (double)(t1->tv_nsec - t0->tv_nsec);
}

int main(int argc, char **argv) {
    if (argc < 4) {
        fprintf(stderr,
            "Usage: %s <rung> <bits> <count> [seed_base] [B1] [smallbits] [mode]\n"
            "  mode: pq (default) - existing constructed-semiprime input,\n"
            "        multiplicity is ALWAYS exactly 1 by construction (p,q\n"
            "        distinct independent primes) - use for success-rate\n"
            "        calibration, NOT for multiplicity-distribution work.\n"
            "        rand - genuine random integer, filtered to remove\n"
            "        factors below the roughness threshold (matching what\n"
            "        real trial division would already have stripped) and\n"
            "        rejected if prime (real escalation candidates are\n"
            "        guaranteed composite) - use this for multiplicity\n"
            "        distribution measurement. smallbits is ignored in\n"
            "        this mode.\n",
            argv[0]);
        return 1;
    }
    uint rung = strtoul(argv[1], NULL, 0);
    uint bits = strtoul(argv[2], NULL, 0);
    uint count = strtoul(argv[3], NULL, 0);
    ulong seed_base = (argc > 4) ? strtoul(argv[4], NULL, 10) : 1;
    ulong B1 = (argc > 5) ? strtoul(argv[5], NULL, 10) : 160000;
    uint smallbits = (argc > 6) ? strtoul(argv[6], NULL, 10) : bits / 2;
    int rand_mode = (argc > 7) && !strcmp(argv[7], "rand");
    if (!rand_mode && (smallbits == 0 || smallbits >= bits)) {
        fprintf(stderr, "smallbits must be > 0 and < bits\n");
        return 1;
    }

    _GMP_init();
    set_verbose_level(0);
    init_tau(0, 0);
    alloc_taum(1);
    t_tm *tm = &taum[0];
    tm->B1 = B1;
    tm->t = 4;
    tm->e = 1;
    tm->bits = 1UL << rung;

    /* private randstate for input generation only - never touches the
     * factoring methods' own _randstate */
    gmp_randstate_t gen_rs;
    gmp_randinit_default(gen_rs);
    gmp_randseed_ui(gen_rs, seed_base * 2654435761UL + 12345);

    mpz_t p, q, orig_n;
    mpz_init(p);
    mpz_init(q);
    mpz_init(orig_n);

    /* roughness filter for rand mode - matches tau_multi_prep()'s own
     * trial division under MPUG_054 (tlim = 64007^2, primes tested up
     * to 64007). A candidate reaching real escalation has, by
     * construction, already survived this - testing against inputs
     * that could still have small factors wouldn't represent what
     * this rung actually sees. */
    static const ulong SMALL_PRIMES[] = {
        2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,
        101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,
        191,193,197,199 /* ...continuing far enough for a reasonable filter;
        a full sieve to 64007 would need ~6400 primes, more than is worth
        hardcoding here - this partial list catches the overwhelming
        majority of non-rough candidates cheaply. Full fidelity to the
        real 64007 threshold isn't essential for THIS measurement: we
        only need candidates the target rung might plausibly be tested
        against, not literally identical to real tau_multi_prep output. */
    };
    #define N_SMALL_PRIMES (sizeof(SMALL_PRIMES)/sizeof(SMALL_PRIMES[0]))

    uint n_success = 0;
    double sum_ns_all = 0, sum_ns_fail = 0;
    double min_ns_fail = -1, max_ns_fail = 0;
    uint mult_hist[16] = {0};   /* mult_hist[k] = count of successes with
                                   multiplicity k+1 (index 0 = mult 1) */
    uint mult_overflow = 0;     /* multiplicity >= 16, shouldn't happen
                                    but tracked rather than silently
                                    miscounted if it somehow does */

    uint i = 0, attempts = 0;
    while (i < count) {
        ++attempts;
        if (rand_mode) {
            /* genuine random integer, rejection-filtered for
             * roughness and compositeness */
            mpz_urandomb(tm->n, gen_rs, bits);
            mpz_setbit(tm->n, bits - 1);
            mpz_setbit(tm->n, 0);
            int rough = 1;
            for (uint k = 0; k < N_SMALL_PRIMES; ++k) {
                if (mpz_divisible_ui_p(tm->n, SMALL_PRIMES[k])) {
                    rough = 0;
                    break;
                }
            }
            if (!rough) continue;
            if (mpz_probab_prime_p(tm->n, 25)) continue;
        } else {
            uint rest = bits - smallbits;
            mpz_urandomb(p, gen_rs, smallbits);
            mpz_setbit(p, smallbits - 1);
            mpz_setbit(p, 0);
            mpz_nextprime(p, p);
            mpz_urandomb(q, gen_rs, rest);
            mpz_setbit(q, rest - 1);
            mpz_setbit(q, 0);
            mpz_nextprime(q, q);
            mpz_mul(tm->n, p, q);
        }

        clear_randstate();
        init_randstate(seed_base + i);

        uint n_bits = mpz_sizeinbase(tm->n, 2);
        mpz_set(orig_n, tm->n);   /* save before the call - the rung
            function itself overwrites tm->n with the found factor on
            success (same reason ftest.c's old bits= bug existed) */

        struct timespec ts0, ts1;
        clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &ts0);
        bool r = (*tmfa[rung])(tm);
        clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &ts1);
        double ns = elapsed_ns(&ts0, &ts1);

        sum_ns_all += ns;
        int mult = 0;
        uint factor_bits = 0;
        if (r) {
            ++n_success;
            /* replicate tau_multi_run()'s own multiplicity-counting
             * exactly (coultau.c ~line 1180), but against our saved
             * copy of n rather than the now-overwritten tm->n */
            mpz_t *f = tm_factor(tm);
            factor_bits = mpz_sizeinbase(*f, 2);
            while (mpz_divisible_p(orig_n, *f)) {
                ++mult;
                mpz_divexact(orig_n, orig_n, *f);
            }
            if (mult >= 1 && mult <= 16)
                ++mult_hist[mult - 1];
            else
                ++mult_overflow;
        } else {
            sum_ns_fail += ns;
            if (min_ns_fail < 0 || ns < min_ns_fail) min_ns_fail = ns;
            if (ns > max_ns_fail) max_ns_fail = ns;
        }
        gmp_printf("trial %u: bits=%u smallbits=%u %s mult=%d "
            "factor_bits=%u ns=%.0f\n", i,
            n_bits, smallbits, r ? "success" : "fail", mult, factor_bits, ns);
        ++i;
    }

    uint n_fail = count - n_success;
    gmp_printf("SUMMARY rung=%u bits=%u smallbits=%u mode=%s n=%u success=%u "
        "fail=%u attempts=%u mean_ns_all=%.0f mean_ns_fail=%.0f "
        "min_ns_fail=%.0f max_ns_fail=%.0f\n",
        rung, bits, smallbits, rand_mode ? "rand" : "pq", count, n_success,
        n_fail, attempts,
        count ? sum_ns_all / count : 0,
        n_fail ? sum_ns_fail / n_fail : 0,
        n_fail ? min_ns_fail : 0,
        n_fail ? max_ns_fail : 0);
    if (n_success) {
        gmp_printf("MULT_HIST rung=%u bits=%u", rung, bits);
        for (int k = 0; k < 16; ++k)
            if (mult_hist[k])
                gmp_printf(" mult%d=%u", k + 1, mult_hist[k]);
        if (mult_overflow)
            gmp_printf(" mult_overflow=%u", mult_overflow);
        gmp_printf("\n");
    }

    return 0;
}
