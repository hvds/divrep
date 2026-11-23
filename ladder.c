/* ladder: time the factoring ladder of tau_multi_run() (see coultau.c)
 * for the rows of the cost table that describe it (see multibench-table),
 * outside pcoul, so that they can be remade after a change to MPUGMP or
 * msiqs alone.
 *
 *   ladder [-Lc<GHz>] [-o<flake>] Q <sizes> <count>
 *   ladder [-Lc<GHz>] [-o<flake>] [-F<F>] G <sizes> <count> [<alpha>]
 *   ladder fit <from> <to>
 *
 * <sizes> is <bits>, or <from>:<to>[:<step>] for every step (default 1)
 * bits from <from> to <to>.
 *
 * Q times QS alone (the QS rung that applies at each size) on count
 * products of two random primes of about half the bits each, giving
 * a row "Q bits us fail" per size.
 *
 * G runs the ladder on count composites of each size with no factor up
 * to F (default 64007, the trial division limit of tau_multi_prep()),
 * each alone and stopping at the first factor found, giving rows
 * "G bits rung reach us hit fbits cprime": the fraction of inputs
 * reaching the rung, the mean cost of an attempt there (including
 * splitting a composite factor), the fraction of attempts finding a
 * factor, and for those the mean bits of the prime factor and the
 * fraction whose cofactor is prime. A last row "G bits 0 none" gives the
 * fraction for which no rung found a factor. Without alpha the inputs
 * are random; with alpha they are built from their factors, the
 * smallest taken from its true distribution with probability alpha,
 * else uniformly in log, each weighted by the ratio of the densities:
 * the same expected results, but with far more of the inputs whose
 * smallest factor is large, which alone reach the costly high rungs.
 * Since QS always finds a factor, at a large cost depending on the size
 * alone, with alpha it is run on at most one built input per size, the
 * rest charged the same and credited with finding the smallest factor.
 *
 * Each of Q and G first gives a line "V qs <sha> <unit>" or "V ladder
 * <sha> <unit>" naming the build (as on pcoul's 001 line) and the unit
 * of the times: "CY<GHz>" for user-mode CPU cycles at a reference clock
 * rate (-Lc<GHz>, default 3.6, as for pcoul), else "CPU" for CPU seconds
 * (-Lc0, or if the cycle counter cannot be opened); times are in
 * microseconds of the unit. -o<flake> drops the rungs from QS on for
 * values of more than flake bits, as pcoul's -o<flake> does.
 *
 * fit reads Q rows on stdin and fits log(us) = a + b.bits by least
 * squares to those from <from> to <to> bits, then shows each row with
 * the time the fit predicts for it, so that the fit can be judged on
 * sizes it did not see.
 *
 * Inputs come from a GMP generator seeded by a constant and the size, so
 * that every run tests the same inputs (for one version of GMP); the
 * factoring code takes its randomness from MPU::GMP's ISAAC instead.
 */

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <stdarg.h>
#include <errno.h>
#include <math.h>
#include <time.h>
#ifdef __linux__
#   include <unistd.h>
#   include <sys/syscall.h>
#   include <linux/perf_event.h>
#endif

#include "coul.h"
#include "coultau.h"
#include "gmp_main.h"
#include "primality.h"
#include "utility.h"

/* needed for coultau.c; but not used, since we init_tau(0, flake) */
t_divisors *divisors = NULL;

void fail(char *format, ...) {
    va_list ap;
    va_start(ap, format);
    gmp_vfprintf(stderr, format, ap);
    fprintf(stderr, "\n");
    va_end(ap);
    exit(1);
}

/* Times are user-mode CPU cycles divided by a reference clock rate when
 * the cycle counter is available (as pcoul's, see init_cycles() in
 * coul.c), else CPU seconds.
 */
double cyc_ghz = 3.6;
int cyc_fd = -1;
static double lclock(void) {
#ifdef __linux__
    if (cyc_fd >= 0) {
        ulong v[3];     /* count, time enabled, time running */
        if (read(cyc_fd, v, sizeof(v)) != sizeof(v))
            fail("could not read cycle counter: %s", strerror(errno));
        /* scale up if the counter was multiplexed */
        double cyc = v[2] ? (double)v[0] * v[1] / v[2] : 0;
        return cyc / (cyc_ghz * 1e9);
    }
#endif
    struct timespec ts;
    clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &ts);
    return ts.tv_sec + ts.tv_nsec / 1e9;
}

static void init_cycles(void) {
#ifdef __linux__
    if (cyc_ghz > 0) {
        struct perf_event_attr pe;
        memset(&pe, 0, sizeof(pe));
        pe.type = PERF_TYPE_HARDWARE;
        pe.size = sizeof(pe);
        pe.config = PERF_COUNT_HW_CPU_CYCLES;
        pe.exclude_kernel = 1;
        pe.exclude_hv = 1;
        pe.read_format = PERF_FORMAT_TOTAL_TIME_ENABLED
                | PERF_FORMAT_TOTAL_TIME_RUNNING;
        cyc_fd = syscall(SYS_perf_event_open, &pe, 0, -1, -1, 0);
        if (cyc_fd < 0)
            fprintf(stderr, "cycle counter unavailable (%s),"
                    " times are CPU seconds\n", strerror(errno));
    }
#endif
}

/* The time, less what reading it costs, so that an interval between two
 * reads leaves out the one read's worth it includes.
 */
static double l_gap = -1;
static ulong l_reads = 0;
static inline double lnow(void) {
    if (l_gap < 0) {
        double t0 = lclock(), t1 = t0;
        for (uint i = 0; i < 10000; ++i)
            t1 = lclock();
        l_gap = (t1 - t0) / 10000;
    }
    return lclock() - l_gap * ++l_reads;
}

/* the section stamp: the build as on pcoul's 001 line, and the unit */
static void stamp(const char *section) {
    printf("V %s %s", section, DIVREP_CHANGE);
    if (strcmp(DIVREP_CHANGE, DIVREP_BASE))
        printf("(%s)", DIVREP_BASE);
    if (DIVREP_DIRTY)
        printf("*");
    printf(";%s", MPU_CHANGE);
    if (strcmp(MPU_CHANGE, MPU_BASE))
        printf("(%s)", MPU_BASE);
    if (MPU_DIRTY)
        printf("*");
#ifdef MSIQS_CHANGE
    printf(";%s", MSIQS_CHANGE);
    if (strcmp(MSIQS_CHANGE, MSIQS_BASE))
        printf("(%s)", MSIQS_BASE);
    if (MSIQS_DIRTY)
        printf("*");
#endif
    if (cyc_fd >= 0)
        printf(" CY%g\n", cyc_ghz);
    else
        printf(" CPU\n");
}

/* The QS rung that applies to values of the given bits, or 0 if none
 * (as above the flake size).
 */
static uint qs_rung(uint bits) {
    ulong mask = tm_rungmask(bits);
    for (uint i = TM_INIT; i < tm_rungs(); ++i)
        if (tm_rung_qs(i) && (mask & (1UL << i)))
            return i;
    return 0;
}

/* Q rows: QS alone on count balanced semiprimes of the given bits */
static void time_qs(uint bits, uint count) {
    uint r = qs_rung(bits);
    if (r == 0) {
        fprintf(stderr, "no QS rung at %u bits\n", bits);
        return;
    }
    gmp_randstate_t rs;
    gmp_randinit_default(rs);
    gmp_randseed_ui(rs, 40503UL + 11 * bits);
    mpz_t p;
    mpz_init(p);
    t_tm tm;
    mpz_init(tm.n);
    double t = 0;
    uint failed = 0;
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
        tm.tlim = 0;
        double t0 = lnow();
        if (!tm_rung(r, &tm))
            ++failed;
        t += lnow() - t0;
    }
    printf("Q %u %.1f %.4f\n", bits, 1e6 * t / count, (double)failed / count);
    fflush(stdout);
    mpz_clear(p);
    mpz_clear(tm.n);
    gmp_randclear(rs);
}

/* Buchstab's function omega(u) for u >= 1, from u omega(u) = 1 for
 * u <= 2 and (u omega(u))' = omega(u - 1), tabulated at steps of BU_H:
 * of the integers near x with no prime factor below y = x^(1/u), there
 * are about x omega(u) / ln y per unit.
 */
#define BU_H 0.001
#define BU_UMAX 64.0
static double *bu_om = NULL;
static uint bu_n;
static void bu_init(void) {
    uint k = (uint)(1 / BU_H + 0.5);
    bu_n = (uint)((BU_UMAX - 1) / BU_H) + 2;
    bu_om = malloc(bu_n * sizeof(double));
    double uw = 1;
    for (uint i = 0; i < bu_n; ++i) {
        if (i > k)
            uw += BU_H * (bu_om[i - 1 - k] + bu_om[i - k]) / 2;
        bu_om[i] = uw / (1 + i * BU_H);
    }
}
static double bu_omega(double u) {
    if (u < 1)
        return 0;
    double x = (u - 1) / BU_H;
    uint i = (uint)x;
    if (i + 1 >= bu_n)
        return bu_om[bu_n - 1];
    return bu_om[i] + (x - i) * (bu_om[i + 1] - bu_om[i]);
}

/* The density of the log s of the smallest prime factor of a composite
 * near e^L with no prime factor below e^a: the integers with smallest
 * factor p are p times one with none below p, and there are about
 * e^s ds / s primes in ds, so it goes as omega((L - s) / s) / s^2 for
 * a <= s <= L / 2. Tabulated as a cumulative distribution over BU_NS
 * steps, for sampling.
 */
#define BU_NS 2000
typedef struct {
    double a, b, L, cdf[BU_NS + 1];
} t_bus;
static void bus_init(t_bus *d, double L, double a) {
    d->L = L;
    d->a = a;
    d->b = L / 2;
    double h = (d->b - d->a) / BU_NS, prev = 0;
    d->cdf[0] = 0;
    for (uint i = 1; i <= BU_NS; ++i) {
        double s = d->a + i * h;
        double f = bu_omega((L - s) / s) / (s * s);
        d->cdf[i] = d->cdf[i - 1] + h * (prev + f) / 2;
        prev = f;
    }
}
/* the density at s, normalized */
static double bus_dens(t_bus *d, double s) {
    return bu_omega((d->L - s) / s) / (s * s) / d->cdf[BU_NS];
}
static double bus_sample(t_bus *d, double r) {
    double v = r * d->cdf[BU_NS];
    uint lo = 0, hi = BU_NS;
    while (hi - lo > 1) {
        uint mid = (lo + hi) / 2;
        if (d->cdf[mid] < v)
            lo = mid;
        else
            hi = mid;
    }
    double c0 = d->cdf[lo], c1 = d->cdf[hi];
    double f = (c1 > c0) ? (v - c0) / (c1 - c0) : 0;
    return d->a + (lo + f) * (d->b - d->a) / BU_NS;
}

/* a random prime of about e^s */
static void bu_prime(mpz_t p, gmp_randstate_t rs, double s, mpz_t tmp) {
    mpz_set_d(p, exp(s));
    uint b = mpz_sizeinbase(p, 2);
    if (b > 52) {
        mpz_urandomb(tmp, rs, b - 52);
        mpz_add(p, p, tmp);
    }
    _GMP_next_prime(p);
}

static double bu_uniform(gmp_randstate_t rs) {
    return (double)gmp_urandomb_ui(rs, 53) / 9007199254740992.0;
}

/* Multiply into n a random integer near e^L with no prime factor below
 * e^a, factor by factor: prime with chance 1 / (u omega(u)), u = L / a,
 * else its smallest factor from the density above and the rest likewise.
 * Returns the number of prime factors.
 */
static uint bu_rough(
    mpz_t n, gmp_randstate_t rs, double L, double a, mpz_t p, mpz_t tmp
) {
    uint np = 0;
    while (1) {
        double u = L / a;
        ++np;
        if (u < 2 || bu_uniform(rs) * u * bu_omega(u) < 1) {
            bu_prime(p, rs, L, tmp);
            mpz_mul(n, n, p);
            return np;
        }
        t_bus d;
        bus_init(&d, L, a);
        double s = bus_sample(&d, bu_uniform(rs));
        bu_prime(p, rs, s, tmp);
        mpz_mul(n, n, p);
        double ls = log(mpz_get_d(p));
        L -= ls;
        a = ls;
    }
}

#define MAX_RUNGS 64    /* at most, as the rung mask is a ulong */
typedef struct {
    double reach[MAX_RUNGS], cost[MAX_RUNGS], hit[MAX_RUNGS],
            fbits[MAX_RUNGS], cprime[MAX_RUNGS];
    double w, none;
} t_lst;

/* QS charged without running it, for built inputs (see time_ladder()) */
#define QS_CAP 1
typedef struct {
    uint n, cap;
    double t;
    uint fbits;     /* of the input's smallest factor, if known */
    bool cprime;    /* whether the rest is prime, if known */
} t_lqs;

/* Run the ladder on tm->n alone to the first factor, adding to st
 * with weight w.
 */
static void ladder_run(t_lst *st, t_tm *tm, mpz_t cof, double w, t_lqs *qs) {
    uint bits = mpz_sizeinbase(tm->n, 2);
    tm->t = 4;
    tm->e = 1;
    tm->vi = 0;
    tm->state = TM_INIT;
    tm->bits = tm_rungmask(bits);
    tm->missed = 0;
    st->w += w;
    for (uint i = TM_INIT; i < tm_rungs(); ++i) {
        if (!(tm->bits & (1UL << i)))
            continue;
        st->reach[i] += w;
        bool isqs = tm_rung_qs(i);
        if (isqs && qs && qs->fbits && qs->n >= qs->cap) {
            st->cost[i] += w * qs->t / qs->n;
            st->hit[i] += w;
            st->fbits[i] += w * qs->fbits;
            if (qs->cprime)
                st->cprime[i] += w;
            return;
        }
        double t0 = lnow();
        bool ok = tm_rung(i, tm);
        mpz_t *f = ok ? tm_factor(tm) : NULL;
        double dt = lnow() - t0;
        st->cost[i] += w * dt;
        if (isqs && qs) {
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

/* G rows: the ladder on count composites of the given bits with no
 * factor up to F, random or (alpha > 0) built
 */
static void time_ladder(uint bits, uint count, uint F, double alpha) {
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
    t_lst st;
    memset(&st, 0, sizeof(st));
    t_tm tm;
    mpz_init(tm.n);
    tm.tlim = (ulong)F * F;     /* ref TLIM_IS_SQUARE */
    if (alpha > 0 && !bu_om)
        bu_init();
    t_lqs qs = { .n = 0, .cap = QS_CAP, .t = 0 };
    for (uint c = 0; c < count; ++c) {
        double w = 1;
        qs.fbits = 0;
        if (alpha > 0) {
            /* A composite of about bits bits: its smallest factor from
             * the mixture, the rest with no factor below that.
             */
            double L = log(2) * (bits - 1) + log(1 + bu_uniform(rs));
            t_bus d;
            bus_init(&d, L, log(F));
            do {
                double s = (bu_uniform(rs) < alpha)
                        ? bus_sample(&d, bu_uniform(rs))
                        : d.a + bu_uniform(rs) * (d.b - d.a);
                bu_prime(p, rs, s, tmp);
                double ls = log(mpz_get_d(p));
                if (ls > d.b)
                    continue;
                double f = bus_dens(&d, ls);
                w = f / (alpha * f + (1 - alpha) / (d.b - d.a));
                mpz_set(tm.n, p);
                qs.fbits = mpz_sizeinbase(p, 2);
                qs.cprime = bu_rough(tm.n, rs, L - ls, ls, p, tmp) == 1;
            } while (mpz_perfect_power_p(tm.n));
        } else {
            do {
                mpz_urandomb(tm.n, rs, bits - 1);
                mpz_setbit(tm.n, bits - 1);
                mpz_gcd(g, prim, tm.n);
            } while (mpz_cmp_ui(g, 1) != 0 || mpz_probab_prime_p(tm.n, 1)
                    || mpz_perfect_power_p(tm.n));
        }
        ladder_run(&st, &tm, cof, w, &qs);
    }
    for (uint i = TM_INIT; i < tm_rungs(); ++i)
        if (st.reach[i] > 0)
            printf("G %u %u %.6f %.4f %.6f %.2f %.4f\n", bits, i,
                    st.reach[i] / st.w, 1e6 * st.cost[i] / st.reach[i],
                    st.hit[i] / st.reach[i],
                    st.hit[i] ? st.fbits[i] / st.hit[i] : 0,
                    st.hit[i] ? st.cprime[i] / st.hit[i] : 0);
    printf("G %u 0 %.6f\n", bits, st.none / st.w);
    fflush(stdout);
    mpz_clear(tm.n);
    mpz_clear(prim);
    mpz_clear(g);
    mpz_clear(cof);
    mpz_clear(p);
    mpz_clear(tmp);
    gmp_randclear(rs);
}

/* Fit log(us) = a + b.bits to the Q rows on stdin from lo to hi bits,
 * and show each row against the fit.
 */
#define MAX_Q 4096
static void fit_qs(uint lo, uint hi) {
    static uint qbits[MAX_Q];
    static double qus[MAX_Q];
    uint nq = 0;
    char buf[256];
    while (fgets(buf, sizeof(buf), stdin)) {
        uint bits;
        double us;
        if (sscanf(buf, "Q %u %lf", &bits, &us) != 2)
            continue;
        if (nq >= MAX_Q)
            fail("too many Q rows");
        qbits[nq] = bits;
        qus[nq] = us;
        ++nq;
    }
    double sx = 0, sy = 0, sxx = 0, sxy = 0;
    uint n = 0;
    for (uint i = 0; i < nq; ++i) {
        if (qbits[i] < lo || qbits[i] > hi || qus[i] <= 0)
            continue;
        double x = qbits[i], y = log(qus[i]);
        sx += x;
        sy += y;
        sxx += x * x;
        sxy += x * y;
        ++n;
    }
    if (n < 2)
        fail("need at least 2 Q rows from %u to %u bits to fit", lo, hi);
    double b = (n * sxy - sx * sy) / (n * sxx - sx * sx);
    double a = (sy - b * sx) / n;
    double ss = 0;
    for (uint i = 0; i < nq; ++i) {
        if (qbits[i] < lo || qbits[i] > hi || qus[i] <= 0)
            continue;
        double r = log(qus[i]) - (a + b * qbits[i]);
        ss += r * r;
    }
    printf("fit over %u..%u bits (%u rows): log(us) = %.6f + %.6f bits,"
            " doubling every %.2f bits, rms residual %.1f%%\n",
            lo, hi, n, a, b, log(2) / b, 100 * (exp(sqrt(ss / n)) - 1));
    for (uint i = 0; i < nq; ++i) {
        double pred = exp(a + b * qbits[i]);
        printf("%c %u %.1f %.1f %.3f\n",
                (qbits[i] < lo || qbits[i] > hi) ? '*' : ' ',
                qbits[i], qus[i], pred, qus[i] / pred);
    }
}

/* parse <bits> or <from>:<to>[:<step>] */
static void parse_sizes(char *s, uint *from, uint *to, uint *step) {
    char *end;
    *from = strtoul(s, &end, 10);
    *to = *from;
    *step = 1;
    if (*end == ':') {
        *to = strtoul(end + 1, &end, 10);
        if (*end == ':')
            *step = strtoul(end + 1, &end, 10);
    }
    if (*end || *from < 2 || *to < *from || *step == 0)
        fail("bad sizes '%s'", s);
}

static void usage(void) {
    fail("usage: ladder [-Lc<GHz>] [-o<flake>] Q <sizes> <count>\n"
            "       ladder [-Lc<GHz>] [-o<flake>] [-F<F>] G <sizes> <count>"
            " [<alpha>]\n"
            "       ladder fit <from> <to>\n"
            "  <sizes> is <bits> or <from>:<to>[:<step>]");
}

int main(int argc, char **argv) {
    uint flake = 0, F = 64007;
    int arg = 1;
    while (arg < argc && argv[arg][0] == '-') {
        char *s = argv[arg++];
        char *end;
        if (strncmp(s, "-Lc", 3) == 0) {
            cyc_ghz = strtod(&s[3], &end);
            if (end == &s[3] || *end || !(cyc_ghz >= 0))
                fail("bad -Lc value '%s'", s);
        } else if (s[1] == 'o')
            flake = strtoul(&s[2], NULL, 10);
        else if (s[1] == 'F')
            F = strtoul(&s[2], NULL, 10);
        else
            usage();
    }
    if (arg >= argc)
        usage();
    char *mode = argv[arg++];

    if (strcmp(mode, "fit") == 0) {
        if (argc - arg != 2)
            usage();
        fit_qs(strtoul(argv[arg], NULL, 10), strtoul(argv[arg + 1], NULL, 10));
        return 0;
    }

    bool isq = strcmp(mode, "Q") == 0;
    if (!isq && strcmp(mode, "G") != 0)
        usage();
    if (argc - arg < 2 || argc - arg > (isq ? 2 : 3))
        usage();
    uint from, to, step;
    parse_sizes(argv[arg], &from, &to, &step);
    uint count = strtoul(argv[arg + 1], NULL, 10);
    double alpha = (argc - arg > 2) ? strtod(argv[arg + 2], NULL) : 0;
    if (count == 0)
        usage();

    _GMP_init();
    init_tau(0, flake);
    init_cycles();
    stamp(isq ? "qs" : "ladder");
    for (uint bits = from; bits <= to; bits += step) {
        if (isq)
            time_qs(bits, count);
        else if (bits < 64 && (1UL << bits) - 1 <= F)
            fprintf(stderr, "no %u-bit value has no factor up to %u\n",
                    bits, F);
        else
            time_ladder(bits, count, F, alpha);
    }
    done_tau();
    _GMP_destroy();
    return 0;
}
