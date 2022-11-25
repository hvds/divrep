#include <stdlib.h>
#include <stdio.h>
#include <unistd.h>
#include <stdarg.h>
#include <string.h>
#include <math.h>
#include <errno.h>
#include <signal.h>
#include <time.h>
#include <sys/time.h>
#include <sys/resource.h>
#include <gmp.h>

#include "coul.h"
#include "diag.h"
#include "coultau.h"
#include "prime_iterator.h"

/* from MPUG */
#include "gmp_main.h"
#include "primality.h"

typedef enum {
    lim, temp, uls_temp,
    p2, p2q, v, n32,

    MAX_ZSTASH
} t_zstash;
mpz_t *zstash;
static inline mpz_t *ZP(t_zstash e) { return &zstash[e]; }
#define Z(e) *ZP(e)

ulong pmin, pmax;
prime_iterator ip, iq, ir;
t_divisors *divisors;

uint diag_delay = 1, log_delay = 600;
timer_t diag_timerid, log_timerid;
volatile bool need_work = 0;
bool clock_is_realtime = 0;
struct rusage rusage_buf;
static inline double utime(void) {
    getrusage(RUSAGE_SELF, &rusage_buf);
    return (double)rusage_buf.ru_utime.tv_sec
            + (double)rusage_buf.ru_utime.tv_usec / 1000000;
}

char *rpath = NULL; /* path to log file */
FILE *rfp = NULL;   /* file handle to log file */

void fail(char *format, ...) {
    va_list ap;
    va_start(ap, format);
    vfprintf(stderr, format, ap);
    fprintf(stderr, "\n");
    va_end(ap);
    if (rfp)
        fclose(rfp);
    exit(1);
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

char buf[256];
void do_diag(void) {
    if (need_work & 1) {
        diag(buf);
        need_work &= ~1;
    }
    if (rfp && (need_work & 2)) {
        fprintf(rfp, "305 %s (%.2fs)\n", buf, utime());
        need_work &= ~2;
    }
}

void diag_p(ulong p) {
    sprintf(buf, "%lu", p);
    do_diag();
}
void diag_pq(ulong p, ulong q) {
    sprintf(buf, "%lu %lu", p, q);
    do_diag();
}
void diag_pqr(ulong p, ulong q, ulong r) {
    sprintf(buf, "%lu %lu %lu", p, q, r);
    do_diag();
}

void handle_sig(int sig) {
    if (sig == SIGUSR1)
        need_work |= 1;
    else
        need_work |= 2;
}

void init_time(void) {
    struct sigaction sa;
    struct sigevent sev;
    struct itimerspec diag_timer, log_timer;

    sa.sa_handler = &handle_sig;
    sa.sa_flags = SA_RESTART;
    sigemptyset(&sa.sa_mask);
    if (sigaction(SIGUSR1, &sa, NULL))
        fail("Could not set USR1 handler: %s\n", strerror(errno));
    if (sigaction(SIGUSR2, &sa, NULL))
        fail("Could not set USR2 handler: %s\n", strerror(errno));

    sev.sigev_notify = SIGEV_SIGNAL;
    sev.sigev_signo = SIGUSR1;
    sev.sigev_value.sival_ptr = &diag_timerid;
    clock_is_realtime = 0;
    if (timer_create(CLOCK_PROCESS_CPUTIME_ID, &sev, &diag_timerid)) {
        /* guess that the CPUTIME clock is not supported */
        if (timer_create(CLOCK_REALTIME, &sev, &diag_timerid))
            fail("Could not create diag timer: %s\n", strerror(errno));
        clock_is_realtime = 1;
    }

    sev.sigev_signo = SIGUSR2;
    sev.sigev_value.sival_ptr = &log_timerid;
    clockid_t clock = clock_is_realtime
            ? CLOCK_REALTIME : CLOCK_PROCESS_CPUTIME_ID;
    if (timer_create(clock, &sev, &log_timerid))
        fail("Could not create log timer: %s\n", strerror(errno));

    diag_timer.it_value.tv_sec = diag_delay;
    diag_timer.it_value.tv_nsec = 0;
    diag_timer.it_interval.tv_sec = diag_delay;
    diag_timer.it_interval.tv_nsec = 0;
    if (timer_settime(diag_timerid, 0, &diag_timer, NULL))
        fail("Could not set diag timer: %s\n", strerror(errno));
    log_timer.it_value.tv_sec = log_delay;
    log_timer.it_value.tv_nsec = 0;
    log_timer.it_interval.tv_sec = log_delay;
    log_timer.it_interval.tv_nsec = 0;
    if (timer_settime(log_timerid, 0, &log_timer, NULL))
        fail("Could not set log timer: %s\n", strerror(errno));
}

void init(void) {
    _GMP_init();
    zstash = (mpz_t *)malloc(MAX_ZSTASH * sizeof(mpz_t));
    for (t_zstash i = 0; i < MAX_ZSTASH; ++i)
        mpz_init(Z(i));
    init_diag();
    init_time();
    init_tau(0);
}

void ston(mpz_t targ, char *s) {
    char *t = strchr(s, 'e');
    if (t) {
        *t = 0;
        mpz_set_str(targ, s, 10);
        ulong exp = strtoul(&t[1], NULL, 10);
        mpz_ui_pow_ui(Z(temp), 10, exp);
        mpz_mul(targ, targ, Z(temp));
        *t = 'e';
    } else {
        mpz_set_str(targ, s, 10);
    }
}

ulong ulston(char *s) {
    ston(Z(uls_temp), s);
    if (mpz_fits_ulong_p(Z(uls_temp)))
        return mpz_get_ui(Z(uls_temp));
    fail("value '%s' out of range of ulong", s);
}

/* m = (n % 576) >> 4 will tell us n32, the nearest multiple of 32 to n.
 * We need n32 = 32p, so can disallow p even; we also require n32 == 2 or -2
 * (mod 18).
 */
const bool fail_36[36] = {
    1, 1, 1, 1, 1, 1, 1, 1, 1,
    0, 0, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 0, 0,
    1, 1, 1, 1, 1, 1, 1, 1, 1
};

/* p^2qr is relevant only if it is within +/- 7 of n32. */
const bool fail_32[32] = {
    0, 0, 0, 0, 0, 0, 0, 0,
    1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1,
    1, 0, 0, 0, 0, 0, 0, 0
};

void tryvalue(mpz_t zv) {
    uint mod576 = mpz_fdiv_ui(zv, 576);
    if (fail_36[mod576 >> 4])
        return;
    uint mod32 = mod576 & 31;
    if (fail_32[mod32])
        return;

    /* find nearest multiple of 32 */
    mpz_sub_ui(Z(n32), zv, mod32);
    if (mod32 & 16)
        mpz_add_ui(Z(n32), Z(n32), 32);

    /* that multiple must be of form 32p */
    mpz_fdiv_q_2exp(Z(temp), Z(n32), 5);
    if (!_GMP_is_prob_prime(Z(temp)))
        return;

    /* we know p > 3, and we know n32 +/- 2 = 6q^2 can be ruled out,
     * so we must have n32 +/- 2 = 18q. */
    if (mod576 > 288) {
        /* n32 == 2 (mod 18) */
        mpz_fdiv_q_ui(Z(temp), Z(n32), 18);
        if (!_GMP_is_prob_prime(Z(temp)))
            return;
        mpz_add_ui(Z(temp), Z(n32), 2);
        if (!is_taux(Z(temp), 12, 1))
            return;
    } else {
        /* n32 == -2 (mod 18) */
        mpz_fdiv_q_ui(Z(temp), Z(n32), 18);
        mpz_add_ui(Z(temp), Z(temp), 1);
        if (!_GMP_is_prob_prime(Z(temp)))
            return;
        mpz_sub_ui(Z(temp), Z(n32), 2);
        if (!is_taux(Z(temp), 12, 1))
            return;
    }
    mpz_sub_ui(Z(temp), Z(n32), 1);
    if (!is_taux(Z(temp), 12, 1))
        return;
    mpz_add_ui(Z(temp), Z(n32), 1);
    if (!is_taux(Z(temp), 12, 1))
        return;
    /* extend chain 10 to 11 */
    mpz_sub_ui(Z(temp), Z(n32), 3);
    if (!is_taux(Z(temp), 12, 1))
        return;
    mpz_add_ui(Z(temp), Z(n32), 3);
    if (!is_taux(Z(temp), 12, 1))
        return;
    keep_diag();
    report("209 hit near %Zu (%.2fs)\n", Z(v), utime());
}

void tryp(ulong p) {
    /* test for p^2qr */
    mpz_ui_pow_ui(Z(p2), p, 2);
    mpz_fdiv_q(Z(temp), Z(lim), Z(p2));
    if (!mpz_fits_ulong_p(Z(temp)))
        fail("qrmax does not fit in ulong");
    ulong qrmax = mpz_get_ui(Z(temp));
    ulong qmax = (ulong)sqrt(qrmax);
    ulong q = 2;
    prime_iterator_setprime(&iq, q);
    bool want_cube = 1;
    while (q <= qmax) {
        if (need_work)
            diag_pq(p, q);
        mpz_mul_ui(Z(p2q), Z(p2), q);
        ulong rmax = qrmax / q;
        prime_iterator_setprime(&ir, q);
        ulong r = prime_iterator_next(&ir);
        while (r <= rmax) {
            if (need_work)
                diag_pqr(p, q, r);
            mpz_mul_ui(Z(v), Z(p2q), r);
            tryvalue(Z(v));
            r = prime_iterator_next(&ir);
        }
        if (want_cube) {
            /* if q^3 < qrmax, try that too */
            if (q <= rmax / q) {
                mpz_mul_ui(Z(v), Z(p2q), q * q);
                tryvalue(Z(v));
            } else
                want_cube = 0;
        }
        q = prime_iterator_next(&iq);
    }
}

int main(int argc, char **argv, char **envp) {
    int i = 1;
    init();
    while (i < argc && argv[i][0] == '-') {
        char *arg = argv[i++];
        if (arg[1] == 'r') {
            rpath = (char *)malloc(strlen(&arg[2]) + 1);
            strcpy(rpath, &arg[2]);
        } else
            fail("unknown option '%s'", arg);
    }
    if (i + 3 != argc)
        fail("wrong number of arguments");
    ston(Z(lim), argv[i++]);
    ulong pmin = ulston(argv[i++]);
    ulong pmax = ulston(argv[i++]);

    if (rpath) {
        printf("path %s\n", rpath);
        rfp = fopen(rpath, "a");
        if (rfp == NULL)
            fail("%s: %s", rpath, strerror(errno));
        setlinebuf(rfp);
    }
    report("001 sq12 %Zu %lu %lu\n", Z(lim), pmin, pmax);

    prime_iterator_setprime(&ip, pmax);
    prime_iterator_next(&ip);
    while (1) {
        ulong p = prime_iterator_prev(&ip);
        if (p < pmin)
            break;
        if (need_work)
            diag_p(p);
        tryp(p);
    }
    report("200 sq12 %Zu %lu %lu (%.2fs)\n", Z(lim), pmin, pmax, utime());
    if (rfp)
        fclose(rfp);
    return 0;
}
