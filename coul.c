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
#include <sys/time.h>
#include <sys/resource.h>

#include "coul.h"
#include "coulfact.h"
#include "diag.h"
#include "rootmod.h"
#include "coultau.h"
#include "pell.h"

/* from MPUG */
#include "factor.h"
#include "gmp_main.h"
#include "utility.h"
#include "primality.h"

/* primary parameters - we are searching for D(n, k), the least d such
 * that tau(d + i) = n for all 0 <= i < k.
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

/* stash of mpz_t, initialized once at start */
typedef enum {
    zero, zone,                 /* constants */
    temp,
    sqm_t, sqm_q, sqm_b, sqm_z, sqm_x,  /* sqrtmod_t */
    uc_minusvi, uc_px,          /* update_chinese */
    ur_a, ur_m, ur_ipg,         /* update_residues */
    asq_o, asq_qq, asq_m,       /* alloc_square */
    wv_ati, wv_end, wv_cand,    /* walk_v */
    wv_startr, wv_endr, wv_qqr, wv_r, wv_rx, wv_temp,
    wv_x, wv_y, wv_x2, wv_y2,
    w1_v, w1_j, w1_r,           /* walk_1 */
    lp_x, lp_mint,              /* limit_p */
    r_walk,                     /* recurse */

    sdm_p, sdm_r,               /* small_divmod (TODO) */
    dm_r,                       /* divmod */
    np_p,                       /* next_prime */
    s_exp, uls_temp,            /* ston, ulston */

    MAX_ZSTASH
} t_zstash;
mpz_t *zstash;
static inline mpz_t *ZP(t_zstash e) { return &zstash[e]; }
#define Z(e) *ZP(e)
/* additional arrays of mpz_t initialized once at start */
mpz_t *wv_o = NULL, *wv_qq = NULL;  /* wv_o[k], wv_qq[k] */

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
 * Each batch describes the location and magnitude of the highest power of p
 * that divides any v_i (using the lower i if there are more than one).
 */
typedef struct s_forcebatch {
    uint vi;    /* allocate p^{x-1} at v_{vi} */
    uint x;
} t_forcebatch;
typedef struct s_forcep {
    uint p;
    uint count;
    t_forcebatch *batch;
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

/* list of some small primes, at least enough for one per allocation  */
uint *sprimes = NULL;
uint nsprimes;

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

mpz_t min, max;     /* limits to check for v_0 */
mpz_t best;         /* best solution seen */
bool improve_max = 1;   /* reduce max when solution found */
uint seen_best = 0; /* number of times we've improved max */
ulong gain = 0;     /* used to fine-tune balance of recursion vs. walk */
ulong antigain = 0;
/* maxp[e] is the greatest prime we should attempt to allocate as power p^e;
 * minp[e] is the threshold that at least one allocated p^e should exceed
 * (else we can skip the walk); midp[e] is the additional threshold up to
 * which we should pre-walk.
 * sminp, smaxp, smidp are the strings that express the requests.
 */
ulong *minp = NULL, *maxp = NULL, *midp = NULL;
char *sminp = NULL, *smaxp = NULL, *smidp = NULL;
char *sminpx = NULL, *smaxpx = NULL, *smidpx = NULL;
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
/* If opt_alloc is true and opt_batch < 0, just show the forced-prime
 * allocation; if opt_alloc is true and opt_batch >= 0, just process
 * the specified batch_alloc.
 */
bool opt_alloc = 0;
int opt_batch_min = -1, opt_batch_max;
int batch_alloc = 0;    /* index of forced-prime allocations */
int last_batch_seen = -1;
uint cur_batch_level = 0;   /* for disp_batch */
uint strategy;          /* best_v() strategy */
uint strategy_set = 0;  /* strategy was user-selected */

bool debugw = 0;    /* diag and keep every case seen (excluding walk) */
bool debugW = 0;    /* diag and keep every case seen (including walk) */
bool debugx = 0;    /* show p^x constraints */
bool debugb = 0;    /* show batch id, if changed */
bool debugB = 0;    /* show every batch id */

ulong randseed = 1; /* for ECM, etc */
bool vt100 = 0;     /* update window title with VT100 escape sequences */

char *rpath = NULL; /* path to log file */
FILE *rfp = NULL;   /* file handle to log file */
bool start_seen = 0;    /* true if log file has been written to before */
bool skip_recover = 0;  /* true if we should not attempt recovery */
t_fact *rstack = NULL;  /* point reached in recovery log file */
bool have_rwalk = 0;    /* true if recovery is mid-walk */
mpz_t rwalk_from;
mpz_t rwalk_to;

t_fact nf;      /* factors of n */
uint maxfact;   /* count of prime factors dividing n, with multiplicity */
uint maxodd;    /* as above for odd prime factors */
uint *maxforce = NULL;  /* max prime to force at v_i */
mpz_t px;       /* p^x */

#define DIAG 1
#define LOG 600
double diag_delay = DIAG, log_delay = LOG, diagt, logt;
ulong countr, countw, countwi;
#define MAX_DEC_ULONG 20
#define MAX_DEC_POWER 5
#define DIAG_BUFSIZE (6 + MAX_DEC_ULONG + k * maxfact * (MAX_DEC_ULONG + 1 + MAX_DEC_POWER + 1) + 1)
char *diag_buf = NULL;
uint aux_buf_size = 0;
char *aux_buf = NULL;

/* Initial pattern set with -I */
char *init_pattern = NULL;

/* Mod constraints set with -m */
typedef struct s_modfix {
    mpz_t mod;
    mpz_t val;
} t_modfix;
t_modfix *modfix = NULL;
uint modfix_count = 0;

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
    offset += sprintf(&diag_buf[offset], "b%u: ", batch_alloc - 1);
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
    prep_show_v(lp);        /* into diag_buf */
    if (lp->have_square) {
        uint l = strlen(diag_buf);
        sprintf(&diag_buf[l], " [sq=%u]", lp->have_square);
    }
    report("203 %s\n", diag_buf);
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
        if (debugw)
            keep_diag();
        else
            need_diag = 0;
    }

    if (rfp && need_log) {
        fprintf(rfp, "305 %s%s (%.2fs)\n", diag_buf, aux_buf, seconds(t1));
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
    if (improve_max && mpz_cmp(c, max) <= 0)
        mpz_set(max, c);
    return improve_max;
}

void free_levels(void) {
    for (uint i = 0; i < maxlevel; ++i) {
        t_level *l = &levels[i];
        free(l->vlevel);
        mpz_clear(l->aq);
        mpz_clear(l->rq);
        prime_iterator_destroy(&l->piter);
    }
    free(levels);
}

void init_levels(void) {
    levels = (t_level *)calloc(maxlevel, sizeof(t_level));
    for (uint i = 0; i < maxlevel; ++i) {
        t_level *l = &levels[i];
        l->level = i;
        l->vlevel = calloc(k, sizeof(uint));
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
    levels[0].nextpi = 0;
    levels[0].maxp = 0;
    for (uint j = 0; j < k; ++j)
        levels[0].vlevel[j] = 1;
    level = 1;
}

void free_value(void) {
    for (int i = 0; i < k; ++i) {
        t_value *v = &value[i];
        for (int j = 0; j <= maxfact; ++j)
            mpz_clear(v->alloc[j].q);
        free(v->alloc);
    }
    free(value);
}

void init_value(void) {
    value = (t_value *)malloc(k * sizeof(t_value));
    for (int i = 0; i < k; ++i) {
        t_value *v = &value[i];
        v->alloc = (t_allocation *)malloc((maxfact + 1) * sizeof(t_allocation));
        for (uint j = 0; j <= maxfact; ++j)
            mpz_init(v->alloc[j].q);
        t_allocation *ap = &v->alloc[0];
        ap->p = 0;
        ap->x = 0;
        ap->t = target_t(i);
        mpz_set_ui(ap->q, 1);
    }
}

void done(void) {
    /* update window title on completion */
    if (vt100)
        printf("\x1b]2;b%d: done\a",
                opt_batch_min < 0 ? batch_alloc : opt_batch_max);

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
    free(modfix);
    free(minp);
    free(maxp);
    free(midp);
    free(midpp);
    free(sqg);
    free_value();
    free_levels();
    free(sprimes);
    if (forcep)
        for (int i = 0; i < forcedp; ++i)
            free(forcep[i].batch);
    free(forcep);
    free(maxforce);
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
    if (rstack)
        for (int i = 0; i < k; ++i)
            free_fact(&rstack[i]);
    free(rstack);
    if (rfp)
        fclose(rfp);
    free(rpath);
    for (t_zstash i = 0; i < MAX_ZSTASH; ++i)
        mpz_clear(Z(i));
    free(zstash);
    mpz_clear(px);
    free_fact(&nf);
    mpz_clear(max);
    mpz_clear(min);
    done_pell();
    done_rootmod();
    done_tau();
    _GMP_destroy();
}

void fail(char *format, ...) {
    va_list ap;
    va_start(ap, format);
    vfprintf(stderr, format, ap);
    fprintf(stderr, "\n");
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

void init_modfix(void) {
    for (uint mfi = 0; mfi < modfix_count; ++mfi) {
        t_modfix *mfp = &modfix[mfi];
        mpz_t zarray[4];
        /* TODO: write a custom chinese() */
        memcpy(&zarray[0], levels[0].rq, sizeof(mpz_t));
        memcpy(&zarray[1], mfp->val, sizeof(mpz_t));
        memcpy(&zarray[2], levels[0].aq, sizeof(mpz_t));
        memcpy(&zarray[3], mfp->mod, sizeof(mpz_t));
        if (!chinese(levels[0].rq, levels[0].aq, &zarray[0], &zarray[2], 2))
            fail("failed to apply v_0 == %Zu (mod %Zu)", mfp->val, mfp->mod);
        mpz_clear(mfp->mod);
        mpz_clear(mfp->val);
    }
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
    mpz_init_set_ui(min, 0);
    mpz_init_set_ui(max, 0);
    init_fact(&nf);
    mpz_init(px);
    zstash = (mpz_t *)malloc(MAX_ZSTASH * sizeof(mpz_t));
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
void parse_305(char *s) {
    double dtime;
    t_ppow pp;
    bool is_W = 0;

    rstack = (t_fact *)malloc(k * sizeof(t_fact));
    for (int i = 0; i < k; ++i)
        init_fact(&rstack[i]);

    if (s[0] == 'b') {
        int off = 0;
        if (EOF == sscanf(s, "b%u: %n", &batch_alloc, &off))
            fail("error parsing 305 line '%s'", s);
        s += off;
        ++batch_alloc;  /* we always point to the next batch */
    }
        
    for (int i = 0; i < k; ++i) {
        if (i) {
            assert(s[0] == ' ');
            ++s;
        }
        if (s[0] == '.') {
            ++s;
            continue;
        }
        while (1) {
            pp.p = strtoul(s, &s, 10);
            pp.e = (s[0] == '^') ? strtoul(&s[1], &s, 10) : 1;
            add_fact(&rstack[i], pp);
            if (s[0] != '.')
                break;
            ++s;
        }
        /* reverse them, so we can pop as we allocate */
        reverse_fact(&rstack[i]);
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
            fail("cannot recover from old-style 'W(...)' entry");
#else
            /* old version had x fixed to 3 */
            midp_recover.vi = midp_recover.x;
            midp_recover.x = 3;
#endif
        } else {
            assert(s[0] == ',');
            ++s;
            midp_recover.vi = strtoul(s, &s, 10);
        }
        assert(s[0] == ')');
        ++s;
        midp_recover.valid = 1;
    }
    if (s[0] == ':') {
        assert(s[1] == ' ');
        s += 2;
        if (strncmp("t=1", s, 3) == 0)
            s += 3; /* ignore */
        else {
            int from_start, from_end, to_start, to_end;
            have_rwalk = 1;
            if (EOF == sscanf(s, "%n%*[0-9]%n / %n%*[0-9]%n ",
                    &from_start, &from_end, &to_start, &to_end))
                fail("could not parse 305 from/to: '%s'", s);
            s[from_end] = 0;
            mpz_init_set_str(rwalk_from, &s[from_start], 10);
            s[to_end] = 0;
            mpz_init_set_str(rwalk_to, &s[to_start], 10);
            have_rwalk = 1;
            s[to_end] = ' ';
            s = &s[to_end];
        }
    }
    if (s[0] == 0 || s[0] == '\n')
        dtime = 0;
    else if (EOF == sscanf(s, " (%lfs)\n", &dtime))
        fail("could not parse 305 time: '%s'", s);
    if (is_W && !need_midp)
        fail("recovery expected -W option");
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
            int start, end;
            mpz_t cand;
            if (EOF == sscanf(curbuf, "202 Candidate %n%*[0-9]%n (%*[0-9.]s)\n",
                    &start, &end))
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
    if (improve_max && seen_best && mpz_cmp(best, max) < 0)
        mpz_set(max, best);
    if (last305)
        parse_305(last305 + 4);
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
        uint t;
#if defined(TYPE_r)
        f.count = 0;
        simple_fact(n + i, &f);
        t = simple_tau(&f);
        target_tau[i] = t;
        ulong g = simple_gcd(target_lcm, t);
        target_lcm *= t / g;
#else
        t = n;
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

    divisors = (t_divisors *)calloc(target_lcm + 1, sizeof(t_divisors));
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
        dp->div = (uint *)malloc(td * sizeof(uint));
        for (uint j = 1; j <= i; ++j) {
            if (i % j)
                continue;
            dp->div[dp->alldiv++] = j;
            if ((j % dp->high) == 0)
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

void prep_mintau(void) {
    return;
}

void prep_maxforce(void) {
    maxforce = (uint *)malloc(k * sizeof(uint));
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
    nsprimes = maxodd * k + forcedp + (maxfact - maxodd);
    sprimes = (uint *)malloc(nsprimes * sizeof(uint));
    uint p = 1;
    for (uint i = 0; i < nsprimes; ++i) {
        p = next_prime(p);
        sprimes[i] = p;
    }
}

typedef enum {
    TFP_BAD = 0,
    TFP_SINGLE,
    TFP_GOOD
} e_tfp;
e_tfp test_forcep(uint p, uint vi, uint x) {
    bool seen_any = 0;
    bool seen_odd = 0;

    if (x == 0) {
        /* p^0 is valid iff the differences are a multiple of p */
        if (TYPE_OFFSET(1) % p)
            return TFP_BAD;
        return TFP_GOOD;
    }

    if (x & (x - 1))
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
        seen_any = 1;
        if (ej & (ej + 1))
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
        if (ej & (ej + 1))
            seen_odd = 1;
        if (ej > ei)
            continue;   /* p^e_i + p^e_j will have valuation e_i */
        if (target_t(vj) % (ej + 1))
            return TFP_BAD;
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

    forcep = (t_forcep *)malloc(forcedp * sizeof(t_forcep));
    for (uint fpi = 0; fpi < forcedp; ++fpi) {
        p = pi[fpi];
        t_forcep *fp = &forcep[fpi];
        fp->p = p;
        fp->count = 0;
        fp->batch = (t_forcebatch *)malloc(maxbatch * sizeof(t_forcebatch));

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
                uint status = test_forcep(p, vi, fx);
                if (status == TFP_BAD)
                    continue;
                if (status == TFP_SINGLE && !keep_single) {
                    have_unforced_tail = 1;
                    continue;
                }
                /* else status == TFP_GOOD */
                fp->batch[fp->count++] = (t_forcebatch){ .vi = vi, .x = fx };
            }
        }
#if defined(TYPE_a)
        uint status = test_forcep(p, 0, 0);
        if (status != TFP_BAD)
            fp->batch[fp->count++] = (t_forcebatch){ .vi = 0, .x = 0 };
#endif
        if (fp->count == 0) {
            if (have_unforced_tail) {
                forcedp = fpi;
                free(fp->batch);
                break;
            }
            fail("No valid arrangement of powers for p=%u", p);
        }
        if (have_unforced_tail)
            fp->batch[fp->count++] = (t_forcebatch){ .vi = 1, .x = 0 };
        fp->batch = (t_forcebatch *)realloc(fp->batch,
                fp->count * sizeof(t_forcebatch));
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
                if ((dm & (dm + 1)) == 0)
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
                if ((dm & (dm + 1)) == 0)
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
        if ((dm & (dm + 1)) == 0)
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
 * Note: we just allocated to vi, so at least one allocation exists.
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

void init_post(void) {
    init_tau(rough);
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
        parse_305(init_pattern);
#ifdef HAVE_SETPROCTITLE
    setproctitle("oul(%lu %lu)", n, k);
#endif
    simple_fact(n, &nf);
    prep_target();
    /* level[0] is special;
     * then we can have forcedp batch allocations and maxodd * k normal
     * allocations; however we don't know forcedp yet, only that it will
     * be at most |{ p: p < k }| for TYPE_o and TYPE_r, and
     * |{ p: p < k or p | n }| for TYPE_a.
     * So pick something conservative enough for all cases.
     */
    maxlevel = 1 + k * maxodd + k
#if defined(TYPE_a)
            + nf.count
#endif
            ;

    /* Strategy 1 is preferred when n is divisible by two or more
     * distinct odd primes. Otherwise, strategy 0 always gives the same
     * results, and is a bit faster. */
    if (!strategy_set)
        strategy = (nf.count > 2) ? 1 : 0;

    init_rootmod(maxlevel);
    prep_fact();
    prep_maxforce();
    prep_forcep();
    prep_primes();  /* needs forcedp */
    prep_mintau();
    prep_mp();  /* maxp[], minp[], midp[] */
    sqg = (uint *)malloc(maxfact * sizeof(uint));

    uint maxmidpp = 0;
    for (uint i = 0; i < k; ++i)
        maxmidpp += divisors[ target_t(i) ].alldiv;
    midpp = malloc(sizeof(t_midpp) * maxmidpp);

    if (debugw) {
        diag_delay = 0;
        need_work = need_diag = 1;
    }
    diagt = diag_delay;
    if (rfp)
        logt = log_delay;
    else
        logt = log_delay = 0;
    init_time();

    init_levels();
    init_modfix();
    init_value();
    countr = 0;
    countw = 0;
    countwi = 0;

    wv_o = (mpz_t *)malloc(k * sizeof(mpz_t));
    wv_qq = (mpz_t *)malloc(k * sizeof(mpz_t));
    for (uint i = 0; i < k; ++i) {
        mpz_init(wv_o[i]);
        mpz_init(wv_qq[i]);
    }
    diag_buf = (char *)malloc(DIAG_BUFSIZE);
    init_diag();    /* ignore result: worst case we lose ^Z handling */
}

void report_init(FILE *fp, char *prog) {
    fprintf(fp, "001 %s%sc%sul(%u %u)", (start_seen ? "recover " : ""),
#ifdef PARALLEL
            "p",
#else
            "",
#endif
#if defined(TYPE_o)
            "o",
#elif defined(TYPE_a)
            "a",
#elif defined(TYPE_r)
            "r",
#endif
            n, k);

    if (strategy)
        fprintf(fp, " -j%u", strategy);
    if (opt_print)
        fprintf(fp, " -o");
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
    if (mpz_sgn(min) || mpz_sgn(max)) {
        fprintf(fp, " -x");
        if (mpz_sgn(min))
            gmp_fprintf(fp, "%Zu:", min);
        if (mpz_sgn(max))
            gmp_fprintf(fp, "%Zu", max);
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
    if (clock_is_realtime)
        fprintf(fp, " *RT*");
    fprintf(fp, "\n");
}

void set_minmax(char *s) {
    char *t = strchr(s, ':');
    if (t) {
        *t = 0;
        if (*s)
            ston(min, s);
        else
            mpz_set_ui(min, 0);
        if (t[1])
            ston(max, &t[1]);
        else
            mpz_set_ui(max, 0);
    } else {
        mpz_set_ui(min, 0);
        ston(max, s);
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
    opt_alloc = 1;
}

void set_modfix(char *s) {
    char *t = strchr(s, '=');
    if (!t)
        fail("-m option must be of form '-m<modulus>=<value>'");
    *t++ = 0;
    uint mfi = modfix_count++;
    modfix = realloc(modfix, modfix_count * sizeof(t_modfix));
    t_modfix *mfp = &modfix[mfi];
    mpz_init(mfp->mod);
    mpz_init(mfp->val);
    ston(mfp->mod, s);
    ston(mfp->val, t);
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
uint find_nextpi(uint pi) {
    while (1) {
        ++pi;
        uint p = sprimes[pi];
        for (uint i = 1; i < level; ++i)
            if (levels[i].p == p)
                goto NEXT_PI;
        return pi;
      NEXT_PI:
        ;
    }
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

bool test_1multi(uint *need, uint nc, uint *t) {
    for (uint i = 0; i < nc; ++i) {
        uint vi = need[i];
        t_tm *tm = &taum[i];
        mpz_set(tm->n, wv_o[vi]);
        tm->t = t[vi];
        if (!tau_multi_prep(i))
            return 0;
    }
    return tau_multi_run(nc);
}

bool test_multi(uint *need, uint nc, ulong ati, uint *t) {
    for (uint i = 0; i < nc; ++i) {
        uint vi = need[i];
        t_tm *tm = &taum[i];
        mpz_mul_ui(tm->n, wv_qq[vi], ati);
        mpz_add(tm->n, tm->n, wv_o[vi]);
        tm->t = t[vi];
        if (!tau_multi_prep(i))
            return 0;
    }
    return tau_multi_run(nc);
}

bool test_zmulti(uint *need, uint nc, mpz_t ati, uint *t) {
    for (uint i = 0; i < nc; ++i) {
        uint vi = need[i];
        t_tm *tm = &taum[i];
        mpz_mul(tm->n, wv_qq[vi], ati);
        mpz_add(tm->n, tm->n, wv_o[vi]);
        tm->t = t[vi];
        if (!tau_multi_prep(i))
            return 0;
    }
    return tau_multi_run(nc);
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
    if (!cur_level->have_min)
        return;

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

    mpz_sub(Z(wv_end), max, *m);
    mpz_fdiv_q(Z(wv_end), Z(wv_end), *aq);
    if (mpz_sgn(Z(wv_end)) < 0)
        return;

    if (mpz_sgn(start)) {
        mpz_set(Z(wv_ati), start);
    } else {
        mpz_sub(Z(wv_ati), min, *m);
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
        else if (t[vi] & 1)
            need_square[nqc++] = vi;
        else
            need_other[noc++] = vi;
    }

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

            mpz_fdiv_q(Z(wv_endr), max, *qi);
            mpz_root(Z(wv_endr), Z(wv_endr), 2);
            /* solve Ax^2 - By^2 = C with x <= D */
            int sqoff = (sqi < sqj)
                ? -(int)TYPE_OFFSET(sqj - sqi)
                : (int)TYPE_OFFSET(sqi - sqj);
            new_pell(*qi, *qj, sqoff, Z(wv_endr));
            uint pc = 0;
            while (next_pell(Z(wv_x), Z(wv_y))) {
                /* v_{sqi} = x^2 . q_i; v_{sqj} = y^2 . q_j */
                mpz_mul(Z(wv_x2), Z(wv_x), Z(wv_x));

                /* verify limit */
                mpz_mul(Z(wv_temp), Z(wv_x2), *qi);
                mpz_sub_ui(Z(wv_temp), Z(wv_temp), TYPE_OFFSET(sqi));
                if (mpz_cmp(Z(wv_temp), max) > 0)
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
                /* Note: assume the square roots are small enough to
                 * factorize without fuss */
                if (!is_taux(Z(wv_x), ti, 2))
                    continue;
                if (!is_taux(Z(wv_y), tj, 2))
                    continue;

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
                for (uint i = 0; i < npc; ++i) {
                    uint vi = need_prime[i];
                    if (!test_zprime(wv_qq[vi], wv_o[vi], Z(wv_ati)))
                        goto next_pell;
                }
                /* TODO: bail and print somewhere here if 'opt_print' */
#ifdef PARALLEL
                if (!test_zmulti(need_other, noc, Z(wv_ati), t))
                    goto next_pell;
#else
                for (uint i = 0; i < noc; ++i) {
                    uint vi = need_other[i];
                    if (!test_zother(wv_qq[vi], wv_o[vi], Z(wv_ati), t[vi]))
                        goto next_pell;
                }
#endif
                /* have candidate: calculate and apply it */
                mpz_mul(Z(wv_cand), wv_qq[0], Z(wv_ati));
                mpz_add(Z(wv_cand), Z(wv_cand), wv_o[0]);
                mpz_mul(Z(wv_cand), Z(wv_cand), *q[0]);
                if (candidate(Z(wv_cand)))
                    break;

              next_pell:
                ;
            }
            /* clear_pell(); */
            return;
        }
        /* gcd(d - 1) for all divisors d of ti */
        uint xi = divisors[ti].gcddm;
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
                    gmp_fprintf(stderr,
                        "from restart %Zu no match found for mod %Zu < %Zu\n",
                        Z(wv_ati), Z(wv_temp), xr->r[xmi]
                    );
                    exit(1);
                }
                if (xmi + 1 == xr->count) {
                    if (mpz_sgn(start) == 0) {
                        rindex = 0;
                        mpz_add_ui(Z(wv_startr), Z(wv_startr), 1);
                        break;
                    }
                    gmp_fprintf(stderr,
                        "from start %Zu no match found for mod %Zu > %Zu\n",
                        Z(wv_ati), Z(wv_temp), xr->r[xmi]
                    );
                    exit(1);
                }
            }
            mpz_mul(Z(wv_qqr), *qqi, Z(wv_startr));
        } else {
            mpz_set_ui(Z(wv_qqr), 0);
        }
        mpz_sub(Z(wv_end), max, *m);
        mpz_fdiv_q(Z(wv_end), Z(wv_end), *aq);
        mpz_add_ui(Z(wv_endr), max, TYPE_OFFSET(sqi));
        mpz_fdiv_q(Z(wv_endr), Z(wv_endr), *qi);
        mpz_root(Z(wv_endr), Z(wv_endr), xi);

        while (1) {
            mpz_add(Z(wv_r), Z(wv_qqr), xr->r[rindex]);
            if (mpz_cmp(Z(wv_r), Z(wv_endr)) > 0)
                return;
            ++countwi;
            mpz_pow_ui(Z(wv_rx), Z(wv_r), xi);
            mpz_sub(Z(wv_ati), Z(wv_rx), *oi);
            mpz_fdiv_q(Z(wv_ati), Z(wv_ati), *qqi);
            if (need_work)
                diag_walk_zv(cur_level, Z(wv_ati), Z(wv_end));
            for (uint ii = 0; ii < inv_count; ++ii) {
                t_mod *ip = &inv[ii];
                if (mpz_fdiv_ui(Z(wv_ati), ip->m) == ip->v)
                    goto next_sqati;
            }
            if (!is_taux(Z(wv_r), ti, xi))
                goto next_sqati;
            /* note: we have no more squares */
            for (uint i = 0; i < npc; ++i) {
                uint vi = need_prime[i];
                if (!test_zprime(wv_qq[vi], wv_o[vi], Z(wv_ati)))
                    goto next_sqati;
            }
            /* TODO: bail and print somewhere here if 'opt_print' */
#ifdef PARALLEL
            if (!test_zmulti(need_other, noc, Z(wv_ati), t))
                goto next_sqati;
#else
            for (uint i = 0; i < noc; ++i) {
                uint vi = need_other[i];
                if (!test_zother(wv_qq[vi], wv_o[vi], Z(wv_ati), t[vi]))
                    goto next_sqati;
            }
#endif
            /* have candidate: calculate and apply it */
            mpz_mul(Z(wv_cand), wv_qq[0], Z(wv_ati));
            mpz_add(Z(wv_cand), Z(wv_cand), wv_o[0]);
            mpz_mul(Z(wv_cand), Z(wv_cand), *q[0]);
            if (candidate(Z(wv_cand)))
                return;
          next_sqati:
            ++rindex;
            if (rindex >= xr->count) {
                mpz_add(Z(wv_qqr), Z(wv_qqr), *qqi);
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
    for (ulong ati = mpz_get_ui(Z(wv_ati)); ati <= end; ++ati) {
        ++countwi;
        if (need_work)
            diag_walk_v(cur_level, ati, end);
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
        for (uint i = 0; i < npc; ++i) {
            uint vi = need_prime[i];
            if (!test_prime(wv_qq[vi], wv_o[vi], ati))
                goto next_ati;
        }
        /* TODO: bail and print somewhere here if 'opt_print' */
#ifdef PARALLEL
        if (!test_multi(need_other, noc, ati, t))
            goto next_ati;
#else
        for (uint i = 0; i < noc; ++i) {
            uint vi = need_other[i];
            if (!test_other(wv_qq[vi], wv_o[vi], ati, t[vi]))
                goto next_ati;
        }
#endif
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
    if (!cur_level->have_min)
        return;

    {
        t_value *vip = &value[vi];
        t_allocation *aip = &vip->alloc[cur_level->vlevel[vi] - 1];
        mpz_sub_ui(Z(w1_v), aip->q, TYPE_OFFSET(vi));
    }

    if (mpz_cmp(Z(w1_v), min) < 0)
        return;
    ++countw;

    uint t[k];
    uint need_prime[k];
    uint need_square[k];
    uint need_other[k];
    uint npc = 0, nqc = 0, noc = 0;
    for (uint vj = 0; vj < k; ++vj) {
        if (vi == vj)
            continue;
        t_value *vjp = &value[vj];
        uint vjl = cur_level->vlevel[vj];
        t_allocation *ajp = vjl ? &vjp->alloc[vjl - 1] : NULL;
        mpz_add_ui(Z(w1_j), Z(w1_v), TYPE_OFFSET(vj));
        if (ajp) {
            /* FIXME: replace this with a single initial check of
             * v_0 == rq mod aq, then use divexact */
            mpz_fdiv_qr(Z(w1_j), Z(w1_r), Z(w1_j), ajp->q);
            if (mpz_sgn(Z(w1_r)) != 0)
                return;
            mpz_gcd(Z(w1_r), Z(w1_j), ajp->q);
            if (mpz_cmp(Z(w1_r), Z(zone)) != 0)
                return;
        }
        t[vj] = ajp ? ajp->t : n;
        if (t[vj] == 1) {
            if (mpz_cmp_ui(Z(w1_j), 1) != 0)
                return;
        } else if (t[vj] == 2)
            need_prime[npc++] = vj;
        else if (t[vj] & 1)
            need_square[nqc++] = vj;
        else
            need_other[noc++] = vj;
        mpz_set(wv_o[vj], Z(w1_j));
    }
    ++countwi;
    for (uint i = 0; i < npc; ++i)
        if (!_GMP_is_prob_prime(wv_o[need_prime[i]]))
            return;
    for (uint i = 0; i < nqc; ++i)
        if (!is_taux(wv_o[need_square[i]], t[need_square[i]], 1))
            return;
    oc_t = t;
    qsort(need_other, noc, sizeof(uint), &other_comparator);
#ifdef PARALLEL
    if (!test_1multi(need_other, noc, t))
        return;
#else
    for (uint i = 0; i < noc; ++i)
        if (!is_taux(wv_o[need_other[i]], t[need_other[i]], 1))
            return;
#endif
    candidate(Z(w1_v));
    return;
}

/* test a set of cases where v_i will have all divisors accounted for */
void walk_1_set(t_level *cur_level, uint vi, ulong plow, ulong phigh, uint x) {
#ifdef SQONLY
    if (!cur_level->have_square)
        return;
#endif
    if (!cur_level->have_min)
        plow = minp[x - 1];
    if (plow < 2)
        plow = 2;

    uint t[k];
    uint need_prime[k];
    uint need_square[k];
    uint need_other[k];
    uint npc = 0, nqc = 0, noc = 0;
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
        else if (t[vj] & 1)
            need_square[nqc++] = vj;
        else
            need_other[noc++] = vj;
    }

    level_setp(cur_level, plow - 1);    /* next prime should be plow */
    t_value *vip = &value[vi];
    uint vil = cur_level->vlevel[vi];
    t_allocation *aip = &vip->alloc[vil - 1];
    while (1) {
        ulong p = prime_iterator_next(&cur_level->piter);
        if (p > phigh)
            break;
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
        mpz_mul(Z(w1_v), Z(w1_v), aip->q);
        mpz_sub_ui(Z(w1_v), Z(w1_v), TYPE_OFFSET(vi));

        if (mpz_cmp(Z(w1_v), min) < 0)
            break;
        ++countw;

        for (uint vj = 0; vj < k; ++vj) {
            t_value *vjp = &value[vj];
            uint vjl = cur_level->vlevel[vj];
            t_allocation *ajp = &vjp->alloc[vjl - 1];
            mpz_add_ui(Z(w1_j), Z(w1_v), TYPE_OFFSET(vj));
            mpz_fdiv_qr(Z(w1_j), Z(w1_r), Z(w1_j), ajp->q);
            if (mpz_sgn(Z(w1_r)) != 0)
                goto reject_this_one;
            mpz_gcd(Z(w1_r), Z(w1_j), ajp->q);
            if (mpz_cmp(Z(w1_r), Z(zone)) != 0)
                goto reject_this_one;
            mpz_set(wv_o[vj], Z(w1_j));
        }
        ++countwi;
        for (uint i = 0; i < npc; ++i)
            if (!_GMP_is_prob_prime(wv_o[need_prime[i]]))
                goto reject_this_one;
        for (uint i = 0; i < nqc; ++i)
            if (!is_taux(wv_o[need_square[i]], t[need_square[i]], 1))
                goto reject_this_one;
        oc_t = t;
        qsort(need_other, noc, sizeof(uint), &other_comparator);
#ifdef PARALLEL
        if (!test_1multi(need_other, noc, t))
            goto reject_this_one;
#else
        for (uint i = 0; i < noc; ++i)
            if (!is_taux(wv_o[need_other[i]], t[need_other[i]], 1))
                goto reject_this_one;
#endif
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
        /* Another allocation on our square, so q_j changes but aq/q_j does
         * not. We must divide the known residues by p^((x-1)/g) mod aq/q_j,
         * and if the required power g has changed take roots again. */
        uint oldg = sqg[jlevel - 1];
        uint newg = divisors[vjp->alloc[jlevel].t].gcddm;
        uint divpow = (x - 1) / oldg;

        /* note: if this is the secondary of a batch, new may have
         * inappropriate values for this stage */
        mpz_divexact(Z(ur_m), old->aq, vjp->alloc[jlevel - 1].q);
        mpz_ui_pow_ui(Z(ur_ipg), p, divpow);
        if (!mpz_invert(Z(ur_ipg), Z(ur_ipg), Z(ur_m)))
            fail("Cannot find mandatory inverse for %lu^%u", p, divpow);

        t_results *rsrc = res_array(old->level);
        t_results *rdest = res_array(new->level);
        resize_results(rdest, rsrc->count);
        for (uint i = 0; i < rsrc->count; ++i) {
            mpz_mul(rdest->r[i], rsrc->r[i], Z(ur_ipg));
            mpz_mod(rdest->r[i], rdest->r[i], Z(ur_m));
        }
        rdest->count = rsrc->count;

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
    /* in the non-retry case, m = old->aq / q_j; in the retry case,
     * we need to take the previous value of q_j */
    uint mlevel = retry ? jlevel - 1 : jlevel;
    if (retry) {
        mpz_ui_pow_ui(Z(ur_m), p, retry);
        mpz_divexact(Z(ur_a), Z(ur_a), Z(ur_m));
    }
    if (!divmod(Z(ur_a), Z(ur_a), vjp->alloc[mlevel].q, px))
        return 0;
    mpz_divexact(Z(ur_m), old->aq, vjp->alloc[mlevel].q);
    /* on retry, residues to update are already at new */
    uint from = retry ? new->level : old->level;

    /* we may have a modfix */
    if (modfix && mpz_divisible_ui_p(levels[0].aq, p)) {
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

    root_extend(new->level, from, Z(ur_m), Z(ur_a), g, p, x - 1, px);
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

    /* is this newly a square? */
    if ((cur->t > 1) && (cur->t & 1) && !(prev->t & 1))
        if (!alloc_square(cur_level, vi))
            return 0;

    return 1;
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
    if (p == sprimes[cur->nextpi])
        cur->nextpi = find_nextpi(cur->nextpi);
    cur->maxp = (p > prev->maxp) ? p : prev->maxp;
}

/* Apply a notional level of p^0 at v_0.
 * Also sets level.rq, level.aq and residues.
 */
void apply_null(t_level *prev, t_level *cur, ulong p) {
    cur->vi = 0;
    cur->p = p;
    cur->x = 1;
    cur->have_square = prev->have_square;
    cur->have_min = prev->have_min;
    cur->nextpi = prev->nextpi;
    if (p == sprimes[cur->nextpi])
        cur->nextpi = find_nextpi(cur->nextpi);
    cur->maxp = (p > prev->maxp) ? p : prev->maxp;
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
    /* if rq > max, no solution <= max is possible */
    if (mpz_cmp(cur->rq, max) > 0) {
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
    if (mpz_cmp(cur->rq, max) > 0)
        return 0;

    return 1;
}

/* floor(log_p{q}) */
static inline uint lpq(uint p, uint q) {
    uint l = 0;
    while (q >= p) {
        q /= p;
        ++l;
    }
    return l;
}

/* Calculate the minimum contribution from unused primes satisfying
 * the given tau.
 *
 * If h(n) is the highest prime dividing n, this may be called for
 * any t: t | n/h(n).
 *
 * We have specific cases for each composite tau we can encounter at least
 * up to n=100, and fall back to a default for other cases which is precise
 * for prime tau but conservative for composite tau.
 */
void mintau(t_level *prev_level, mpz_t mint, uint t) {
    uint pi = prev_level->nextpi;
    uint p = sprimes[pi];
    switch(t) {
      case 1:
        mpz_set_ui(mint, 1);
        break;
      case 2:
        mpz_set_ui(mint, p);
        break;
      case 4: {
        uint q = sprimes[find_nextpi(pi)];
        if (lpq(p, q) < 2) {
            mpz_set_ui(mint, p);
            mpz_mul_ui(mint, mint, q);
        } else {
            mpz_ui_pow_ui(mint, p, 3);
        }
        break;
      }
      case 6: {
        uint q = sprimes[find_nextpi(pi)];
        if (lpq(p, q) < 3) {
            mpz_ui_pow_ui(mint, p, 2);
            mpz_mul_ui(mint, mint, q);
        } else {
            mpz_ui_pow_ui(mint, p, 5);
        }
        break;
      }
      case 8: {
        uint qi = find_nextpi(pi);
        uint q = sprimes[qi];
        uint r = sprimes[find_nextpi(qi)];
        if (lpq(p, r) < 2) {
            mpz_set_ui(mint, p);
            mpz_mul_ui(mint, mint, q);
            mpz_mul_ui(mint, mint, r);
        } else if (lpq(p, q) < 4) {
            mpz_ui_pow_ui(mint, p, 3);
            mpz_mul_ui(mint, mint, q);
        } else {
            mpz_ui_pow_ui(mint, p, 7);
        }
        break;
      }
      case 9: {
        uint q = sprimes[find_nextpi(pi)];
        if (lpq(p, q) < 3) {
            mpz_ui_pow_ui(mint, p * q, 2);
        } else {
            mpz_ui_pow_ui(mint, p, 8);
        }
        break;
      }
      case 10: {
        uint q = sprimes[find_nextpi(pi)];
        if (lpq(p, q) < 5) {
            mpz_ui_pow_ui(mint, p, 4);
            mpz_mul_ui(mint, mint, q);
        } else {
            mpz_ui_pow_ui(mint, p, 9);
        }
        break;
      }
      case 12: {
        uint qi = find_nextpi(pi);
        uint q = sprimes[qi];
        uint r = sprimes[find_nextpi(qi)];
        uint pq = lpq(p, q);
        if (p > r / q && lpq(p, r) < 3) {
            mpz_set_ui(mint, p * p);
            mpz_mul_ui(mint, mint, q * r);
        } else if (pq < 2) {
            mpz_ui_pow_ui(mint, p * q, 2);
            mpz_mul_ui(mint, mint, p);
        } else if (pq < 6) {
            mpz_ui_pow_ui(mint, p, 5);
            mpz_mul_ui(mint, mint, q);
        } else {
            mpz_ui_pow_ui(mint, p, 11);
        }
        break;
      }
      case 14: {
        uint q = sprimes[find_nextpi(pi)];
        if (lpq(p, q) < 7) {
            mpz_ui_pow_ui(mint, p, 6);
            mpz_mul_ui(mint, mint, q);
        } else {
            mpz_ui_pow_ui(mint, p, 13);
        }
        break;
      }
      case 16: {
        uint qi = find_nextpi(pi);
        uint q = sprimes[qi];
        uint ri = find_nextpi(qi);
        uint r = sprimes[ri];
        uint s = sprimes[find_nextpi(ri)];
        uint pq = lpq(p, q);
        if (lpq(p, s) < 2) {
            mpz_set_ui(mint, p * s);
            mpz_mul_ui(mint, mint, q * r);
        } else if (lpq(q, r) < 2 && lpq(p, r) < 4) {
            mpz_ui_pow_ui(mint, p, 3);
            mpz_mul_ui(mint, mint, q * r);
        } else if (pq < 2) {
            mpz_ui_pow_ui(mint, p * q, 3);
        } else if (pq < 8) {
            mpz_ui_pow_ui(mint, p, 7);
            mpz_mul_ui(mint, mint, q);
        } else {
            mpz_ui_pow_ui(mint, p, 15);
        }
        break;
      }
      case 18: {
        uint qi = find_nextpi(pi);
        uint q = sprimes[qi];
        uint r = sprimes[find_nextpi(qi)];
        uint pq = lpq(p, q);
        if (lpq(p, q * r) < 6) {
            mpz_ui_pow_ui(mint, p * q, 2);
            mpz_mul_ui(mint, mint, r);
        } else if (pq < 3) {
            mpz_ui_pow_ui(mint, p, 5);
            mpz_mul_ui(mint, mint, q * q);
        } else if (pq < 9) {
            mpz_ui_pow_ui(mint, p, 8);
            mpz_mul_ui(mint, mint, q);
        } else {
            mpz_ui_pow_ui(mint, p, 17);
        }
        break;
      }
      case 20: {
        uint qi = find_nextpi(pi);
        uint q = sprimes[qi];
        uint r = sprimes[find_nextpi(qi)];
        /* A: p^4.q.r, B: p^4.q^3, C: p^9.q, D: p^19 */
        if (lpq(q, r) < 2 && lpq(p, r) < 5) {
            mpz_ui_pow_ui(mint, p, 4);
            mpz_mul_ui(mint, mint, q * r);
        } else if (lpq(p, q * q) < 5) {
            mpz_ui_pow_ui(mint, p * q, 3);
            mpz_mul_ui(mint, mint, p);
        } else if (lpq(p, q) < 10) {
            mpz_ui_pow_ui(mint, p, 9);
            mpz_mul_ui(mint, mint, q);
        } else {
            mpz_ui_pow_ui(mint, p, 19);
        }
        break;
      }
      case 24: {
        uint qi = find_nextpi(pi);
        uint q = sprimes[qi];
        uint ri = find_nextpi(qi);
        uint r = sprimes[ri];
        uint s = sprimes[find_nextpi(ri)];
        /* A: p^2.q.r.d, B: p^3.q^2.r, C: p^5.q.r, D: p^5.q^3, E: p^7.q^2,
         * F: p^11.q, G: p^23 */
        uint pq = lpq(p, q);
        bool rp2q = (r / q < p * p);
        if (s < p * q && lpq(p, s) < 3) {
            mpz_set_ui(mint, p * p);
            mpz_mul_ui(mint, mint, q * r);
            mpz_mul_ui(mint, mint, s);
        } else if (lpq(p, q) < 2 && rp2q) {
            mpz_ui_pow_ui(mint, p * q, 2);
            mpz_mul_ui(mint, mint, p * r);
        } else if (rp2q && lpq(q, r) < 2 && lpq(p, r) < 6) {
            mpz_ui_pow_ui(mint, p, 5);
            mpz_mul_ui(mint, mint, q * r);
        } else if (pq < 2) {
            mpz_ui_pow_ui(mint, p * q, 3);
            mpz_mul_ui(mint, mint, p * p);
        } else if (pq < 4) {
            mpz_ui_pow_ui(mint, p, 7);
            mpz_mul_ui(mint, mint, q * q);
        } else if (pq < 12) {
            mpz_ui_pow_ui(mint, p, 11);
            mpz_mul_ui(mint, mint, q);
        } else {
            mpz_ui_pow_ui(mint, p, 23);
        }
        break;
      }
      case 32: {
        uint qi = find_nextpi(pi);
        uint q = sprimes[qi];
        uint ri = find_nextpi(qi);
        uint r = sprimes[ri];
        uint si = find_nextpi(ri);
        uint s = sprimes[si];
        uint u = sprimes[find_nextpi(si)];
        uint pq = lpq(p, q);
        uint pr = lpq(p, r);
        if (p * p > u) {
            mpz_set_ui(mint, p * s);
            mpz_mul_ui(mint, mint, q * r);
            mpz_mul_ui(mint, mint, u);
        } else if (q * q > s && lpq(p, s) < 4) {
            mpz_ui_pow_ui(mint, p, 3);
            mpz_mul_ui(mint, mint, q * r);
            mpz_mul_ui(mint, mint, s);
        } else if (pq < 2 && pr < 4) {
            mpz_ui_pow_ui(mint, p * q, 3);
            mpz_mul_ui(mint, mint, r);
        } else if (q * q > r && pr < 8) {
            mpz_ui_pow_ui(mint, p, 7);
            mpz_mul_ui(mint, mint, q * r);
        } else if (pq < 4) {
            mpz_ui_pow_ui(mint, p, 7);
            mpz_mul_ui(mint, mint, q * q);
            mpz_mul_ui(mint, mint, q);
        } else if (pq < 16) {
            mpz_ui_pow_ui(mint, p, 15);
            mpz_mul_ui(mint, mint, q); 
        } else {
            mpz_ui_pow_ui(mint, p, 31);
        }
        break;
      }
      default:
        /* quick version: given the minimum prime p that can be used, we
         * calculate p^k where k = sum{p_i - 1} over the primes dividing
         * t _with multiplicity_.
         */
        mpz_ui_pow_ui(mint, p, divisors[t].sumpm);
        break;
    }
}

/* order by maxp descending */
int midpp_comparator(const void *va, const void *vb) {
    t_midpp *ma = (t_midpp *)va;
    t_midpp *mb = (t_midpp *)vb;
    return mb->maxp - ma->maxp;
}

void prep_midp(t_level *cur_level) {
    t_level *prev_level = &levels[cur_level->level - 1];
    for (uint vi = 0; vi < k; ++vi) {
        t_value *vp = &value[vi];
        uint vil = cur_level->vlevel[vi];
        t_allocation *ap = &vp->alloc[vil - 1];
        uint t = ap->t;
        if ((t & (t - 1)) == 0)
            continue;
        t_divisors *dp = &divisors[t];
        /* try all divisors until we reach the powers of 2 */
        for (uint di = 0; di < dp->alldiv; ++di) {
            uint x = dp->div[di];
            if ((x & (x - 1)) == 0)
                break;
            /* find range of p for allocating p^e at v_i */
            mpz_add_ui(Z(temp), max, TYPE_OFFSET(vi));
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

    while (1) {
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
        if (midppc == 0)
            break;
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
    t_level *prev_level, t_level *cur_level, t_forcep *fp, uint bi
) {
    assert(fp->count > bi);
    t_value *vp;
    cur_level->is_forced = 1;
    cur_level->bi = bi;
    t_forcebatch *bp = &fp->batch[bi];
    uint terminal = k;

    if (bp->x == 0) {
        apply_null(prev_level, cur_level, fp->p);
        return 1;
    }
    cur_level->have_min = prev_level->have_min;

    uint ep = bp->x - 1;
    if (!apply_primary(prev_level, cur_level, bp->vi, fp->p, bp->x))
        return 0;
    vp = &value[bp->vi];
    if (vp->alloc[ cur_level->vlevel[bp->vi] - 1 ].t == 1)
        terminal = bp->vi;

    for (uint i = 1; i <= bp->vi; ++i) {
        uint e = relative_valuation(i, fp->p, ep);
        if (e == 0)
            continue;
        uint vi = bp->vi - i;
        if (!apply_secondary(prev_level, cur_level, vi, fp->p, e + 1))
            return 0;
        vp = &value[vi];
        if (vp->alloc[ cur_level->vlevel[vi] - 1 ].t == 1)
            terminal = vi;
    }
    for (uint i = 1; bp->vi + i < k; ++i) {
        uint e = relative_valuation(i, fp->p, ep);
        if (e == 0)
            continue;
        uint vi = bp->vi + i;
        if (!apply_secondary(prev_level, cur_level, vi, fp->p, e + 1))
            return 0;
        vp = &value[vi];
        if (vp->alloc[ cur_level->vlevel[vi] - 1 ].t == 1)
            terminal = vi;
    }

    if (terminal < k) {
        walk_1(cur_level, terminal);
        /* nothing more to do */
        return 0;
    }

    /* did we already have a square? */
    if (prev_level->have_square) {
        uint i_diff = abs((int)bp->vi - (int)sq0);
        uint eq = i_diff ? relative_valuation(i_diff, fp->p, ep) : 0;
        /* need extra care only when a secondary hits the square */
        /* so not if a) the primary hits it, or b) nothing hits it */
        if (i_diff == 0 || eq == 0) {
            mpz_ui_pow_ui(px, fp->p, bp->x - 1);
            if (!update_residues(
                prev_level, cur_level, bp->vi, fp->p, bp->x, px, 0
            ))
                return 0;
        } else {
            /* apply the secondary first, then the primary */
            mpz_ui_pow_ui(px, fp->p, eq);
            if (!update_residues(
                prev_level, cur_level, sq0, fp->p, eq + 1, px, 0
            ))
                return 0;
            uint e2 = ep - eq;
            if (e2 > 0) {
                mpz_ui_pow_ui(px, fp->p, e2);
                if (!update_residues(
                    prev_level, cur_level, bp->vi, fp->p, e2 + 1, px, eq
                ))
                    return 0;
            }
        }
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
    if (debugB)
        disp_batch();
    if (opt_alloc) {
        /* check if this is a batch we want to process */
        if (opt_batch_min >= 0
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
    return 1;
}

/* Choose that v_i with the highest t_i still to fulfil, or (on equality)
 * with the highest q_i, but having at least one factor to allocate.
 * If there is no best entry, returns k.
 */
uint best_v0(t_level *cur_level) {
    uint vi, ti = 0;
    mpz_t *qi;
    for (uint vj = 0; vj < k; ++vj) {
        t_value *vpj = &value[vj];
        uint vjl = cur_level->vlevel[vj];
        t_allocation *apj = &vpj->alloc[vjl - 1];
        uint tj = apj->t;
        mpz_t *qj = &apj->q;

        /* skip if no odd prime factor */
        if (divisors[tj].high <= 2)
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
    for (uint vj = 0; vj < k; ++vj) {
        t_value *vpj = &value[vj];
        uint vjl = cur_level->vlevel[vj];
        t_allocation *apj = &vpj->alloc[vjl - 1];
        uint tj = apj->t;
        mpz_t *qj = &apj->q;

        /* skip if no odd prime factor */
        if (divisors[tj].high <= 2)
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
    for (uint vj = 0; vj < k; ++vj) {
        t_value *vpj = &value[vj];
        uint vjl = cur_level->vlevel[vj];
        t_allocation *apj = &vpj->alloc[vjl - 1];
        uint tj = apj->t;
        mpz_t *qj = &apj->q;

        /* skip if no odd prime factor */
        if (divisors[tj].high <= 2)
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
    for (uint vj = 0; vj < k; ++vj) {
        t_value *vpj = &value[vj];
        uint vjl = cur_level->vlevel[vj];
        t_allocation *apj = &vpj->alloc[vjl - 1];
        uint tj = apj->t;
        mpz_t *qj = &apj->q;

        /* skip if no odd prime factor */
        if (divisors[tj].high <= 2)
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

typedef uint (*t_strategy)(t_level *cur_level);
#define NUM_STRATEGIES 4
t_strategy strategies[NUM_STRATEGIES] = {
    &best_v0, &best_v1, &best_v2, &best_v3
};
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
    mpz_add_ui(Z(lp_x), max, TYPE_OFFSET(vi));
    mpz_div(Z(lp_x), Z(lp_x), ap->q);

    if (x == nextt && divisors[x].high == x) {
        /* We are allocating p^{x-1} with x prime, leaving x as the
         * remaining tau; so this and the remaining allocation will
         * be of the form p^{x-1}.q^{x-1}, and we can set the limit
         * to max^{1/2(x-1)}.
         */
        mpz_root(Z(lp_x), Z(lp_x), 2 * (x - 1));
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
    PUX_ALL_DONE,
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
    } /* else we're continuing from known p */

    /* try p^{x-1} for all p until q_i . p^{x-1} . minrest > max + i */
    limp = limit_p(cur_level, vi, x, nextt);
    if (limp == 0) {
        /* force walk */
#ifdef SQONLY
        if (prev_level->have_square)
            walk_v(prev_level, Z(zero));
#else
        walk_v(prev_level, Z(zero));
#endif
        return PUX_ALL_DONE;
    } else if (limp < p + 1)
        return PUX_SKIP_THIS_X; /* nothing to do here */
    if (nextt == 1) {
        cur_level->have_min = prev_level->have_min;
        walk_1_set(cur_level, vi, p, limp, x);
        return PUX_SKIP_THIS_X;
    }

    mpz_add_ui(Z(r_walk), max, vi);
#ifdef LARGE_MIN
    mpz_sub(Z(r_walk), Z(r_walk), min);
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
    }
    if (gain > 1)
        mpz_mul_ui(Z(r_walk), Z(r_walk), gain);
    if (antigain > 1)
        mpz_fdiv_q_ui(Z(r_walk), Z(r_walk), antigain);
    if (mpz_fits_ulong_p(Z(r_walk))
        && mpz_get_ui(Z(r_walk)) < limp - p
    ) {
#ifdef SQONLY
        if (prev_level->have_square)
            walk_v(prev_level, Z(zero));
        else if (cur_level->level > 1 && !prev_level->is_forced)
            level_setp(prev_level, prev_level->limp);
#else
        walk_v(prev_level, Z(zero));
#endif
        return PUX_ALL_DONE;
    }
  force_unforced:
    level_setp(cur_level, p);
    cur_level->x = x;
    cur_level->limp = limp;
    cur_level->max_at = seen_best;
    /* TODO: do some constant alloc stuff in advance */
    return PUX_DO_THIS_X;
}

typedef enum {
    IS_DEEPER = 0,
    IS_NEXTX,
    IS_NEXT,
    IS_MIDP
} e_is;
/* On recovery, set up the recursion stack to the point we had reached.
 * Returns IS_DEEPER if we should continue by recursing deeper from this
 * point; returns IS_NEXTX if we should continue by advancing the power
 * applied at the current position; returns IS_NEXT if we should continue
 * by advancing the current level; and returns IS_MIDP if we should continue
 * via walk_midp().
 */
e_is insert_stack(void) {
    e_is jump = IS_DEEPER;

    /* first insert forced primes */
    for (uint fpi = 0; fpi < forcedp; ++fpi) {
        t_forcep *fp = &forcep[fpi];
        uint p = fp->p;
        uint maxx = 0, mini;
        for (uint vi = 0; vi < k; ++vi) {
            t_fact *rs = &rstack[vi];
            if (rs->count && rs->ppow[rs->count - 1].p == p) {
                uint x = rs->ppow[rs->count - 1].e + 1;
                if (maxx < x) {
                    maxx = x;
                    mini = vi;
                }
            }
        }
        /* find the batch */
        uint bi;
        if (maxx == 0) {
            bi = fp->count - 1;
            if (fp->batch[bi].x != 0)
                goto insert_check;
#if defined(TYPE_a)
            if (fp->batch[bi].vi == 0) {
                mini = 0;
                goto have_batch;
            }
#endif
            /* this prime unforced, so any remaining ones are too */
            break;
        }

        for (bi = 0; bi < fp->count; ++bi) {
            t_forcebatch *b = &fp->batch[bi];
            if (b->x == maxx && b->vi == mini)
                break;
        }
        if (bi >= fp->count) {
            if (fp->batch[fp->count -1].x != 0)
                fail("no batch found for %u^{%u-1} at v_%u", p, maxx, mini);
            /* this prime unforced, so any remaining ones are too */
            break;
        }

      have_batch: ;
        t_level *prev_level = &levels[level - 1];
        t_level *cur_level = &levels[level];
        reset_vlevel(cur_level);
        cur_level->is_forced = 1;
        cur_level->bi = bi;
        cur_batch_level = level;

        if (maxx == 0) {
            apply_null(prev_level, cur_level, p);
            goto inserted_batch;
        }

        /* progress is shown just before we apply, so on recovery it is
         * legitimate for the last one to fail */
        --rstack[mini].count;
        if (!apply_single(prev_level, cur_level, mini, p, maxx)) {
            jump = IS_NEXT;
            goto insert_check;
        }

        for (uint j = 1; j <= mini; ++j) {
            uint vj = mini - j;
            uint e = relative_valuation(j, p, maxx - 1);
            if (e == 0)
                continue;
            t_fact *rs = &rstack[vj];
            t_ppow *rsp = rs->count ? &rs->ppow[rs->count - 1] : NULL;
            if (!rsp || rsp->p != p || rsp->e != e)
                fail("missing secondary %u^%u at %u", p, e, vj);
            --rs->count;

            if (!apply_secondary(prev_level, cur_level, vj, p, e + 1))
                fail("could not apply_secondary(%u, %lu, %u)", vj, p, e + 1);
        }
        for (uint j = 1; mini + j < k; ++j) {
            uint vj = mini + j;
            uint e = relative_valuation(j, p, maxx - 1);
            if (e == 0)
                continue;
            t_fact *rs = &rstack[vj];
            t_ppow *rsp = rs->count ? &rs->ppow[rs->count - 1] : NULL;
            if (!rsp || rsp->p != p || rsp->e != e)
                fail("missing secondary %u^%u at %u", p, e, vj);
            --rs->count;

            if (!apply_secondary(prev_level, cur_level, vj, p, e + 1))
                fail("could not apply_secondary(%u, %lu, %u)", vj, p, e + 1);
        }
      inserted_batch:
        ++level;
    }
    /* now insert the rest */
    while (1) {
        t_level *prev_level = &levels[level - 1];
        t_level *cur_level = &levels[level];
        reset_vlevel(cur_level);
        uint vi = best_v(cur_level);
        if (vi == k)
            break;
        t_fact *rs = &rstack[vi];
        if (rs->count == 0)
            break;
        --rs->count;

        ulong p = rs->ppow[rs->count].p;
        uint x = rs->ppow[rs->count].e + 1;
        t_value *vp = &value[vi];
        uint vil = cur_level->vlevel[vi];
        uint ti = vp->alloc[vil - 1].t;
        t_divisors *dp = &divisors[ti];
        if (dp->highdiv == 0)
            fail("best_v() returned %u, but nothing to do there", vi);

        uint di;
        for (di = 0; di <= dp->highdiv; ++di) {
            if (di == dp->highdiv)
                fail("x=%u is not a highdiv of t=%u\n", x, ti);
            if (dp->div[di] == x)
                break;
        }
        cur_level->vi = vi;
        cur_level->ti = ti;
        cur_level->di = di;

        e_pux pux = prep_unforced_x(prev_level, cur_level,
                p, init_pattern ? 1 : 0);
        switch (pux) {
          case PUX_NOTHING_TO_DO:
          case PUX_SKIP_THIS_X:
            if (ti == x) {
                /* legitimate skip after walk_1_set */
                jump = IS_NEXTX;
                goto insert_check;
            }
            fail("prep_nextt %u for %lu^%u at %u\n", pux, p, x, vi);
          case PUX_ALL_DONE:
            /* we have now acted on this */
            jump = IS_NEXT;
            goto insert_check;
        }

        level_setp(cur_level, p);
        /* progress is shown just before we apply, so on recovery it is
         * legitimate for the last one to fail */
        if (!apply_single(prev_level, cur_level, vi, p, x)) {
            --cur_level->vlevel[cur_level->vi];
            jump = IS_NEXT;
            goto insert_check;
        }
        ++level;
    }
  insert_check:
    /* check we found them all */
    for (uint vi = 0; vi < k; ++vi) {
        t_fact *rs = &rstack[vi];
        uint c = rs->count;
        while (c) {
            t_ppow pp = rs->ppow[--c];
            if (!init_pattern)
                fail("failed to inject %lu^%u at v_%u", pp.p, pp.e, vi);
            t_level *prev_level = &levels[level - 1];
            t_level *cur_level = &levels[level];
            reset_vlevel(cur_level);
            if (!apply_single(prev_level, cur_level, vi, pp.p, pp.e + 1))
                fail("error injecting %lu^%u at v_%u", pp.p, pp.e, vi);
            ++level;
        }
    }
    if (init_pattern) {
        for (uint l = 1; l < level; ++l)
            levels[l].is_forced = 1;
        final_level = level;
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
    uint x, fi, bi;
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

    while (1) {
        ++countr;
        prev_level = &levels[level - 1];
        cur_level = &levels[level];

        /* recurse deeper */
        fi = level - 1;
        if (fi < forcedp && (fi == 0 || prev_level->is_forced)) {
            fp = &forcep[fi];
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
            uint vi = best_v(cur_level);
            /* TODO: walk_v() directly at previous level, if best_v() would
             * give same result each time.
             */
            if (vi == k) {
#ifdef SQONLY
                if (prev_level->have_square)
                    walk_v(prev_level, Z(zero));
                else if (level > 1 && !prev_level->is_forced)
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
            if (dp->highdiv == 0)
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
                case PUX_ALL_DONE:
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
        --level;
        if (level <= final_level)
            break;
        prev_level = &levels[level - 1];
        cur_level = &levels[level];
        if (cur_level->is_forced) {
            /* unapply the batch */
            reset_vlevel(cur_level);
        } else
            --cur_level->vlevel[cur_level->vi];
        /* goto continue_recurse; */
      continue_recurse:
        if (cur_level->is_forced) {
            fi = level - 1;
            fp = &forcep[fi];
            bi = cur_level->bi + 1;
          continue_forced:
            if (bi >= fp->count) {
                goto derecurse;
            }
            if (fp->batch[bi].x == 0
#if defined(TYPE_a)
                && fp->batch[bi].vi != 0
#endif
            ) {
                /* tail batch: continue with this prime unforced */
                cur_level->is_forced = 0;
                reset_vlevel(cur_level);
                if (process_batch(prev_level))
                    goto unforced;
                goto derecurse;
            }
            if (apply_batch(prev_level, cur_level, fp, bi)
                && (level != forcedp || process_batch(cur_level))
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
            ulong p = cur_level->p;
            /* recalculate limit if we have an improved maximum */
            if (improve_max && seen_best > cur_level->max_at)
                switch (prep_unforced_x(prev_level, cur_level, p, 0)) {
                  case PUX_NOTHING_TO_DO:
                  case PUX_ALL_DONE:
                    goto continue_unforced_x;
                }
            /* note: only valid to use from just below here */
          redo_unforced:
            p = prime_iterator_next(&cur_level->piter);
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
                /* not redo_unforced, we may have improved max */
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
        else if (arg[1] == 'p')
            set_cap(&arg[2]);
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
        else if (arg[1] == 'r') {
            rpath = (char *)malloc(strlen(&arg[2]) + 1);
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
        else if (arg[1] == 'a')
            opt_alloc = 1;
        else if (arg[1] == 'b')
            set_batch(&arg[2]);
        else if (arg[1] == 'o')
            opt_print = 1;
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
                break;
              case 'W':
                debugw = 1;
                debugW = 1;
                break;
              case 'b':
                debugb = 1;
                break;
              case 'B':
                debugb = 1;
                debugB = 1;
                break;
              case 'x':
                debugx = 1;
                break;
              default:
                fail("Unknown debug option '%s'", arg);
            }
        } else if (arg[1] == 'v')
            vt100 = 1;
        else if (arg[1] == 'j') {
            strategy = strtoul(&arg[2], NULL, 10);
            if (strategy >= NUM_STRATEGIES)
                fail("Invalid strategy %u", strategy);
            strategy_set = 1;
        } else
            fail("unknown option '%s'", arg);
    }
    if (init_pattern)
        skip_recover = 1;
    if (i + 2 == argc) {
        n = strtoul(argv[i++], NULL, 10);
        k = strtoul(argv[i++], NULL, 10);
    } else
        fail("wrong number of arguments");
    if (force_all > k)
        fail("require force_all <= k");

    init_post();
    report_init(stdout, argv[0]);
    if (rfp) report_init(rfp, argv[0]);

    bool jump = IS_DEEPER;
    if (rstack) {
        jump = insert_stack();
        /* FIXME: temporary fix for recovering a single batch run.
         * It won't do the right thing for a range of batches.
         */
        if (batch_alloc == 0) {
            if (opt_batch_min >= 0)
                batch_alloc = opt_batch_min + 1;
            else
                ++batch_alloc;
        }
    }
    recurse(jump);
    keep_diag();

    double tz = utime();
    report("367 c%sul(%u, %u): recurse %lu, walk %lu, walkc %lu (%.2fs)\n",
#if defined(TYPE_o)
            "o",
#elif defined(TYPE_a)
            "a",
#elif defined(TYPE_r)
            "r",
#endif
            n, k, countr, countw, countwi, seconds(tz));
    if (seen_best)
        report("200 f(%u, %u) = %Zu (%.2fs)\n", n, k, best, seconds(tz));
    done();
    return 0;
}
