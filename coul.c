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
#include <sys/times.h>
#include "coulfact.h"
#include "diag.h"
#include "rootmod.h"

/* from MPUG */
#include "factor.h"
#include "gmp_main.h"
#include "utility.h"
#include "primality.h"

/* primary parameters - we are searching for D(n, k), the least d such
 * that tau(d + i) = n for all 0 <= i < k.
 */
uint n, k;

/* stash of mpz_t, initialized once at start */
typedef enum {
    zero, zone,                 /* constants */
    res_m, res_e, res_px,       /* check_residue */
    sqm_t, sqm_q, sqm_b, sqm_z, sqm_x,  /* sqrtmod_t */
    uc_minusvi,                 /* update_chinese */
    wv_ati, wv_end, wv_cand,    /* walk_v */
    wv_startr, wv_endr, wv_qqr, wv_r, wv_rx, wv_temp,
    w1_v, w1_j, w1_r,           /* walk_1 */
    lp_x, lp_mint,              /* limit_p */
    r_walk,                     /* recurse */

    sdm_p, sdm_r,               /* small_divmod (TODO) */
    np_p,                       /* next_prime (TODO) */

    MAX_ZSTASH
} t_zstash;
mpz_t *zstash;
static inline mpz_t *ZP(t_zstash e) { return &zstash[e]; }
#define Z(e) *ZP(e)
/* additional arrays of mpz_t initialized once at start */
mpz_t *wv_o = NULL, *wv_qq = NULL;  /* wv_o[k], wv_qq[k] */

typedef unsigned char bool;

/* used to store disallowed inverses in walk_v() */
typedef struct s_mod {
    ulong v;
    ulong m;
} t_mod;

/* 'divisors[i].div' is a list of divisors of 'i' in descending order of
 * highest prime factor, then ascending. 'high' is the highest prime
 * factor of 'i'; 'alldiv' is the number of factors; 'highdiv' is the
 * number of factors that are a multiple of 'high'; 'sumpm' is sum{p_i - 1}
 * of the primes dividing 'i', with multiplicity.
 * Eg divisors[18] = {
 *   alldiv = 6, highdiv = 4, high = 3, sumpm = 5 = (3-1)+(3-1)+(2-1),
 *   div = = [3, 6, 9, 18, 2, 1]
 * }
 */
typedef struct s_divisors {
    uint alldiv;
    uint highdiv;
    uint high;
    uint sumpm;
    uint *div;
} t_divisors;
t_divisors *divisors = NULL;

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

/* When allocation forces the residue of some v_i to be square, we want
 * to capture some information, and check if that is consistent with
 * existing allocations.
 */
#define MAX_SQUARE 2
typedef struct s_square {
    uint vi;
    mpz_t m;    /* v_{vi} = mz^2 for some z */
} t_square;
t_square *squares = NULL;
t_square *sqspare = NULL;

/* Each level of "recursion" allocates one prime power p^{x-1} with x | n
 * to one value v_i. It may be "forced", in which case it is part of a
 * batch of simultaneous allocations of the same p to different i (and
 * in which case derecursion should unwind the whole batch), or not, in
 * which case no other v_j will be divisible by p.
 */
typedef struct s_level {
    bool is_forced;
    uint vi;    /* allocation of p^x into v_i */
    ulong p;
    uint x;
    uint have_square;   /* number of v_i residues forced square so far */
    uint nextpi;    /* index of least prime not yet allocated */
    /* union */
        uint bi;    /* batch index, if forced */
    /* .. with */
        uint di;    /* divisor index, if unforced */
        uint ti;    /* target tau for v_i */
        ulong limp; /* limit for p */
        uint max_at;/* which max value used for limp calculation */
    /* end union */
    mpz_t aq;   /* running LCM of allocated p^x */
    mpz_t rq;   /* running CRT of (-i) % p^x */
} t_level;
t_level *levels = NULL;
uint level = 0;

/* Each value v_0 to v_{k-1} has had 'level' allocations of prime powers
 * p_i^{x_i-1}; q tracks the product of those prime powers, and t tracks
 * our target tau - starting at n, and divided by x_i on each allocation.
 */
typedef struct s_allocation {
    ulong p;
    uint x;
    mpz_t q;
    uint t;
} t_allocation;
typedef struct s_value {
    uint vlevel;
    t_allocation *alloc;    /* size maxfact */
} t_value;
t_value *value = NULL;

/* saved counts of allocations in each value before applying nth forced prime */
uint *vlevels = NULL;
uint vl_forced = 0;
static inline uint *VLP(uint vlevel) { return &vlevels[vlevel * k]; }
static inline void STOREVL(uint vli) {
    uint *vlp = VLP(vli);
    for (uint vi = 0; vi < k; ++vi)
        vlp[vi] = value[vi].vlevel;
}
static inline void FETCHVL(uint vli) {
    uint *vlp = VLP(vli);
    for (uint vi = 0; vi < k; ++vi)
        value[vi].vlevel = vlp[vi];
}

/* list of some small primes, at least enough for one per allocation  */
uint *sprimes = NULL;
uint nsprimes;

long ticks_per_second;
/* set to utime at start of run, minus last timestamp of recovery file */
clock_t ticks = 0;
struct tms time_buf;
static inline clock_t utime(void) {
    times(&time_buf);
    return time_buf.tms_utime;
}

mpz_t min, max;     /* limits to check for v_0 */
uint seen_best = 0; /* number of times we've improved max */
ulong gain = 0;     /* used to fine-tune balance of recursion vs. walk */
ulong antigain = 0;
/* maxp is the greatest prime we should attempt to allocate; minp is the
 * threshold that at least one allocated prime should exceed (else we can
 * skip the walk)
 */
/* TODO: implement minp */
uint minp = 0, maxp = 0;
uint runid = 0;     /* runid for log file */
bool opt_print = 0; /* print candidates instead of fully testing them */
bool debug = 0;     /* diag and keep every case seen */

char *rpath = NULL; /* path to log file */
FILE *rfp = NULL;   /* file handle to log file */
bool start_seen = 0;    /* true if log file has been written to before */
t_fact *rstack = NULL;  /* point reached in recovery log file */
bool have_rwalk = 0;    /* true if recovery is mid-walk */
mpz_t rwalk_from;
mpz_t rwalk_to;

t_fact nf;      /* factors of n */
uint tn;        /* tau(n) */
uint maxfact;   /* count of prime factors dividing n, with multiplicity */
uint maxodd;    /* as above for odd prime factors */
uint *maxforce = NULL;  /* max prime to force at v_i */
mpz_t px;       /* p^x */

#define DIAG 1
#define LOG 600
clock_t diag_delay, log_delay, diagt, logt;
ulong countr, countw, countwi;
#define DIAG_BUFSIZE (3 + k * maxfact * (20 + 1 + 5 + 1) + 1)
char *diag_buf = NULL;

void prep_show_v(void) {
    uint offset = 0;
    for (uint vi = 0; vi < k; ++vi) {
        t_value *vp = &value[vi];
        if (vi)
            diag_buf[offset++] = ' ';
        if (vp->vlevel == 0)
            diag_buf[offset++] = '.';
        else {
            for (uint ai = 0; ai < vp->vlevel; ++ai) {
                t_allocation *ap = &vp->alloc[ai];
                if (ai)
                    diag_buf[offset++] = '.';
                offset += sprintf(&diag_buf[offset], "%lu", ap->p);
                if (ap->x > 2)
                    offset += sprintf(&diag_buf[offset], "^%u", ap->x - 1);
            }
        }
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

double seconds(clock_t t1) {
    return (double)(t1 - ticks) / ticks_per_second;
}

void diag_plain(void) {
    clock_t t1 = utime();

    prep_show_v();  /* into diag_buf */
    diag("%s", diag_buf);
    if (debug)
        keep_diag();
    diagt = t1 + diag_delay;

    if (rfp && t1 >= logt) {
        fprintf(rfp, "305 %s (%.2fs)\n", diag_buf, seconds(t1));
        logt = t1 + log_delay;
    }
}

void diag_walk_v(ulong ati, ulong end) {
    clock_t t1 = utime();

    prep_show_v();  /* into diag_buf */
    if (!(debug && ati))
        diag("%s: %lu / %lu", diag_buf, ati, end);
    if (debug)
        keep_diag();
    diagt = t1 + diag_delay;

    if (rfp && t1 >= logt) {
        fprintf(rfp, "305 %s: %lu / %lu (%.2fs)\n",
                diag_buf, ati, end, seconds(t1));
        logt = t1 + log_delay;
    }
}

void diag_walk_zv(mpz_t ati, mpz_t end) {
    clock_t t1 = utime();

    prep_show_v();  /* into diag_buf */
    if (!(debug && mpz_sgn(ati)))
        diag("%s: %Zu / %Zu", diag_buf, ati, end);
    if (debug)
        keep_diag();
    diagt = t1 + diag_delay;

    if (rfp && t1 >= logt) {
        gmp_fprintf(rfp, "305 %s: %Zu / %Zu (%.2fs)\n",
                diag_buf, ati, end, seconds(t1));
        logt = t1 + log_delay;
    }
}

void candidate(mpz_t c) {
    keep_diag();
    clock_t t1 = utime();
    report("202 Candidate %Zu (%.2fs)\n", c, seconds(t1));
    if (mpz_cmp(c, max) <= 0) {
        mpz_set(max, c);
        ++seen_best;
    }
}

void free_levels(void) {
    for (uint i = 0; i < k * maxfact + 1; ++i) {
        t_level *l = &levels[i];
        mpz_clear(l->aq);
        mpz_clear(l->rq);
    }
    free(levels);
}

void init_levels(void) {
    /* CHECKME: can this be maxodd * k + forcedp? */
    levels = (t_level *)calloc(k * maxfact + 1, sizeof(t_level));
    for (uint i = 0; i < k * maxfact + 1; ++i) {
        t_level *l = &levels[i];
        mpz_init(l->aq);
        mpz_init(l->rq);
    }
    mpz_set_ui(levels[0].aq, 1);
    mpz_set_ui(levels[0].rq, 0);
    levels[0].have_square = 0;
    levels[0].nextpi = 0;
    level = 1;
}

void free_value(void) {
    for (int i = 0; i < k; ++i) {
        t_value *v = &value[i];
        for (int j = 0; j < maxfact; ++j)
            mpz_clear(v->alloc[j].q);
        free(v->alloc);
    }
    free(value);
}

void init_value(void) {
    value = (t_value *)malloc(k * sizeof(t_value));
    for (int i = 0; i < k; ++i) {
        t_value *v = &value[i];
        v->vlevel = 0;
        v->alloc = (t_allocation *)malloc(maxfact * sizeof(t_allocation));
        for (uint j = 0; j < maxfact; ++j)
            mpz_init(v->alloc[j].q);
    }
}

void done(void) {
    free(diag_buf);
    if (wv_qq)
        for (uint i = 0; i < k; ++i)
            mpz_clear(wv_qq[i]);
    free(wv_qq);
    if (wv_o)
        for (uint i = 0; i < k; ++i)
            mpz_clear(wv_o[i]);
    free(wv_o);
    free(vlevels);
    free_value();
    free_levels();
    free(sprimes);
    if (forcep)
        for (int i = 0; i < forcedp; ++i)
            free(forcep[i].batch);
    free(forcep);
    free(maxforce);
    if (divisors)
        for (int i = 0; i <= n; ++i)
            free(divisors[i].div);
    free(divisors);
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
    for (uint i = 0; i < MAX_SQUARE + 1; ++i)
        mpz_clear(squares[i].m);
    free(squares);
    mpz_clear(px);
    free_fact(&nf);
    mpz_clear(max);
    mpz_clear(min);
    done_rootmod();
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

void init_pre(void) {
    _GMP_init();
    init_rootmod();
    ticks_per_second = sysconf(_SC_CLK_TCK);
    ticks = utime();
    mpz_init_set_ui(min, 0);
    mpz_init_set_ui(max, 0);
    init_fact(&nf);
    mpz_init(px);
    squares = (t_square *)malloc((MAX_SQUARE + 1) * sizeof(t_square));
    sqspare = &squares[MAX_SQUARE];
    for (uint i = 0; i < MAX_SQUARE + 1; ++i)
        mpz_init(squares[i].m);
    zstash = (mpz_t *)malloc(MAX_ZSTASH * sizeof(mpz_t));
    for (t_zstash i = 0; i < MAX_ZSTASH; ++i)
        mpz_init(Z(i));
    mpz_set_ui(Z(zero), 0);
    mpz_set_ui(Z(zone), 1);
}

/* Parse a "305" log line for initialization.
 * Input string should point after the initial "305 ".
 */
void parse_305(char *s) {
    double dtime;
    t_ppow pp;

    rstack = (t_fact *)malloc(k * sizeof(t_fact));
    for (int i = 0; i < k; ++i)
        init_fact(&rstack[i]);

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
    if (EOF == sscanf(s, " (%lfs)\n", &dtime))
        fail("could not parse 305 time: '%s'", s);
    ticks -= (clock_t)dtime * ticks_per_second;
}

void recover(void) {
    char *last305 = NULL;
    char *last202 = NULL;
    char *curbuf = NULL;
    size_t len = 120;

    while (1) {
        ssize_t nread = getline(&curbuf, &len, rfp);
        if (nread < 0) {
            if (errno == 0)
                break;
            fail("error reading %s: %s", rpath, strerror(errno));
        }
        if (curbuf[nread - 1] != '\n'
                || memchr(curbuf, 0, nread) != NULL) {
            /* corrupt line, file should be truncated */
            off_t offset = ftello(rfp);
            if (offset == -1)
                fail("could not ask offset: %s", strerror(errno));
            ftruncate(fileno(rfp), offset - nread);
            if (freopen(NULL, "a+", rfp) == NULL)
                fail("could not reopen %s: %s", rpath, strerror(errno));
            break;
        }
        if (strncmp("305 ", curbuf, 4) == 0) {
            char *t = last305;
            last305 = curbuf;
            curbuf = t;
        } else if (strncmp("202 ", curbuf, 4) == 0) {
            char *t = last202;
            last202 = curbuf;
            curbuf = t;
        } else if (strncmp("001 ", curbuf, 4) == 0) {
            /* TODO: parse and check for consistent options */
            start_seen = 1;
        } else if (strncmp("000 ", curbuf, 4) == 0)
            ;   /* comment */
        else
            fail("unexpected log line %.3s in %s", curbuf, rpath);
    }
    if (last202) {
        int start, end;
        mpz_t cand;
        if (EOF == sscanf(last202, "202 Candidate %n%*[0-9]%n (%*[0-9.]s)\n",
                &start, &end))
            fail("error parsing 202 line '%s'", last202);
        last202[end] = 0;
        mpz_init_set_str(cand, &last202[start], 10);
        if (mpz_sgn(max) == 0 || mpz_cmp(max, cand) > 0)
            mpz_set(max, cand);
        mpz_clear(cand);
        free(last202);
    }
    if (last305)
        parse_305(last305 + 4);
    free(curbuf);
    free(last305);
    free(last202);
}

int cmp_high(const void *va, const void *vb) {
    uint a = *(uint *)va, b = *(uint *)vb;
    return divisors[b].high - divisors[a].high;
}

/* TODO: use MPU code for ulong next_prime */
ulong next_prime(ulong cur) {
    mpz_set_ui(Z(np_p), cur);
    _GMP_next_prime(Z(np_p));
    if (mpz_fits_ulong_p(Z(np_p)))
        return mpz_get_ui(Z(np_p));
    diag_plain();
    keep_diag();
    report("002 next_prime overflow\n");
    exit(1);
}

/* recurse() wants the list of powers to try: each divisor of t_i (which
 * itself divides n) that is divisible by the highest odd prime factor
 * dividing t_i, in increasing order.
 * prep_forcep() wants the full list of divisors, but in similar order.
 * For each power, recurse() also wants to know which powers to skip
 * if the previous power was a given value, but that's simply:
 * skip x' if x' < x and high(x') == high(x)
 */
void prep_fact(void) {
    t_fact f;

    divisors = (t_divisors *)calloc(n + 1, sizeof(t_divisors));
    init_fact(&f);
    for (uint i = 1; i <= n; ++i) {
        if (n % i)
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
    }
    free_fact(&f);
}

void prep_mintau(void) {
    /* max tau we care about */
    uint maxt = n / (nf.count ? nf.ppow[nf.count - 1].p : 1);

    /* max factors in a factorization of maxt */
    int cp = -1;
    for (int i = 0; i < nf.count; ++i)
        cp += nf.ppow[i].e;

    /* max allocation per element is number of odd prime factors */
    int cop = cp + 1 - (nf.count ? 0 : nf.ppow[0].e);

    /* max total allocations exclduding current one, ignoring forced primes */
    int max_alloc = cop * k - 1;

    /* we need at most 1 per factor of a factorization, plus 1 for each
     * allocation, plus 1 per forced prime (which can be used without
     * filling a normal allocation).
     * Note: prime_count(k) will be forcedp.
     * Note: this could be reduced by the min number of forced allocations
     * that will use allocatable factors (ie divisible by odd prime).
     */
    int need = cp + max_alloc + simple_prime_count(k);

    /* TODO: work out first what we want mintau() to do; we probably want
     * to fill this cache lazily, or not cache at all.
     */
}

void prep_maxforce(void) {
    maxforce = (uint *)malloc(k * sizeof(uint));
    if ((n & 3) != 0) {
        for (int i = 0; i < k; ++i)
            maxforce[i] = k;
    } else
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
     * usually be less. */
    nsprimes = maxodd * k + forcedp;
    sprimes = (uint *)malloc(nsprimes * sizeof(uint));
    uint p = 1;
    for (uint i = 0; i < nsprimes; ++i) {
        p = next_prime(p);
        sprimes[i] = p;
    }
}

void prep_forcep(void) {
    mpz_t pz;
    uint p;
    uint pi[k];

    forcedp = 0;
    mpz_init_set_ui(pz, 1);
    while (1) {
        _GMP_next_prime(pz);
        p = mpz_get_ui(pz);
        if (p > k)
            break;
        pi[forcedp++] = p;
    }
    mpz_clear(pz);

    uint first_bad = n + 1;
    for (uint div = 2; div < n; ++div)
        if (n % div) {
            first_bad = div;
            break;
        }

    forcep = (t_forcep *)malloc(forcedp * sizeof(t_forcep));
    t_divisors *d = &divisors[n];
    for (uint fpi = 0; fpi < forcedp; ++fpi) {
        t_forcep *fp = &forcep[fpi];
        fp->p = p = pi[fpi];
        fp->count = 0;
        fp->batch = (t_forcebatch *)malloc(tn * k * sizeof(t_forcebatch));

        uint x = 1, px = 1;
        while (px * p < k) {
            ++x;
            px *= p;
        }
        uint bad_pow = k + 1;
        if (first_bad <= x) {
            bad_pow = 1;
            for (uint i = 1; i < first_bad; ++i)
                bad_pow *= p;
        }

        bool keep_single = ((n & 3) || p <= force_all) ? 1 : 0;
        bool skipped = 0;
        for (uint vi = 0; vi < k; ++vi) {
            /* skip if forcing p^{x-1} at v_i would require p^{y-1} at v_j
             * such that not y | n.
             */
            if (vi + bad_pow < k || vi >= bad_pow)
                continue;
            if (p > maxforce[vi] && !keep_single) {
                skipped = 1;
                continue;
            }
            for (uint di = 0; di < d->alldiv; ++di) {
                uint fx = d->div[di];
                if (fx < x)
                    continue;   /* would not be highest power */
                if (fx == x) {
                    if (vi >= px)
                        continue;   /* would not be first highest power */
                    if (vi + px * (p - 1) < k)
                        continue;   /* would not be highest power */
                }
                fp->batch[fp->count++] = (t_forcebatch){ .vi = vi, .x = fx };
            }
        }
        if (fp->count == 0) {
            forcedp = fpi;
            free(fp->batch);
            break;
        }
        if (skipped)
            fp->batch[fp->count++] = (t_forcebatch){ .x = 0 };
        fp->batch = (t_forcebatch *)realloc(fp->batch,
                fp->count * sizeof(t_forcebatch));
    }
}

void init_post(void) {
    if (runid) {
        char buf[100];
        snprintf(buf, sizeof(buf), "%s/%u.%u-%u",
                "logs/o", n, k, runid);
        rpath = (char *)malloc(strlen(buf) + 1);
        strcpy(rpath, buf);
    }
    if (rpath) {
        printf("path %s\n", rpath);
        rfp = fopen(rpath, "a+");
        if (rfp == NULL)
            fail("%s: %s", rpath, strerror(errno));
        setlinebuf(rfp);
        recover();
    }
#ifdef HAVE_SETPROCTITLE
    setproctitle("oul(%lu %lu)", n, k);
#endif
    simple_fact(n, &nf);
    tn = simple_tau(&nf);
    maxfact = 0;
    for (int i = 0; i < nf.count; ++i)
        maxfact += nf.ppow[i].e;
    maxodd = maxfact - nf.ppow[0].e;    /* n is always even */

    prep_fact();
    prep_maxforce();
    prep_forcep();
    prep_primes();  /* needs forcedp */
    prep_mintau();

    diag_delay = (debug) ? 0 : DIAG * ticks_per_second;
    log_delay = (debug) ? 0 : LOG * ticks_per_second;
    diagt = diag_delay;
    logt = log_delay;

    init_levels();
    init_value();
    vlevels = (uint *)malloc(forcedp * k * sizeof(uint));
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
    fprintf(fp, "001 %s%s", (start_seen ? "recover " : ""), prog);
    if (opt_print)
        fprintf(fp, " -o");
    if (minp || maxp) {
        fprintf(fp, " -p");
        if (minp)
            fprintf(fp, "%u:", minp);
        if (maxp)
            fprintf(fp, "%u", maxp);
    }
    if (force_all)
        fprintf(fp, " -f%u", force_all);
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
    fprintf(fp, " %u %u\n", n, k);
}

void set_minmax(char *s) {
    char *t = strchr(s, ':');
    if (t) {
        *t = 0;
        if (*s)
            mpz_set_str(min, s, 10);
        else
            mpz_set_ui(min, 0);
        if (t[1])
            mpz_set_str(max, &t[1], 10);
        else
            mpz_set_ui(max, 0);
    } else {
        mpz_set_ui(min, 0);
        mpz_set_str(max, s, 10);
    }
}

void set_gain(char *s) {
    char *t = strchr(s, ':');
    if (t) {
        *t = 0;
        antigain = *s ? strtoul(s, NULL, 10) : 0;
        gain = t[1] ? strtoul(&t[1], NULL, 10) : 0;
    } else {
        antigain = 0;
        gain = strtoul(s, NULL, 10);
    }
}

void set_cap(char *s) {
    char *t = strchr(s, ':');
    if (t) {
        *t = 0;
        minp = *s ? strtoul(s, NULL, 10) : 0;
        maxp = t[1] ? strtoul(&t[1], NULL, 10) : 0;
    } else {
        minp = 0;
        maxp = strtoul(s, NULL, 10);
    }
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

/* This allocation uses what was the next unused prime, so find the
 * index of the new next unused prime.
 */
uint find_nextpi(t_level *cur) {
    uint pi = cur->nextpi;
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

bool test_other(mpz_t qq, mpz_t o, ulong ati, uint t) {
    mpz_mul_ui(Z(wv_cand), qq, ati);
    mpz_add(Z(wv_cand), Z(wv_cand), o);
    return is_tau(Z(wv_cand), t);
}

bool test_zother(mpz_t qq, mpz_t o, mpz_t ati, uint t) {
    mpz_mul(Z(wv_cand), qq, ati);
    mpz_add(Z(wv_cand), Z(wv_cand), o);
    return is_tau(Z(wv_cand), t);
}

uint gcd_divisors(uint t) {
    assert(t > 1);
    t_divisors *dp = &divisors[t];
    uint g = dp->div[0] - 1;
    for (uint di = 1; di < dp->alldiv; ++di)
        g = tiny_gcd(g, dp->div[di] - 1);
    return g;
}

void walk_v(t_level *cur_level, mpz_t start) {
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
        q[vi] = vp->vlevel ? &vp->alloc[vp->vlevel - 1].q : ZP(zone);
        t[vi] = vp->vlevel ? vp->alloc[vp->vlevel - 1].t : n;
        mpz_divexact(wv_qq[vi], *aq, *q[vi]);
        mpz_add_ui(wv_o[vi], *m, vi);
        mpz_divexact(wv_o[vi], wv_o[vi], *q[vi]);
        for (uint ai = 0; ai < vp->vlevel; ++ai) {
            t_allocation *ap = &vp->alloc[ai];
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
/* CHECKME: after parallelization, check if we have a use for this */
/*      else if (t[vi] == 4)
            need_semiprime[nsc++] = vi;
*/
        else
            need_other[noc++] = vi;
    }

    if (nqc) {
        uint sqi = need_square[0];
        mpz_t *oi = &wv_o[sqi];
        mpz_t *qi = q[sqi];
        mpz_t *qqi = &wv_qq[sqi];
        uint ti = t[sqi];
#if 0
        if (npc > 1) {
            /* TODO: special case Pell solver */
        }
#endif
        uint xi = gcd_divisors(ti);
        /* we need to find all r: r^x_i == o_i (mod qq_i) */
        mpz_t *xmod;
        uint xmc = allrootmod(&xmod, *oi, xi, *qqi);
        if (xmc == 0)
            return;
        uint rindex = 0;
        if (mpz_sgn(Z(wv_ati)) > 0) {
            mpz_mul(Z(wv_startr), Z(wv_ati), *qqi);
            mpz_add(Z(wv_startr), Z(wv_startr), *oi);
            mpz_root(Z(wv_startr), Z(wv_startr), xi);
            mpz_fdiv_qr(Z(wv_startr), Z(wv_temp), Z(wv_startr), *qqi);
            /* Note: on recover, we expect an exact match here, but on
             * normal entry we don't. */
            for (uint xmi = 0; xmi < xmc; ++xmi) {
                int cmp = mpz_cmp(xmod[xmi], Z(wv_temp));
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
                        Z(wv_ati), Z(wv_temp), xmod[xmi]
                    );
                    exit(1);
                }
                if (xmi + 1 == xmc) {
                    if (mpz_sgn(start) == 0) {
                        rindex = 0;
                        mpz_add_ui(Z(wv_startr), Z(wv_startr), 1);
                        break;
                    }
                    gmp_fprintf(stderr,
                        "from start %Zu no match found for mod %Zu > %Zu\n",
                        Z(wv_ati), Z(wv_temp), xmod[xmi]
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
        mpz_add_ui(Z(wv_endr), max, sqi);
        mpz_fdiv_q(Z(wv_endr), Z(wv_endr), *qi);
        mpz_root(Z(wv_endr), Z(wv_endr), xi);

        while (1) {
            mpz_add(Z(wv_r), Z(wv_qqr), xmod[rindex]);
            if (mpz_cmp(Z(wv_r), Z(wv_endr)) > 0)
                return;
            ++countwi;
            mpz_pow_ui(Z(wv_rx), Z(wv_r), xi);
            mpz_sub(Z(wv_ati), Z(wv_rx), *oi);
            mpz_fdiv_q(Z(wv_ati), Z(wv_ati), *qqi);
            if (utime() >= diagt)
                diag_walk_zv(Z(wv_ati), Z(wv_end));
            for (uint ii = 0; ii < inv_count; ++ii) {
                t_mod *ip = &inv[ii];
                if (mpz_fdiv_ui(Z(wv_ati), ip->m) == ip->v)
                    goto next_sqati;
            }
            /* TODO: variant is_tau for known power */
            if (!is_tau(Z(wv_rx), ti))
                goto next_sqati;
            /* TODO: bail and print somewhere here if 'opt_print' */
            /* note: we have no more squares */
            /* TODO: remove me once we handle Pell */
            for (uint i = 1; i < nqc; ++i) {
                uint vi = need_square[i];
                if (!test_zother(wv_qq[vi], wv_o[vi], Z(wv_ati), t[vi]))
                    goto next_sqati;
            }
            for (uint i = 0; i < npc; ++i) {
                uint vi = need_prime[i];
                if (!test_zprime(wv_qq[vi], wv_o[vi], Z(wv_ati)))
                    goto next_sqati;
            }
            /* TODO: test these in parallel, with optional printme cutoff */
            for (uint i = 0; i < noc; ++i) {
                uint vi = need_other[i];
                if (!test_zother(wv_qq[vi], wv_o[vi], Z(wv_ati), t[vi]))
                    goto next_sqati;
            }
            /* have candidate: calculate and apply it */
            mpz_mul(Z(wv_cand), wv_qq[0], Z(wv_ati));
            mpz_add(Z(wv_cand), Z(wv_cand), wv_o[0]);
            mpz_mul(Z(wv_cand), Z(wv_cand), *q[0]);
            candidate(Z(wv_cand));
            return;
          next_sqati:
            ++rindex;
            if (rindex >= xmc) {
                mpz_add(Z(wv_qqr), Z(wv_qqr), *qqi);
                rindex = 0;
            }
        }
    }

    if (!mpz_fits_ulong_p(Z(wv_end)))
        fail("TODO: walk_v.end > 2^64");
    ulong end = mpz_get_ui(Z(wv_end));
    for (ulong ati = mpz_get_ui(Z(wv_ati)); ati <= end; ++ati) {
        ++countwi;
        if (utime() >= diagt)
            diag_walk_v(ati, end);
        for (uint ii = 0; ii < inv_count; ++ii) {
            t_mod *ip = &inv[ii];
            if (ati % ip->m == ip->v)
                goto next_ati;
        }
        /* TODO: bail and print somewhere here if 'opt_print' */
        /* note: we have no squares */
        for (uint i = 0; i < npc; ++i) {
            uint vi = need_prime[i];
            if (!test_prime(wv_qq[vi], wv_o[vi], ati))
                goto next_ati;
        }
        /* TODO: test these in parallel, with optional printme cutoff */
        for (uint i = 0; i < noc; ++i) {
            uint vi = need_other[i];
            if (!test_other(wv_qq[vi], wv_o[vi], ati, t[vi]))
                goto next_ati;
        }
        /* have candidate: calculate and apply it */
        mpz_mul_ui(Z(wv_cand), wv_qq[0], ati);
        mpz_add(Z(wv_cand), Z(wv_cand), wv_o[0]);
        mpz_mul(Z(wv_cand), Z(wv_cand), *q[0]);
        candidate(Z(wv_cand));
        return;
      next_ati:
        ;
    }
}

void walk_1(uint vi) {
    t_value *vip = &value[vi];
    t_allocation *aip = &vip->alloc[vip->vlevel - 1];
    mpz_sub_ui(Z(w1_v), aip->q, vi);

    if (mpz_cmp(Z(w1_v), min) < 0)
        return;
    for (uint vj = 0; vj < k; ++vj) {
        if (vi == vj)
            continue;
        t_value *vjp = &value[vj];
        t_allocation *ajp = (vjp->vlevel) ? &vjp->alloc[vjp->vlevel - 1] : NULL;
        mpz_add_ui(Z(w1_j), Z(w1_v), vj);
        if (ajp) {
            mpz_fdiv_qr(Z(w1_j), Z(w1_r), Z(w1_j), ajp->q);
            if (mpz_sgn(Z(w1_r)) != 0)
                return;
            mpz_gcd(Z(w1_r), Z(w1_j), ajp->q);
            if (mpz_cmp(Z(w1_r), Z(zone)) != 0)
                return;
        }
        /* TODO: stash these in an array, test them in order */
        if (!is_tau(Z(w1_j), ajp ? ajp->t : n))
            return;
    }
    candidate(Z(w1_v));
    return;
}

/* return TRUE if a is a quadratic residue mod m
 * TODO: since we don't need the root, can we speed this up?
 */
bool has_sqrtmod(mpz_t a, mpz_t m) {
    return sqrtmod_t(Z(sqm_x), a, m, Z(sqm_t), Z(sqm_q), Z(sqm_b), Z(sqm_z));
}

/* Return TRUE if allocating p^{x-1} at v_i is consistent with the known
 * square v_j = mz^2.
 * TODO: we probably always have mpz_fits_ulong_p(m)
 * TODO: for p > 2 see modinvert() in MPU-util.c
 * TODO: p == 2 seems like it should be easy, but existing algorithm
 * doesn't special-case it.
 */
bool check_residue(uint vi, ulong p, uint x, uint vj, mpz_t m, bool is_forced) {
    int d = vj - vi;
    if (d == 0)
        return 1;
    uint e1 = x - 1;
    uint e2 = 0;
    bool need_divide = 0;

    if (is_forced) {
        while ((d % p) == 0) {
            ++e2;
            d /= p;
        }

        t_value *vpj = &value[vj];
        for (uint i = 0; i < vpj->vlevel; ++i)
            if (vpj->alloc[i].p == p) {
                if (e2 == 0)
                    return 0;
                if (e1 == e2)
                    return 1;   /* see below */
                if (mpz_divisible_ui_p(m, p)) {
                    need_divide = 1;
                    --e1;
                    --e2;
                }
                break;
            }

        if (e1 == e2) {
            /* we know only that valuation(v_j, p) > e1, punt on this */
            return 1;
        }
    }

    if (need_divide)
        mpz_divexact_ui(Z(res_m), m, p);
    else
        mpz_set(Z(res_m), m);

    /* we have v_j = p^{min(e1, e2)} . m . z^2 */
    if (p == 2)
        mpz_mul_2exp(Z(res_px), Z(zone), (e1 < e2) ? e2 - e1 : e1 - e2);
    else
        mpz_set_ui(Z(res_px), p);

    /* return true iff d / m (mod px) is a quadratic residue (mod px) */
    if (!mpz_invert(Z(res_m), Z(res_m), Z(res_px)))
        fail("logic error, p ~| m, so m should be invertible");
    if (d != 1) {
        mpz_mul_si(Z(res_m), Z(res_m), d);
        mpz_mod(Z(res_m), Z(res_m), Z(res_px));
    }
    return has_sqrtmod(Z(res_m), Z(res_px));
}

void update_chinese(t_level *old, t_level *new, uint vi, mpz_t px) {
    mpz_t zarray[4];
    mpz_set_si(Z(uc_minusvi), -(long)vi);

    memcpy(&zarray[0], old->rq, sizeof(mpz_t));
    memcpy(&zarray[1], Z(uc_minusvi), sizeof(mpz_t));
    memcpy(&zarray[2], old->aq, sizeof(mpz_t));
    memcpy(&zarray[3], px, sizeof(mpz_t));
    if (chinese(new->rq, new->aq, &zarray[0], &zarray[2], 2))
        return;
    fail("chinese failed");
}

/* Record a new square at v_i; return FALSE if any v_j factor is not a
 * residue.
 */
bool alloc_square(t_level *cur, uint vi) {
    t_value *v = &value[vi];
    uint sqi = cur->have_square++;
    t_square *sqp = (sqi < MAX_SQUARE) ? &squares[sqi] : sqspare;
    sqp->vi = vi;
    mpz_set_ui(sqp->m, 1);
    for (uint ai = 0; ai < v->vlevel; ++ai) {
        t_allocation *ap = &v->alloc[ai];
        if (ap->x & 1)
            continue;
        mpz_mul_ui(sqp->m, sqp->m, ap->p);
    }
    /* note: we rely on cur <= levels[level + 1] */
    for (uint j = 1; j < level; ++j) {
        t_level *lp = &levels[j];
        if (lp == cur)
            break;
        /* note: for a forced batch, we only need to check an example of
         * the highest power involved, which is the levels[] entry itself */
        if (!check_residue(lp->vi, lp->p, lp->x, vi, sqp->m, lp->is_forced))
            return 0;
    }
    return 1;
}

/* returns TRUE if this newly creates a square */
bool apply_allocv(t_level *cur_level, uint vi, ulong p, uint x, mpz_t px) {
    t_value *v = &value[vi];
    t_allocation *prev = (v->vlevel) ? &v->alloc[v->vlevel - 1] : NULL;
    t_allocation *cur = &v->alloc[v->vlevel];
    ++v->vlevel;
    uint prevt = prev ? prev->t : n;
    if (prevt % x)
        return 0;

    cur->p = p;
    cur->x = x;
    cur->t = prevt / x;
    if (prev)
        mpz_mul(cur->q, prev->q, px);
    else
        mpz_set(cur->q, px);
    if (cur->t == 1) {
        walk_1(vi);
        return 0;
    }

    if (cur_level->have_square) {
        /* TODO: either support Pell solver, or loop over squares here */
        t_square *sqp = &squares[0];
        if (!check_residue(vi, p, x, sqp->vi, sqp->m, cur_level->is_forced))
            return 0;
    }

    if ((cur->t & 1) && !(prevt & 1))
        if (!alloc_square(cur_level, vi))
            return 0;
    return 1;
}

/* Allocate p^{x-1} to v_{vi}. Returns FALSE if it is invalid. */
bool apply_alloc(t_level *prev, t_level *cur, uint vi, ulong p, uint x) {
    cur->vi = vi;
    cur->p = p;
    cur->x = x;
    cur->have_square = prev->have_square;
    cur->nextpi = prev->nextpi;
    if (p == sprimes[cur->nextpi])
        cur->nextpi = find_nextpi(cur);
    mpz_set_ui(px, p);
    mpz_pow_ui(px, px, x - 1);
    update_chinese(prev, cur, vi, px);
    return apply_allocv(cur, vi, p, x, px);
}

bool apply_secondary(t_level *cur, uint vi, ulong p, uint x) {
    mpz_set_ui(px, p);
    mpz_pow_ui(px, px, x - 1);
    return apply_allocv(cur, vi, p, x, px);
}

/* find the best entry to progress: the one with the highest tau()
 * still to fulfil, or (on equality) with the highest q, but having
 * at least one factor to allocate.
 * If there is no best entry, returns k.
 */
uint best_v(void) {
    uint vi, ti = 0;
    mpz_t *qi;
    for (uint vj = 0; vj < k; ++vj) {
        t_value *vpj = &value[vj];
        t_allocation *apj = (vpj->vlevel) ? &vpj->alloc[vpj->vlevel - 1] : NULL;
        uint tj = apj ? apj->t : n;
        mpz_t *qj = apj ? &apj->q : ZP(zone);

        /* skip if no odd prime factor */
        if (divisors[tj].high <= 2)
            continue;
        /* skip prime powers when capped */
        if (maxp && (tj & 1) && divisors[tj].alldiv == 2)
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

void insert_stack(void) {
    /* first insert forced primes */
    for (uint fpi = 0; fpi < forcedp; ++fpi) {
        STOREVL(vl_forced++);
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
        if (maxx == 0)
            fail("no forced prime %u found", p);
        /* CHECKME: this returns 0 if t=1 */
        t_level *prev = &levels[level - 1];
        t_level *cur = &levels[level];
        if (!apply_alloc(prev, cur, mini, p, maxx))
            fail("could not apply_alloc(%u, %lu, %u)", mini, p, maxx);
        for (uint vi = 0; vi < k; ++vi) {
            t_fact *rs = &rstack[vi];
            if (rs->count && rs->ppow[rs->count - 1].p == p) {
                --rs->count;
                if (vi == mini)
                    continue;
                uint x = rs->ppow[rs->count].e + 1;
                if (!apply_secondary(cur, vi, p, x))
                    fail("could not apply_secondary(%u, %lu, %u)", vi, p, x);
            }
        }
        ++level;

        uint bi;
        for (bi = 0; bi < fp->count; ++bi) {
            t_forcebatch *b = &fp->batch[bi];
            if (b->x == maxx && b->vi == mini)
                break;
        }
        if (bi >= fp->count)
            fail("no batch found for %u^{%u-1} at v_%u", p, maxx, mini);
        cur->is_forced = 1;
        cur->bi = bi;
    }
    /* now insert the rest */
    while (1) {
        uint vi = best_v();
        if (vi == k)
            break;
        t_fact *rs = &rstack[vi];
        if (rs->count == 0)
            break;
        --rs->count;
        uint p = rs->ppow[rs->count].p;
        uint x = rs->ppow[rs->count].e + 1;
        /* CHECKME: this returns 0 if t=1 */
        t_level *prev = &levels[level - 1];
        t_level *cur = &levels[level];
        if (!apply_alloc(prev, cur, vi, p, x))
            fail("could not apply_alloc(%u, %lu, %u)", vi, p, x);
        ++level;
        cur->is_forced = 0;
        /* FIXME: set secondary values for unforced */
    }
    /* check we found them all */
    for (uint vi = 0; vi < k; ++vi) {
        t_fact *rs = &rstack[vi];
        if (rs->count) {
            t_ppow pp = rs->ppow[rs->count - 1];
            fail("failed to inject %lu^%u at v_%u", pp.p, pp.e, vi);
        }
    }
}

/* Calculate the minimum contribution from primes satisfying the given tau.
 */
void mintau(mpz_t mint, uint vi, uint t) {
    /* quick version: given the minimum prime p that can be used, we
     * calculate p^k where k = sum{p_i - 1} over the primes dividing
     * t _with multiplicity_.
     */
    uint minnext = sprimes[levels[level - 1].nextpi];
    mpz_set_ui(mint, minnext);
    mpz_pow_ui(mint, mint, divisors[t].sumpm);
}

/* return the maximum prime to iterate to */
ulong limit_p(uint vi, uint x, uint nextt) {
    t_value *vp = &value[vi];
    t_allocation *ap = (vp->vlevel) ? &vp->alloc[vp->vlevel - 1] : NULL;
    mpz_add_ui(Z(lp_x), max, vi);
    if (ap)
        mpz_div(Z(lp_x), Z(lp_x), ap->q);
    /* else notional ap->q is 1 */

    /* divide through by the minimum contribution that could supply the
     * remaining tau */
    if (nextt > 1) {
        mintau(Z(lp_mint), vi, nextt);
        mpz_div(Z(lp_x), Z(lp_x), Z(lp_mint));
    }

    mpz_root(Z(lp_x), Z(lp_x), x - 1);
    if (mpz_fits_ulong_p(Z(lp_x))) {
        ulong lim = mpz_get_ui(Z(lp_x));
        if (maxp && maxp < lim)
            return maxp;
        return lim;
    }
    diag_plain();
    keep_diag();
    report("002 %s: outsize limit %Zu\n", diag_buf, Z(lp_x));
    return 0;
}

bool apply_batch(t_level *prev, t_level *cur, t_forcep *fp, uint bi) {
    assert(fp->count > bi);
    t_value *vp;
    cur->is_forced = 1;
    cur->bi = bi;

    t_forcebatch *bp = &fp->batch[bi];
    if (!apply_alloc(prev, cur, bp->vi, fp->p, bp->x))
        return 0;
    /* check if we overshot */
    vp = &value[bp->vi];
    if (mpz_cmp(vp->alloc[vp->vlevel - 1].q, max) > 0)
        return 0;

    /* TODO: prep this */
    for (uint i = fp->p; i <= bp->vi; i += fp->p) {
        uint x = simple_valuation(i, fp->p) + 1;
        if (!apply_secondary(cur, bp->vi - i, fp->p, x))
            return 0;
        vp = &value[bp->vi - i];
        if (mpz_cmp(vp->alloc[vp->vlevel - 1].q, max) > 0)
            return 0;
    }
    for (uint i = fp->p; bp->vi + i < k; i += fp->p) {
        uint x = simple_valuation(i, fp->p) + 1;
        if (!apply_secondary(cur, bp->vi + i, fp->p, x))
            return 0;
        vp = &value[bp->vi + i];
        if (mpz_cmp(vp->alloc[vp->vlevel - 1].q, max) > 0)
            return 0;
    }
    return 1;
}

/*
 * return 0 if nothing more to do at this level for any x;
 * return 1 if nothing more to do for this x;
 * return 2 if prepped for this x with work to do.
 */
uint prep_unforced_x(t_level *prev, t_level *cur, ulong p) {
    uint ti = cur->ti;

/* TODO: for n=54, we should disallow eg x=9 when t=54, since we
 * will already have tried all x=3 and x=6 before that.
 */

    uint x = divisors[ti].div[cur->di];
    uint vi = cur->vi;
    t_value *vp = &value[vi];
    t_allocation *ap = (vp->vlevel) ? &vp->alloc[vp->vlevel - 1] : NULL;

    /* pick up any previous unforced x */
    uint unforced_base = (vl_forced) ? VLP(vl_forced - 1)[vi] : 0;
    uint prevx = (vp->vlevel > unforced_base) ? ap->x : 0;
    if (p == 0 && x <= prevx && (ti % prevx) == 0) {
        if (x < prevx)
            return 1;   /* skip this x, we already did the reverse */
        p = ap->p;      /* skip smaller p, we already did the reverse */
    } else if (p == 0)
        p = maxforce[vi];
    /* else we're continuing from known p */

    uint nextt = ti / x;
    /* try p^{x-1} for all p until q_i . p^{x-1} . minrest > max + i */
    ulong limp = limit_p(vi, x, nextt);
    if (limp < p + 1)
        return 1;   /* nothing to do here */
    mpz_add_ui(Z(r_walk), max, vi);
    mpz_fdiv_q(Z(r_walk), Z(r_walk), prev->aq);
    if (prev->have_square) {
        /* If we fix a square, expect to actually walk sqrt(r_walk)
         * times number of roots mod cur->aq, typically 2^k if there are
         * k primes dividing aq.
         */
        mpz_root(Z(r_walk), Z(r_walk), 2);
        mpz_mul_2exp(Z(r_walk), Z(r_walk), level - 1);
#   if 0
        /* TODO: support Pell */
        if (prev->have_square > 1)
            mpz_set_ui(Z(r_walk), 0);
#   endif
    }
    if (gain > 1)
        mpz_mul_ui(Z(r_walk), Z(r_walk), gain);
    if (antigain > 1)
        mpz_fdiv_q_ui(Z(r_walk), Z(r_walk), antigain);
    if (mpz_fits_ulong_p(Z(r_walk))
        && mpz_get_ui(Z(r_walk)) < limp - p
    ) {
        walk_v(prev, Z(zero));
        return 0;
    }
    cur->p = p;
    cur->x = x;
    cur->limp = limp;
    cur->max_at = seen_best;
    /* TODO: do some constant alloc stuff in advance */
    /* TODO: special case for nextt == 1 */
    return 2;
}

/* we emulate recursive calls via the levels[] array */
void recurse(void) {
    ulong p;
    uint x;
    t_level *prev_level, *cur_level;

    if (have_rwalk) {
        prev_level = &levels[level - 1];
        walk_v(prev_level, rwalk_from);
        goto derecurse;
    }

    while (1) {
        ++countr;
        prev_level = &levels[level - 1];
        cur_level = &levels[level];

        /* recurse deeper */
        {
            uint fi = level - 1;
            if (fi < forcedp && (fi == 0 || prev_level->is_forced)) {
                t_forcep *fp = &forcep[fi];
                if (fp->count == 0)
                    goto unforced;
                STOREVL(vl_forced++);
                if (!apply_batch(prev_level, cur_level, fp, 0)) {
                    FETCHVL(vl_forced - 1);
                    goto continue_recurse;
                }
                ++level;
                if (utime() >= diagt)
                    diag_plain();
                continue;   /* deeper */
            }
        }
      unforced:
        {
            uint vi = best_v();
            /* TODO: walk_v() directly at previous level, if best_v() would
             * give same result each time.
             */
            if (vi == k) {
                walk_v(prev_level, Z(zero));
                goto derecurse;
            }
            t_value *vp = &value[vi];
            uint ti = (vp->vlevel) ? vp->alloc[vp->vlevel - 1].t : n;
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
            switch (prep_unforced_x(prev_level, cur_level, 0)) {
                case 0:
                    /* nothing to do for any x */
                    goto derecurse;
                case 1:
                    /* nothing to do for this x */
                    goto continue_unforced_x;
                case 2:
                    /* ok, continue for this x */
                    ;
            }
            goto continue_unforced;
        }
        break;
      /* entry point, must set prev_level/cur_level before using */
      derecurse:
        --level;
        if (level == 0)
            break;
        prev_level = &levels[level - 1];
        cur_level = &levels[level];
        if (cur_level->is_forced) {
            /* unapply the batch */
            FETCHVL(vl_forced - 1);
        } else
            --value[cur_level->vi].vlevel;
        /* goto continue_recurse; */
      continue_recurse:
        if (cur_level->is_forced) {
            uint fi = level - 1;
            t_forcep *fp = &forcep[fi];

            uint bi = cur_level->bi + 1;
            if (bi >= fp->count) {
                --vl_forced;
                goto derecurse;
            }
            if (fp->batch[bi].x == 0) {
                cur_level->is_forced = 0;
                FETCHVL(--vl_forced);
                goto unforced;
            }
            if (!apply_batch(prev_level, cur_level, fp, bi)) {
                /* unapply a possible partial batch */
                FETCHVL(vl_forced - 1);
                goto continue_recurse;
            }
            ++level;
            if (utime() >= diagt)
                diag_plain();
            continue;
        }
      continue_unforced:
        {
            ulong p = cur_level->p;
            /* recalculate limit if we have an improved maximum */
            if (seen_best > cur_level->max_at)
                if (!prep_unforced_x(prev_level, cur_level, p))
                    goto continue_unforced_x;
            /* note: only valid to use from just below here */
          redo_unforced:
            p = next_prime(p);
            if (p > cur_level->limp)
                goto continue_unforced_x;
            /* TODO: save max_used_p, use it to short-circuit */
            for (uint li = 1; li < level; ++li)
                if (p == levels[li].p)
                    goto redo_unforced;
            /* note: this returns 0 if t=1 */
            if (!apply_alloc(prev_level, cur_level, cur_level->vi, p, cur_level->x)) {
                if (utime() >= diagt)
                    diag_plain();
                --value[cur_level->vi].vlevel;
                /* not redo_unforced, we may have improved max */
                goto continue_unforced;
            }
            ++level;
            if (utime() >= diagt)
                diag_plain();
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
        if (strncmp("--", arg, 2) == 0)
            break;
        if (arg[1] == 'x')
            set_minmax(&arg[2]);
        else if (arg[1] == 'g')
            set_gain(&arg[2]);
        else if (arg[1] == 'p')
            set_cap(&arg[2]);
        else if (arg[1] == 'r')
            runid = strtoul(&arg[2], NULL, 10);
        else if (arg[1] == 'f')
            force_all = strtoul(&arg[2], NULL, 10);
        else if (strncmp("-o", arg, 2) == 0)
            opt_print = 1;
        else if (strncmp("-d", arg, 2) == 0)
            debug = 1;
        else
            fail("unknown option '%s'", arg);
    }
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
    if (rstack)
        insert_stack();
    recurse();
    keep_diag();

    clock_t tz = utime();
    report("367 coul(%u, %u): recurse %lu, walk %lu, walkc %lu (%.2fs)\n",
            n, k, countr, countw, countwi, seconds(tz));
    if (seen_best)
        report("200 f(%u, %u) = %Zu (%.2fs)\n", n, k, max, seconds(tz));
    done();
    return 0;
}