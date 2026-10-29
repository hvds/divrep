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
#include <setjmp.h>
#include <sys/time.h>
#include <sys/resource.h>
#ifdef __linux__
#   include <sys/ioctl.h>
#   include <sys/syscall.h>
#   include <linux/perf_event.h>
#endif

#include "coul.h"
#include "builtins.h"
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
#define MAXK 66     /* nextprime(8 * sizeof(ulong)) - 1 */
#define MAXK_KERN 64    /* under -k: positions are bits of a ulong */
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
    rec_cand, rec_lead, rec_trail,  /* recover */
    p3_base,                    /* parse_305 */

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
ulong g_ati;

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
 *
 * The primary has exactly p^e, so v_primary / p^e is one of the p - 1
 * units mod p; each other v_j with the same power excludes one more.
 * When only one remains, "fold" is that unit, and the allocation can
 * fix v_0 mod p^{e+1} rather than mod p^e; else it is 0. For p = 2 it
 * is always 1.
 */
typedef struct s_forcebatch {
    uint primary;   /* x[primary] is first max */
    uint fold;      /* v_primary / p^e == fold (mod p), if non-zero */
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
bool restrict_forced = 0;

/* When allocation forces the residue of some v_i to be square, we want
 * to calculate the roots mod every allocation (before and after this one),
 * first to check if a solution is possible, and second to avoid duplicate
 * work when we actually use the roots in walk_v().
 * The set of roots lives in resarray(level), but here we track what power
 * root they are: the allocation at value[sq0].alloc[i] leaves gcddm sqg[i].
 */
uint sq0 = 0;
uint *sqg = NULL;   /* size maxfact */

uint maxlevel;              /* avvailable entries in nodes[], acts[] */
t_node *nodes = NULL;       /* one per level: the state reached */
t_act *acts = NULL;         /* one per level: the loop reaching it */
uint level = 0;             /* current recursion level */
uint final_level = 0;       /* level at which to terminate */
t_value *value = NULL;      /* v_0 .. v_{k-1} */
uint *cur_vlevel = NULL;    /* Number of allocations (+1) at each value */

static inline void level_setp(t_act *cur_act, ulong p) {
    cur_act->p = p;
    prime_iterator_setprime(&cur_act->piter, p);
}

/* list of some small primes, at least enough for one per allocation,
 * and a reverse lookup */
#define MAX_NSPRIMES 32767      /* indexed and counted by short */
uint nsprimes;
uint *sprimes = NULL;
uint *ptoi = NULL;
uint lastprime;

/* set to utime at start of run, minus last timestamp of recovery file */
double t0 = 0;
struct rusage rusage_buf;

/* Reported times are user-mode CPU cycles divided by a reference clock
 * rate (-Lc<GHz>) when the cycle counter is available (Linux only, see
 * init_cycles()), else CPU seconds.
 * -Ld uses these scaled times; -Ls and -Lf use raw CPU seconds.
 */
double cyc_ghz = 3.6;
int cyc_fd = -1;
int cyc_errno = 0;      /* wanted cycles, but could not open the counter */
static inline double utime(void) {
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
bool any_bound = 0;     /* apply_single() accepts rq > zmax */
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
bool midp_only = 0, need_midp = 0;
/* -k: where a batch fixes one square, each position with tau == 2 (mod 4)
 * left takes one more prime to an odd power, and that power leaves a
 * second square. walk_midp() tries every such power with p <= kern_b,
 * each a Pell equation; elsewhere those primes are known to exceed kern_b.
 */
ulong kern_b = 0;
bool kern_passed(uint vi);
/* where to walk for -W (midp) */
typedef struct s_midpp {
    uint vi;
    uint x;
    ulong maxp;
    ulong minp;
} t_midpp;
uint midppc;
t_midpp *midpp = NULL;

/* The act a recovery line shows in progress by its suffix, if any: set
 * up by its action's parse via parse_305(), and cleared (to A_NONE)
 * once resumed. Which fields are used depends on the action.
 */
struct {
    e_action action;
    uint vi;
    ulong p;            /* W: p in progress; F: have checked p^r up to p */
    uint x;             /* W: x in progress */
    uint a;             /* 6X: bit-vector over allocated prime powers */
    ulong p_outer;      /* F: have checked all p^{2r} up to p_outer */
    ulong p_inner;      /* F: have checked all p^{2r}.q^r up to p_inner */
} act_recover;

uint rough = 0;     /* test roughness if tau >= rough */
bool opt_print = 0; /* print candidates instead of fully testing them */
uint opt_flake = 0; /* test less before printing candidates */
/* If opt_alloc is non-zero and opt_batch < 0, just show the forced-prime
 * allocation; if opt_alloc is non-zero and opt_batch >= 0, just process
 * the specified batch_alloc.
 */
uint opt_alloc = 0;
slong opt_batch_min = -1, opt_batch_max;
slong batch_alloc = 0;    /* index of forced-prime allocations */
/* longjmp() here to end the search early, going on to the final reports:
 * the implication is that we have searched everything we were asked to.
 */
jmp_buf jmp_finish;
slong last_batch_seen = -1;
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

/* Sentinel values returned by best_v() and strategies[] functions.
 * Any real v_i is < BV_SPECIAL; BV_WALK means there is no v_i to allocate
 * to; BV_NEXTX means there is no work left to do for this x.
 */
#define BV_SPECIAL k
#define BV_WALK (BV_SPECIAL + 0)
#define BV_NEXTX (BV_SPECIAL + 1)
#define BV_6X (BV_SPECIAL + 2)

/* What prep_unforced_x() and limit_unforced_x() find for allocating
 * p^{x-1} at the current level's v_i.
 */
typedef enum {
    PUX_NOTHING_TO_DO = 0,  /* nothing more to do at this level for any x */
    PUX_FLIP_PQSQ,          /* the flip is available now: run_flip_pqsq() */
    PUX_SKIP_THIS_X,        /* nothing more to do for this x */
    PUX_DO_THIS_X           /* there are p to allocate for this x */
} e_pux;

/* What choose_action() decides the act at a new level is to do. */
typedef enum {
    CH_NOTHING = 0, /* nothing to do below this point */
    CH_FORCED,      /* the batches of the next forced prime */
    CH_UNFORCED,    /* a loop of p^x at the act's v_i */
    CH_WALK,        /* walk_v() covers everything below */
    CH_6X           /* walk_6x() covers everything below */
} e_choice;

/* e_is indicates where we should pick up when we enter recurse() */
typedef enum {
    IS_DEEPER = 0,  /* Current level is good, try to recurse deeper */
    IS_FINISH,  /* Everything is done */
    IS_NEXTX,   /* Current power is done, try the next power */
    IS_NEXT,    /* Current prime is done, try the next prime */
    IS_RWALK,   /* Finish a partial (non-midp) walk before continuing */
    IS_BATCH,   /* Start in process_batch() */
    IS_MIDP,    /* Resume walk_midp(), possibly with partial progress */
    IS_6X,      /* Resume best_6x(), possibly with partial progress */
    IS_FLIP     /* Resume run_flip_pqsq(), possibly with partial progress */
} e_is;

typedef uint (*t_strategy)(t_act *cur_act);
uint best_v0(t_act *cur_act);
uint best_v1(t_act *cur_act);
uint best_v2(t_act *cur_act);
uint best_v3(t_act *cur_act);
uint best_v4(t_act *cur_act);
/* best_6x() special-case strategy (TYPE_o only) */
uint best_6x(t_act *cur_act);
/* best_fixed() special-case strategy (-js) */
uint best_fixed(t_act *cur_act);
#define STRATEGY_6X 5
#define STRATEGY_FIXED 6
#define NUM_STRATEGIES 7
t_strategy strategies[NUM_STRATEGIES] = {
    &best_v0, &best_v1, &best_v2, &best_v3, &best_v4,
    &best_6x, &best_fixed
};

/* What each action does, where it differs from others. An action that
 * iterates has a next_op, which makes the act's next child node (returning
 * FALSE when there is none left), and an undo_op, which unapplies the last
 * one as unwinding passes it; recurse() drives them. An action with a
 * suffix_op is shown in progress lines by the suffix it writes (returning
 * its length) in place of the allocation at its level. For recovery its
 * parse_op reads the suffix into act_recover, given the text after the
 * tag that starts it, and returns the text after the suffix.
 */
typedef bool (*t_next_op)(t_act *cur_act);
bool next_forced(t_act *cur_act);
bool next_unforced(t_act *cur_act);
typedef void (*t_undo_op)(t_act *cur_act);
void undo_forced(t_act *cur_act);
void undo_unforced(t_act *cur_act);
void undo_flip(t_act *cur_act);
typedef uint (*t_suffix_op)(t_act *cur_act, char *buf);
uint suffix_midp(t_act *cur_act, char *buf);
uint suffix_6x(t_act *cur_act, char *buf);
uint suffix_flip(t_act *cur_act, char *buf);
typedef char *(*t_parse_op)(char *s);
char *parse_midp(char *s);
char *parse_6x(char *s);
char *parse_flip(char *s);
typedef struct s_action_ops {
    t_next_op next;
    t_undo_op undo;
    t_suffix_op suffix;
    char *tag;
    t_parse_op parse;
} t_action_ops;
const t_action_ops action_ops[A_NONE] = {
    [A_UNFORCED] = { .next = &next_unforced, .undo = &undo_unforced },
    [A_FORCED] = { .next = &next_forced, .undo = &undo_forced },
    [A_MIDP] = { .suffix = &suffix_midp, .tag = " W(", .parse = &parse_midp },
    [A_6X] = { .suffix = &suffix_6x, .tag = " 6X(", .parse = &parse_6x },
    [A_FLIP] = {
        .undo = &undo_flip,
        .suffix = &suffix_flip, .tag = " F(", .parse = &parse_flip
    },
};
static inline bool has_suffix(e_action a) {
    return action_ops[a].suffix != NULL;
}

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
bool debugc = 0;    /* show modular constraints */
bool debugC = 0;    /* show more modular constraints */
bool debugm = 0;    /* track and show mintau results */
bool debugL = 0;    /* force every diag to also write a 305/315 log line */
uint debugL_count = 0;  /* debugL only for the first n iterations */
bool log_full = 0;  /* show prefinal result for harness */

ulong randseed = 1; /* for ECM, etc */
bool vt100 = 0;     /* update window title with VT100 escape sequences */

/* From an expanded (315) line, forced[li] is 1 + the position of the
 * allocation made at level li, or 0 if none is shown (as for a forced
 * prime's p^0 tail); force is 1 + the highest level shown.
 */
typedef struct s_recover {
    uint force;
    uint *forced;
    t_fact *f;
} t_recover;

char *rpath = NULL; /* path to log file */
FILE *rfp = NULL;   /* file handle to log file */
bool start_seen = 0;    /* true if log file has been written to before */
bool skip_recover = 0;  /* true if we should not attempt recovery */
bool ignore_exceptions = 0; /* true if we should not check exceptions[] */
t_recover *rstack = NULL;  /* point reached in recovery log file */
t_recover *istack = NULL;  /* point requested by -I */
bool have_pend202 = 0;  /* true when Z(rec_trail) is trailing candidate */
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
    /* the rest need MAX_NSPRIMES < 32768 */
    ushort *pfreei;     /* list of free prime indices */
    ushort pfreenext;   /* where to start looking for next free prime */
    ushort pfreedepth;  /* number of free primes found */
} t_mint_state;
size_t pfree_vecsize;
uint mint_maxdepth;     /* size of pfreei[], mint_best[] and mint_px[] */
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
#define MAX_EXPANDED 5
#define DIAG_BUFSIZE (6 + MAX_DEC_ULONG + k * maxfact * (MAX_DEC_ULONG + 1 + MAX_DEC_POWER + 1 + MAX_EXPANDED) + 1)
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
 * stored in nodes[0].rq/aq.
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
/* tests the primes queued from 'first' on, taking them off the queue */
static inline uint test_prime_run(uint first) {
    uint remain = tau_prime_run(first, tm_count);
    tm_count = first;
    return remain;
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

/* True if p is never allocated as an unforced prime, wherever it lies:
 * under TYPE_a each p | n divides every v_i or none, as the batch has it.
 * Needs checking only for p <= level.maxp, which starts high enough.
 */
static inline bool never_unforced(ulong p) {
#if defined(TYPE_a)
    return (n % p) == 0;
#else
    return 0;
#endif
}

/* Returns true if p is "known" at the given level, so should not be
 * permitted as an additional unforced allocation.
 */
static inline bool known_prime(t_node *np, ulong p) {
    /* all known primes are <= maxp */
    if (p > np->maxp)
        return 0;
    if (never_unforced(p))
        return 1;
    /* a flip withdraws its allocation */
    for (uint li = 1; li <= np->level; ++li)
        if (p == acts[li].p && acts[li].x > 1
                && acts[li].action != A_FLIP)
            return 1;
    return 0;
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

void update_window(t_node *cur_node) {
    if (vt100) {
        /* update window title and icon with <ESC> ] 0 ; "string" <BEL> */
        slong this_batch = (opt_batch_min < 0) ? batch_alloc : batch_alloc - 1;
        printf("\x1b]0;b%ld:", this_batch);
        uint pc = 0;
        for (uint i = final_level + 1; i <= cur_node->level && pc < 3; ++i) {
            if (acts[i].action != A_UNFORCED
                    && !has_suffix(acts[i].action))
                continue;
            printf(" %lu", acts[i].p);
            ++pc;
        }
        printf("\a");
    }
    fflush(stdout);
}

/* Show the allocations into diag_buf. If expanded, mark each allocation
 * with its level when not at the position best_v() would have chosen,
 * so recovery can reproduce the order. Returns TRUE if any is marked.
 * An act with a suffix at or below cur_node's level is shown by that
 * suffix, and recovered from it, in place of the allocation at its own
 * level; from its level up, no allocation is marked.
 */
bool prep_show_v(t_node *cur_node, bool expanded) {
    bool marked = 0;
    uint offset = 0;
    t_act *sfx = NULL;
    for (uint li = final_level + 1; li <= cur_node->level; ++li)
        if (has_suffix(acts[li].action)) {
            sfx = &acts[li];
            break;
        }
    uint top = sfx ? sfx->level - 1 : level;
    offset += (batch_alloc)
        ? sprintf(&diag_buf[offset], "b%ld: ", batch_alloc - 1)
        : sprintf(&diag_buf[offset], "b*: ");
    for (uint vi = 0; vi < k; ++vi) {
        t_value *vp = &value[vi];
        uint vlevel = cur_vlevel[vi];
        if (sfx && vlevel > 1 && vp->alloc[vlevel - 1].level == sfx->level)
            --vlevel;
        if (vi)
            diag_buf[offset++] = ' ';
        if (vlevel == 1)
            diag_buf[offset++] = '.';
        else {
            for (uint ai = 1; ai < vlevel; ++ai) {
                t_allocation *ap = &vp->alloc[ai];
                if (ai > 1)
                    diag_buf[offset++] = '.';
                offset += sprintf(&diag_buf[offset], "%lu", ap->p);
                if (ap->x > 2)
                    offset += sprintf(&diag_buf[offset], "^%u", ap->x - 1);
                if (expanded && ap->level <= top
                        && acts[ap->level].unsorted) {
                    offset += sprintf(&diag_buf[offset], "(%u)", ap->level);
                    marked = 1;
                }
            }
        }
    }
    if (sfx)
        offset += action_ops[sfx->action].suffix(sfx, &diag_buf[offset]);
    diag_buf[offset] = 0;
    return marked;
}

void diag_csv_head(void) {
    printf("Batch id");
    for (uint i = 0; i < k; ++i)
        printf(",v_%u", i);
    t_divisors *dp = &divisors[target_lcm];
    printf(",LCM");
    for (uint i = 0; i < dp->alldiv; ++i)
        printf(",t %u", dp->div[i]);
    printf("\n");
}

void diag_csv(t_node *cur_node) {
    t_divisors *dp = &divisors[target_lcm];
    uint tc[dp->alldiv];
    memset(&tc[0], 0, dp->alldiv * sizeof(uint));
    mpz_set_ui(Z(temp), 1);
    printf("%ld", batch_alloc);
    for (uint vi = 0; vi < k; ++vi) {
        t_value *vp = &value[vi];
        uint vlevel = cur_vlevel[vi];
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

    t_node *np = &nodes[cur_batch_level];
    /* Show the batch alone, without what is allocated above it. Before
     * the first batch (b*) there is none, so show what there is.
     */
    uint save[k];
    memcpy(save, cur_vlevel, k * sizeof(uint));
    if (batch_alloc)
        for (uint vi = 0; vi < k; ++vi) {
            t_allocation *alloc = value[vi].alloc;
            uint d = 1;
            while (d < save[vi] && alloc[d].level <= cur_batch_level)
                ++d;
            cur_vlevel[vi] = d;
        }
    if (opt_alloc & 2) {
        diag_csv(np);
    } else {
        prep_show_v(np, 0);        /* into diag_buf */
        if (np->have_square) {
            uint l = strlen(diag_buf);
            sprintf(&diag_buf[l], " [sq=%u]", np->have_square);
        }
        if (opt_alloc)
            /* with the batch's modulus, as a guide to its size */
            report("203 %s [aq=%Zu] (%.2fs)\n",
                    diag_buf, np->aq, seconds(utime()));
        else
            report("203 %s (%.2fs)\n", diag_buf, seconds(utime()));
    }
    memcpy(cur_vlevel, save, k * sizeof(uint));
}

void diag_any(t_node *cur_node, bool need_disp) {
    double t1 = utime();
    update_window(cur_node);

    if ((debugb && !debugB)
        && batch_alloc != last_batch_seen
        && ((need_diag && need_disp) || (rfp && need_log))
    ) {
        last_batch_seen = batch_alloc;
        disp_batch();
    }

    prep_show_v(cur_node, 0);     /* into diag_buf */
    if (need_diag) {
        if (need_disp)
            diag("%s%s", diag_buf, aux_buf);
        if (debugw) {
            keep_diag();
            if (debugw_count && need_disp) {
                --debugw_count;
                if (debugw_count == 0) {
                    report("301 Stopping: debug count exhausted\n");
                    fail_silent();
                }
            }
        } else
            need_diag = 0;
        /* -Ld limits the time of this invocation, not the whole run */
        if (death_delay)
            if (t1 >= death_delay) {
                keep_diag();
                report("301 Timeout after %.2fs\n", seconds(t1));
                fail_silent();
            }
    }

    if (rfp && (need_log || debugL)) {
        /* Recovery needs to know of levels not placed by best_v(), if
         * there are any with active allocations, but we don't want to
         * clutter on-screen display with that.
         */
        char *code = prep_show_v(cur_node, 1) ? "315" : "305";
#ifdef TRACK_STATS
        fprintf(rfp, "%s %s%s (%.2fs) [", code, diag_buf, aux_buf, seconds(t1));
        for (uint i = 0; i < k; ++i) {
            if (i)
                fprintf(rfp, " ");
            fprintf(rfp, "%lu", count_bad[i]);
        }
        fprintf(rfp, "]\n");
#else
        fprintf(rfp, "%s %s%s (%.2fs)\n", code, diag_buf, aux_buf, seconds(t1));
#endif
        logt = t1 + log_delay;
        need_log = 0;
        if (debugL && debugL_count) {
            --debugL_count;
            if (debugL_count == 0) {
                report("301 Stopping: debug count exhausted\n");
                fail_silent();
            }
        }
    }
    if (!debugw && !debugL)
        need_work = 0;
}

void diag_plain(t_node *cur_node) {
    aux_sprintf("");
    diag_any(cur_node, 1);
}

/* Show progress with p^{x-1} at v_i, not (or no longer) applied: an
 * allocation about to be tried, or one that failed. On recovery it is
 * tried again, and may legitimately fail again.
 */
void diag_attempt(t_node *cur_node, uint vi, ulong p, uint x) {
    uint vil = cur_vlevel[vi];
    t_allocation *ap = &value[vi].alloc[vil];
    ap->p = p;
    ap->x = x;
    ap->level = cur_node->level;   /* for expanded diagnostics */
    ++cur_vlevel[vi];
    diag_plain(cur_node);
    --cur_vlevel[vi];
}

void diag_walk_v(t_node *cur_node, ulong ati, ulong end) {
    aux_sprintf(": %lu / %lu", ati, end);
    diag_any(cur_node, !(debugw && !debugW && ati));
}

void diag_walk_zv(t_node *cur_node, mpz_t ati, mpz_t end) {
    aux_sprintf(": %Zu / %Zu", ati, end);
    diag_any(cur_node, !(debugw && !debugW && mpz_sgn(ati)));
}

void diag_walk_pell(t_node *cur_node, uint pc) {
    aux_sprintf(": P%u", pc);
    diag_any(cur_node, !(debugw && !debugW && pc));
}

/* Mark each unforced level on the current path at which best_v() would
 * no longer choose the position chosen there, so that progress lines
 * show it for recovery. best_v() is asked again as it would be on
 * recovery, given the depths of the positions and the strategy in force
 * when the choice was made. The depth of each position then
 * was 1 more than the number of its allocations made at earlier levels.
 */
uint best_v(t_act *cur_act);
void mark_unsorted(void) {
    /* nothing to do while reading a recovery log, before any levels */
    if (level <= final_level + 1)
        return;
    bool suffixed = 0;
    uint save[k];
    memcpy(save, cur_vlevel, k * sizeof(uint));
    uint save_strategy = strategy;
    /* the current level too, if its position has been chosen */
    for (uint li = final_level + 1; li <= level; ++li) {
        t_act *actp = &acts[li];
        /* from an action with a suffix up, recovery rebuilds from that */
        if (has_suffix(actp->action))
            suffixed = 1;
        if (actp->action != A_UNFORCED || actp->p == 0 || suffixed) {
            actp->unsorted = 0;
            continue;
        }
        /* set cur_vlevel[] as it would have been at this level */
        for (uint vj = 0; vj < k; ++vj) {
            t_allocation *alloc = value[vj].alloc;
            uint d = 1;
            while (d < save[vj] && alloc[d].level < li)
                ++d;
            cur_vlevel[vj] = d;
        }
        strategy = actp->choice_strategy;
        /* if best_v() would now choose the 6X walk, no mark is needed */
        uint bvi = best_v(actp);
        actp->unsorted = (bvi == BV_6X) ? 0 : (bvi != actp->vi);
    }
    strategy = save_strategy;
    memcpy(cur_vlevel, save, k * sizeof(uint));
}

void updated_zmax(void) {
    /* If we are allocating p^{2^m-1}, changing zmax affects calculation
     * of best_v(). Existing cached limits must be recalculated, and the
     * positions best_v() would no longer choose must be marked in
     * progress lines so that recovery can sync correctly.
     */
    if (highpow) {
        /* there are no allocations if cur_vlevel is not initialised */
        if (cur_vlevel) {
            for (uint vi = 0; vi < k; ++vi) {
                t_value *v = &value[vi];
                for (uint ai = 1; ai < cur_vlevel[vi]; ++ai) {
                    t_allocation *ap = &v->alloc[ai];
                    if (!ispow2_u64(ap->t))
                        continue;
                    mpz_add_ui(ap->lim, zmax, TYPE_OFFSET(vi));
                    if (ap->t > 1) {
                        mpz_fdiv_q(ap->lim, ap->lim, ap->q);
                        mpz_root(ap->lim, ap->lim, divisors[ap->t].sumpm);
                    }
                }
            }
            mark_unsorted();
        }
    } else if (strategy == STRATEGY_6X && cur_vlevel) {
        /* best_6x() also depends on zmax */
        mark_unsorted();
    }
}

/* Record a new candidate, tightening zmax if allowed */
void update_best(mpz_t c) {
    if (!seen_best || mpz_cmp(c, best) <= 0) {
        mpz_set(best, c);
        ++seen_best;
    }
    if (improve_max && mpz_cmp(c, zmax) <= 0) {
        mpz_sub_ui(zmax, c, 1);
        updated_zmax();
    }
}

/* Record a found candidate; returns FALSE if we should continue testing
 * larger candidates with the current set of allocations.
 */
bool candidate(mpz_t c) {
#if defined(TYPE_r)
    if (mpz_fits_ulong_p(c) && mpz_get_ui(c) == n)
        return 0;
#endif
    /* no walk should start at or before the minimum, but make sure */
    if (mpz_cmp(c, zmin) <= 0)
        return 0;
    keep_diag();
    double t1 = utime();
    report("202 Candidate %Zu (%.2fs)\n", c, seconds(t1));
    update_best(c);
    return improve_max;
}

void free_levels(void) {
    for (uint i = 0; i < maxlevel; ++i) {
        t_node *np = &nodes[i];
        free(np->pfreev);
        mpz_clear(np->aq);
        mpz_clear(np->rq);
        prime_iterator_destroy(&acts[i].piter);
    }
    free(nodes);
    free(acts);
    free(cur_vlevel);
}

void init_levels(void) {
    nodes = calloc(maxlevel + 1, sizeof(t_node));
    acts = calloc(maxlevel + 1, sizeof(t_act));
    cur_vlevel = calloc(k, sizeof(uint));
    for (uint i = 0; i < maxlevel; ++i) {
        t_node *np = &nodes[i];
        np->level = i;
        np->pfreev = malloc(pfree_vecsize * sizeof(uint));
        mpz_init(np->aq);
        mpz_init(np->rq);
        acts[i].level = i;
#if 0
        /* not needed, prime_iterator_setprime() later will initialize */
        prime_iterator_init(&acts[i].piter);
#endif
    }
    t_node *np = &nodes[0];
    np->have_min = (sminp || sminpx) ? 0 : 1;
    np->have_square = 0;
    np->nextpi = 0;
#if defined(TYPE_a)
    np->maxp = divisors[n].high;  /* covers never_unforced() */
#else
    np->maxp = 0;
#endif
    /* the -p cap, if any: under -W that is midp[], see prep_mp() */
    np->cap = (smaxp || smaxpx) ? (need_midp ? midp : maxp) : NULL;
    np->vi_depth = 1;
    memset(np->pfreev, 0xff, pfree_vecsize * sizeof(uint));
    if (forcedp + 1 > 8 * sizeof(np->fp_need))
        fail("FIXME: too many forced primes");
    np->fp_need = (1U << forcedp) - 1;
    mpz_set_ui(np->aq, 1);
    mpz_set_ui(np->rq, 0);
    acts[0].action = A_BASE;
    acts[0].next_best = 0;
    for (uint j = 0; j < k; ++j)
        cur_vlevel[j] = 1;
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
        ap->level = 0;
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
    t_divisors *dp = &divisors[target_lcm];
    *p = calloc(target_lcm + 1, sizeof(t_mint *));
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
    t_divisors *dp = &divisors[target_lcm];
    for (uint di = 0; di < dp->alldiv; ++di) {
        uint d = dp->div[di];
        uint h = divisors[d].high;
        if (h <= 2)
            break;
        if ((target_lcm / d) % h)
            continue;
        restricted = realloc(restricted, (restricted_count + 1) * sizeof(uint));
        restricted[restricted_count++] = d;
    }
    if (restricted_count) {
        mint_base_restricted = malloc(restricted_count * sizeof(t_mint **));
        for (uint i = 0; i < restricted_count; ++i)
            mint_init_base(&mint_base_restricted[i]);
    }

    /* mintau() is asked for t dividing n/h(n); or under -k for t dividing
     * n/2, since that fixes the prime to an odd power before any other
     * (see mintau_at()).
     */
    uint maxtau = target_lcm / divisors[target_lcm].high;
    if (kern_b && !(target_lcm & 1))
        maxtau = target_lcm / 2;
    dp = &divisors[maxtau];
    uint maxdepth = dp->sumpm;
    pfree_vecsize = (nsprimes + 31) >> 5;
    mint_maxdepth = maxdepth;
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
    uint maxtau = target_lcm / divisors[target_lcm].high;
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

    uint maxtau = target_lcm / divisors[target_lcm].high;
    t_divisors *dp = &divisors[maxtau];
    uint maxdepth = dp->sumpm;
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

t_recover *new_stack(void) {
    t_recover *stack = malloc(sizeof(t_recover));
    stack->f = malloc(k * sizeof(t_fact));
    for (uint i = 0; i < k; ++i)
        init_fact(&stack->f[i]);
    stack->forced = calloc(k * maxfact, sizeof(uint));
    stack->force = 0;
    return stack;
}

void free_stack(t_recover *stack) {
    for (uint vi = 0; vi < k; ++vi)
        free_fact(&stack->f[vi]);
    free(stack->f);
    free(stack->forced);
    free(stack);
}

void done(void) {
    /* update window title on completion */
    if (vt100)
        printf("\x1b]2;b%ld: done\a",
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
    if (rstack)
        free_stack(rstack);
    if (istack)
        free_stack(istack);
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
    done_zrootmod();
    done_coulfact();
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

/* Open the cycle counter for utime(), unless -Lc0 asked for CPU seconds.
 * Failure is not fatal: we report it with a 000 line after the 001 line,
 * and times are then CPU seconds; the 001 line marks which we have.
 */
void init_cycles(void) {
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
            cyc_errno = errno;
    }
#endif
    /* the clock may have changed */
    t0 = utime();
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

    init_coulfact();
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
    act_recover.action = A_NONE;
}

static inline uint max_forcep(void);
uint list_forcep(uint *pi);

/* Add the prime powers of zn^e to f, in ascending order of p.
 * A prime factor that does not fit a ulong is a fatal error.
 */
void add_product(t_fact *f, mpz_t zn, uint e) {
    factor_state fs;
    uint start = f->count;

    fs_init(&fs);
    mpz_set(fs.n, zn);
    while (factor_one(&fs)) {
        if (!mpz_fits_ulong_p(fs.f))
            fail("517 prime factor %Zu of %Zu is too large", fs.f, zn);
        t_ppow pp = { mpz_get_ui(fs.f), fs.e * e };
        /* factor_one() finds them in no particular order */
        uint i = f->count;
        add_fact(f, pp);
        for (; i > start && f->ppow[i - 1].p > pp.p; --i)
            f->ppow[i] = f->ppow[i - 1];
        f->ppow[i] = pp;
    }
    fs_clear(&fs);
}

/* Move the forced primes at v_i to the start of f, in the order that
 * insert_forced() will look for them, leaving the rest in their order.
 * Needed when an init pattern gives a product at v_i, since its factors
 * are found in ascending order. A prime given more than once at v_i is
 * a fatal error.
 */
void order_forced(t_fact *f, uint vi) {
    for (uint i = 1; i < f->count; ++i)
        for (uint j = 0; j < i; ++j)
            if (f->ppow[i].p == f->ppow[j].p)
                fail("518 %lu given twice at v_%u in init or recovery pattern",
                        f->ppow[i].p, vi);

    uint pi[max_forcep()];
    uint count = list_forcep(pi), next = 0;
    for (uint fpi = 0; fpi < count; ++fpi) {
        for (uint j = next; j < f->count; ++j) {
            if (f->ppow[j].p != pi[fpi])
                continue;
            t_ppow pp = f->ppow[j];
            memmove(&f->ppow[next + 1], &f->ppow[next],
                    (j - next) * sizeof(t_ppow));
            f->ppow[next++] = pp;
            break;
        }
    }
}

/* Parse a "305" log line for initialization.
 * Input string should point after the initial "305 ".
 * If 'expanded' is true, expects a "315" expanded line instead.
 */
void parse_305(char *s, t_recover **stackp, bool expanded) {
    double dtime;
    t_ppow pp;
    e_action shown = A_NONE;   /* the action of the suffix seen, if any */

    t_recover *stack = new_stack();
    *stackp = stack;

    if (s[0] == 'b') {
        int off = 0;
        sscanf(s, "b%ld: %n", &batch_alloc, &off);
        if (off == 0) {
            batch_alloc = -1;
            sscanf(s, "b*: %n", &off);
            if (off == 0)
                fail("501 error parsing 305 line '%s'", s);
        } else {
            /* the run that logged this had reached a valid batch */
            seen_valid = 1;
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
        bool product = 0;
        while (1) {
            /* -I allows unfactored entries, so the base may be large */
            char *end = s + strspn(s, "0123456789");
            char c = *end;
            *end = 0;
            int bad = mpz_set_str(Z(p3_base), s, 10);
            *end = c;
            if (bad || mpz_sgn(Z(p3_base)) == 0)
                fail("519 expected a positive number in init or recovery"
                        " pattern");
            s = end;
            pp.e = (s[0] == '^') ? strtoul(&s[1], &s, 10) : 1;
            if (mpz_cmp_ui(Z(p3_base), 1) == 0 || pp.e == 0)
                ;
            else if (mpz_fits_ulong_p(Z(p3_base))
                    && bpsw_u64(mpz_get_ui(Z(p3_base)))) {
                pp.p = mpz_get_ui(Z(p3_base));
                add_fact(&stack->f[i], pp);
            } else {
                add_product(&stack->f[i], Z(p3_base), pp.e);
                product = 1;
            }
            if (expanded && s[0] == '(') {
                uint off = strtoul(&s[1], &s, 10);
                stack->forced[off] = i + 1;
                if (stack->force <= off)
                    stack->force = off + 1;
                if (s[0] != ')')
                    fail("513 Missing ')' in expanded recovery pattern");
                ++s;
            }
            if (s[0] != '.')
                break;
            ++s;
        }
        if (product)
            order_forced(&stack->f[i], i);
        /* reverse them, so we can pop as we allocate */
        reverse_fact(&stack->f[i]);
    }
    for (e_action a = 0; a < A_NONE; ++a) {
        char *tag = action_ops[a].tag;
        if (tag == NULL || strncmp(s, tag, strlen(tag)) != 0)
            continue;
        if (shown != A_NONE)
            fail("520 more than one suffix in recovery pattern");
        shown = a;
        act_recover.action = a;
        s = action_ops[a].parse(s + strlen(tag));
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
    if (shown == A_MIDP && !need_midp && !kern_b)
        fail("512 recovery expected -W or -k option");
    t0 -= dtime;
}

/* Returns the candidate of a 202 line, as a string of digits. */
char *digits_202(char *s) {
    int start, end, off = 0;
    sscanf(s, "202 Candidate %n%*[0-9]%n (%*[0-9.]s)%n",
            &start, &end, &off);
    if (off == 0)
        fail("error parsing 202 line '%s'", s);
    s[end] = 0;
    return &s[start];
}

void apply_pend202(void) {
    update_best(Z(rec_trail));
    have_pend202 = 0;
}

void recover(FILE *fp) {
    char *last305 = NULL;   /* 305 or 315 */
    bool expanded = 0;      /* true if it's 315 */
    char *curbuf = NULL;
    size_t len = 120, len305 = 0;
    /* The least candidate up to the last progress line is Z(rec_lead),
     * and the least since it Z(rec_trail); these are the digits in each,
     * 0 if there is none. Candidates are written with no leading zeros,
     * so one with more digits than the least need not be parsed.
     */
    size_t nlead = 0, ntrail = 0;

    while (1) {
        errno = 0;      /* getline() does not clear errno on eof */
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
        if (strncmp("305 ", curbuf, 4) == 0
            || strncmp("315 ", curbuf, 4) == 0
        ) {
            expanded = (curbuf[1] == '1');
            char *t = last305;
            last305 = curbuf;
            curbuf = t;
            size_t lt = len305;
            len305 = len;
            len = lt;
            if (ntrail) {
                if (!nlead || mpz_cmp(Z(rec_trail), Z(rec_lead)) < 0) {
                    mpz_set(Z(rec_lead), Z(rec_trail));
                    nlead = ntrail;
                }
                ntrail = 0;
            }
        } else if (strncmp("202 ", curbuf, 4) == 0) {
            char *d = digits_202(curbuf);
            size_t nd = strlen(d);
            if (!ntrail || nd <= ntrail) {
                mpz_set_str(Z(rec_cand), d, 10);
                if (!ntrail || mpz_cmp(Z(rec_cand), Z(rec_trail)) < 0) {
                    mpz_set(Z(rec_trail), Z(rec_cand));
                    ntrail = nd;
                }
            }
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
    /* apply best candidate seen before last305 */
    if (nlead)
        update_best(Z(rec_lead));
    if (last305)
        parse_305(last305 + 4, &rstack, expanded);
    /* save best candidate seen after last305 to apply after stack is rebuilt */
    if (ntrail && (!nlead || mpz_cmp(Z(rec_trail), Z(rec_lead)) < 0))
        have_pend202 = 1;
    free(curbuf);
    free(last305);
}

/* order by highest prime descending, then by value ascending */
int cmp_high(const void *va, const void *vb) {
    uint a = *(uint *)va, b = *(uint *)vb;
    int cmp = (int)divisors[b].high - (int)divisors[a].high;
    return cmp ? cmp : (int)a - (int)b;
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
 * Flip recovery wants sqrt, the square root of t_i where it is a square.
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
            if (j * j == i)
                dp->sqrt = j;
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
    if (nsprimes > MAX_NSPRIMES)
        fail("require at most %u small primes, not %u",
                MAX_NSPRIMES, nsprimes);
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
    fpb->fold = 0;
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

    if (!ispow2_u64(x))
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
        if (!ispow2_u64(ej + 1))
            seen_odd = 1;
        if (ej < ei)
            continue;
        /* Earlier element cannot have same or higher power of p */
        return TFP_BAD;
    }
    /* can fail for pcaul when p | n */
    if (p > 8 * sizeof(ulong))
        fail("TODO: cope with p > %u", 8 * sizeof(ulong));
    /* set bits for moduli 1 .. p - 1 */
    ulong seen_same = (1UL << p) - 2;   /* needs MAXK < 67 */
    for (uint j = 1; j + vi < k; ++j) {
        uint vj = vi + j;
        uint off = TYPE_OFFSET(j);
        uint ej = simple_valuation(off, p);
        if (ej == 0)
            continue;
        seen_any = 1;
        if (!ispow2_u64(ej + 1))
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
        seen_same &= ~(1UL << (off % p));   /* needs MAXK < 67 */
    }
    if (seen_same == 0)
        /* all moduli seen, so one must have a higher power of p */
        return TFP_BAD;
    /* with one modulus b left, v_i / p^e_i == -b (mod p) */
    if (ispow2_u64(seen_same) && p == 2)
        fpb->fold = p - trailing_zeroes_u64(seen_same);

    if (unforce_all && p >= unforce_all && !seen_odd)
        return TFP_SINGLE;
    if (seen_any)
        return TFP_GOOD;
    return TFP_SINGLE;
}

/* The size of array that list_forcep() needs. */
static inline uint max_forcep(void) {
#if defined(TYPE_o) || defined(TYPE_r)
    return k;
#elif defined(TYPE_a)
    /* we also force each p | n */
    return k + nf.count;
#endif
}

/* Set pi[] to the primes to force, in the order they are forced, and
 * return how many there are. pi[] must have room for max_forcep() entries.
 * Needs nf, so may be called before prep_forcep().
 */
uint list_forcep(uint *pi) {
    mpz_t pz;
    uint p, count = 0;

    mpz_init_set_ui(pz, 1);
#if defined(TYPE_o) || defined(TYPE_r)
    while (1) {
        _GMP_next_prime(pz);
        p = mpz_get_ui(pz);
        if (p > k)
            break;
        pi[count++] = p;
    }
#elif defined(TYPE_a)
    /* divisors of n must be force_all, so must come before other primes */
    for (uint i = 0; i < nf.count; ++i) {
        p = (uint)nf.ppow[i].p;
        pi[count++] = p;
    }
    while (1) {
        _GMP_next_prime(pz);
        p = mpz_get_ui(pz);
        if (p > k)
            break;
        if (n % p)
            pi[count++] = p;
    }
#endif
    mpz_clear(pz);
    return count;
}

void prep_forcep(void) {
    uint p;
    uint pi[max_forcep()];

    forcedp = list_forcep(pi);

    uint maxbatch = 0;
    for (uint i = 0; i < k; ++i)
        maxbatch += divisors[ target_t(i) ].alldiv;

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
                /* a cap of 0 means no cap, as in limit_p() */
                if (restrict_forced && maxp[fx - 1] && maxp[fx - 1] < p)
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
    *mp = calloc(target_lcm, sizeof(ulong));
    if (sp) {
        char *t = strchr(sp, '^');
        t_divisors *dp = &divisors[target_lcm];
        if (t) {
            *t = 0;
            ulong p = ulston(sp);
            uint e = ulston(t + 1);
            *t = '^';
            mpz_ui_pow_ui(Z(temp), p, e);
            for (uint di = 0; di < dp->alldiv; ++di) {
                uint dm = dp->div[di] - 1;
                if (highpow ? dm == 0 : ispow2_u64(dm + 1))
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
                if (highpow ? dm == 0 : ispow2_u64(dm + 1))
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
    t_divisors *dp = &divisors[target_lcm];
    for (uint di = 0; di < dp->alldiv; ++di) {
        uint dm = dp->div[di] - 1;
        if (highpow ? dm == 0 : ispow2_u64(dm + 1))
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
bool alloc_square(t_node *cur, uint vi) {
    t_value *v = &value[vi];
    uint vlevel = cur_vlevel[vi];
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

    allzrootmod(stash_level, Z(asq_o), g, Z(asq_qq));
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
    /* The one batch of a search with no forced primes is otherwise at
     * level 0, and a -W sweep needs a level above its own.
     */
    if (!saw_square && forcedp == 0 && need_midp)
        fail("523 -W is not supported with no forced primes");
    if (saw_square) {
        /* we rely on resarray(0) being available for other uses, so we
         * must use a dummy level here before allocating the square(s)
         */
        t_node *prev = &nodes[level - 1];
        t_node *cur = &nodes[level];
        t_act *cur_act = &acts[level];
        cur->have_min = prev->have_min;
        cur->nextpi = prev->nextpi;
        cur->maxp = prev->maxp;
        cur->cap = prev->cap;
        cur->kern = NULL;
        cur->fp_need = prev->fp_need;
        memcpy(cur->pfreev, prev->pfreev, pfree_vecsize * sizeof(uint));
        mpz_set(cur->aq, prev->aq);
        mpz_set(cur->rq, prev->rq);
        cur_act->action = A_PRESQ;
        cur_act->p = 0;
        cur->have_square = 0;
        for (uint vi = 0; vi < k; ++vi)
            if (target_t(vi) & 1)
                alloc_square(cur, vi);
        ++level;
        ++final_level;
    }
}

/* Cases proven impossible by hand, but not by the search itself. Like
 * check_exceptions() in the perl Type:: classes, an entry { type, n, k }
 * means no solution exists for any (n, k') with k' > k. Each entry has
 * its proof documented here.
 *
 * r(49, 2): we need tau(v + i) = (3, 6, 4) for i = 0 .. 2. Then v = p^2
 * with p prime, and p = 2 fails, so p is odd. That gives v + 1 == 2 (mod 8),
 * so v + 1 = 2y^2 and v + 2 = 2(v + 1) - v = (2y - p)(2y + p). p = 3 fails,
 * so 3 | v + 2; and tau(v + 2) = 4 now requires 2y - p to be in { 1, 3 }.
 * But 2y - p > (sqrt(2) - 1)p so we need only check p in { 5, 7 }.
 * 5 fails, so p = 7 giving v = 49 is the only solution.
 *
 * r(625, 4): we need tau(v + i) = (5, 4, 8, 6, 4) for i in 0 .. 4. With
 * v = p^4, p in {2, 3} both fail and p = 5 gives n, so p > 5. However we
 * have p^4 + 4 = (p^2 - 2p + 2)(p^2 + 2p + 2), and for p > 5 we need
 * 5 | p^4 + 4 and both those factors > 5, so tau(v + 4) > 4.
 *
 * r(729, 4): we need tau(v + i) = (7, 8, 4, 12, 2) for i = 0 .. 4. Then
 * v = p^6 with p prime; p = 2 fails, and p = 3 is n itself, so p >= 5
 * and v + 1 == 2 (mod 8). Since p^6 == p^2 (mod 5), v is 0, 1 or 4
 * (mod 5); v == 0 needs p = 5, which fails, and v == 1 makes v + 4 = 5.
 * So 5 | v + 1, and tau(v + 1) = 8 needs v + 1 = 250 (fails) or 10q with
 * q prime. But v + 1 = (p^2 + 1)(p^4 - p^2 + 1), where the second factor
 * is odd and > 10, so the first is 2 or 10, giving p <= 3.
 */
typedef struct s_exception {
    char type;
    uint n;
    uint k;
} t_exception;
const t_exception exceptions[] = {
    { 'r', 49, 2 },
    { 'r', 625, 4 },
    { 'r', 729, 4 },
};

void check_exceptions(void) {
    for (uint i = 0; i < sizeof(exceptions) / sizeof(t_exception); ++i) {
        const t_exception *ep = &exceptions[i];
        if (ep->type == typename() && ep->n == n && ep->k < k) {
            report("403 Error: f(%u) > %u known impossible by exception"
                    " (%.2fs)\n", n, ep->k, elapsed());
            fail_silent();
        }
    }
}

void init_post(void) {
    init_cycles();
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
    simple_fact(n, &nf);
    prep_target();
    if (init_pattern)
        parse_305(init_pattern, &istack, 0);
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
#ifdef HAVE_SETPROCTITLE
    setproctitle("-D(%u %u)", n, k);
#endif
    if (!ignore_exceptions)
        check_exceptions();

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

    init_zrootmod(maxlevel);
    prep_fact();
    prep_maxforce();
    prep_mp();  /* maxp[], minp[], midp[] */
    prep_forcep();
    if (debugf)
        disp_forcep();
    prep_primes();  /* needs forcedp */
    prep_mintau();
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
    if (debugL)
        need_work = 1;
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
            fprintf(fp, " -js");
            for (uint i = 0; i < fixed_level; ++i) {
                if (i)
                    fprintf(fp, ",");
                fprintf(fp, "%u", fixed_v[i]);
            }
        } else
            fprintf(fp, " -j%u", strategy);
    }
    if (opt_print) {
        fprintf(fp, " -o");
        if (opt_flake)
            fprintf(fp, "%u", opt_flake);
    }
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
    if (kern_b)
        fprintf(fp, " -k%lu", kern_b);
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
        fprintf(fp, " -b%ld", opt_batch_min);
        if (opt_batch_min != opt_batch_max) {
            fprintf(fp, ":");
            if (opt_batch_max < LONG_MAX)
                fprintf(fp, "%ld", opt_batch_max);
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
    /* git SHA details for divrep and MPU::GMP */
    fprintf(fp, " sha=%s", DIVREP_CHANGE);
    if (strcmp(DIVREP_CHANGE, DIVREP_BASE))
        fprintf(fp, "(%s)", DIVREP_BASE);
    if (DIVREP_DIRTY)
        fprintf(fp, "*");
    fprintf(fp, ";%s", MPU_CHANGE);
    if (strcmp(MPU_CHANGE, MPU_BASE))
        fprintf(fp, "(%s)", MPU_BASE);
    if (MPU_DIRTY)
        fprintf(fp, "*");

    if (clock_is_realtime)
        fprintf(fp, " *RT*");
    /* times are cycles at the given GHz (see utime()) */
    if (cyc_fd >= 0)
        fprintf(fp, " *CY%g*", cyc_ghz);
    fprintf(fp, "\n");
    if (cyc_errno)
        fprintf(fp, "000 cycle counter unavailable (%s),"
                " times are CPU seconds\n", strerror(cyc_errno));
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
        opt_batch_min = *s ? strtol(s, NULL, 10) : 0;
        opt_batch_max = t[1] ? strtol(&t[1], NULL, 10) : LONG_MAX;
    } else {
        opt_batch_min = strtol(s, NULL, 10);
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
uint find_nextpi(t_node *cur, uint pi) {
    uint *pv = cur->pfreev;
    uint off = pi >> 5;
    uint bit = pi & 0x1f;
    while (off < pfree_vecsize) {
        uint v = pv[off] & ~((1U << bit) - 1);
        int ffs = ffs_u32(v);
        if (ffs)
            return (off << 5) + ffs - 1;
        ++off;
        bit = 0;
    }
    fail("panic: find_nextpi() fell off end of bit vector");
}

/* Find index of next unused forced prime */
static inline uint next_fpi(t_node *prev) {
    return ffs_u32(prev->fp_need) - 1;
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
    uint remain = test_prime_run(0);
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
    uint remain = test_prime_run(0);
    if (remain) {
        TRACK_BAD(nc - remain, taum[0].vi);
        return 0;
    }
    return 1;
}

/* The caller may have queued the roots of the squares it is walking:
 * we leave those on the queue for test_zmulti().
 */
bool test_zprimes(uint *need, uint nc, mpz_t ati) {
    uint good = 0;
    uint first = tm_count;
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
    uint remain = test_prime_run(first);
    if (remain) {
        TRACK_BAD(nc - remain, taum[first].vi);
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

/* The caller may have queued the roots of the squares it is walking:
 * we test those along with the rest. Having odd tau, they sort to the
 * front of the queue.
 */
bool test_zmulti(
    uint *need, uint nc, mpz_t ati, uint *t, tau_failure_handler tfh
) {
    uint good = 0;
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

/* Sort need_prime by qq multiplier ascending, then by index */
int prime_comparator(const void *va, const void *vb) {
    uint a = *(uint *)va;
    uint b = *(uint *)vb;
    int cmp = mpz_cmp(wv_qq[a], wv_qq[b]);
    return cmp ? cmp : (a > b) - (a < b);
}

/* Sort need_other by tau (power of 2 ascending, then size ascending),
 * then by size of the value to test ascending, then by index.
 * Size is given by oc_size[]: in walk_v() the qq multiplier, in walk_1()
 * the value itself.
 * TODO: if we implement trial division to higher levels to show
 * a given tau is not reachable, we may want tau by size descending.
 */
uint *oc_t;
mpz_t *oc_size;
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
    int cmp = mpz_cmp(oc_size[a], oc_size[b]);
    return cmp ? cmp : (a > b) - (a < b);
}

/* Sort inverses by modulus ascending, then by value ascending */
int inv_comparator(const void *va, const void *vb) {
    t_mod *a = (t_mod *)va;
    t_mod *b = (t_mod *)vb;
    if (a->m != b->m)
        return (b->m < a->m) - (a->m < b->m);
    return (b->v < a->v) - (a->v < b->v);
}

void walk_v(t_node *cur_node, mpz_t start) {
#ifdef SQONLY
    if (!cur_node->have_square)
        return;
#endif
    if (!cur_node->have_min) {
        t_act *cur_act = &acts[cur_node->level];
        ulong min = minp[cur_act->x - 1];
        if (min)
            level_setp(cur_act, min);
        return;
    }

    mpz_t *q[k];
    mpz_t *m = &cur_node->rq;
    uint t[k];
    mpz_t *aq = &cur_node->aq;
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
        /* the first with v_0 > zmin */
        mpz_sub(Z(wv_ati), zmin, *m);
        mpz_fdiv_q(Z(wv_ati), Z(wv_ati), *aq);
        mpz_add_ui(Z(wv_ati), Z(wv_ati), 1);
    }

    for (uint vi = 0; vi < k; ++vi) {
        t_value *vp = &value[vi];
        uint vlevel = cur_vlevel[vi];
        q[vi] = &vp->alloc[vlevel - 1].q;
        t[vi] = vp->alloc[vlevel - 1].t;
        mpz_divexact(wv_qq[vi], *aq, *q[vi]);
        mpz_add_ui(wv_o[vi], *m, TYPE_OFFSET(vi));
        mpz_divexact(wv_o[vi], wv_o[vi], *q[vi]);
        for (uint ai = 1; ai < vlevel; ++ai) {
            t_allocation *ap = &vp->alloc[ai];
            /* No inverse exists if p | aq / q_i, when the CRT has already
             * fixed v_i / q_i (mod p), as for p = 2 and other folds.
             */
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
    oc_size = wv_qq;
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
                /* v_0 > zmin needs x^2 > (zmin + i) / q_i, rounded down */
                mpz_add_ui(Z(temp), zmin, TYPE_OFFSET(sqi));
                mpz_fdiv_q(Z(temp), Z(temp), *qi);
                mpz_sqrt(Z(temp), Z(temp));
                while (next_pell(Z(wv_x), Z(wv_y))) {
                    if (mpz_cmp(Z(temp), Z(wv_x)) < 0)
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
                    diag_walk_pell(cur_node, pc);

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

        t_results *xr = res_array(cur_node->level);
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
                diag_walk_zv(cur_node, Z(wv_ati), Z(wv_end));
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
            diag_walk_v(cur_node, ati, end);
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
void walk_1(t_node *cur_node, uint vi) {
#ifdef SQONLY
    if (!cur_node->have_square)
        return;
#endif
    if (!cur_node->have_min) {
        t_act *cur_act = &acts[cur_node->level];
        ulong min = minp[cur_act->x - 1];
        if (min)
            level_setp(cur_act, min);
        return;
    }

    {
        /* calculate v_0 */
        t_value *vip = &value[vi];
        t_allocation *aip = &vip->alloc[cur_vlevel[vi] - 1];
        mpz_sub_ui(Z(w1_v), aip->q, TYPE_OFFSET(vi));
    }

    if (mpz_cmp(Z(w1_v), zmin) <= 0)
        return;
    ++countw;
    if (check && !cvec_testv(cx0, Z(w1_v)))
        return;


    /* Verify v_0 == rq (mod aq) to guarantee all allocations will
     * divide exactly. */
    mpz_fdiv_r(Z(w1_r), Z(w1_v), cur_node->aq);
    if (mpz_cmp(Z(w1_r), cur_node->rq) != 0)
        return;

    uint t[k];
    uint need_prime[k];
    uint need_other[k];
    uint npc = 0, noc = 0;
    for (uint vj = 0; vj < k; ++vj) {
        if (vi == vj)
            continue;
        t_value *vjp = &value[vj];
        uint vjl = cur_vlevel[vj];
        t_allocation *ajp = &vjp->alloc[vjl - 1];
        mpz_add_ui(Z(w1_j), Z(w1_v), TYPE_OFFSET(vj));
        if (vjl > 1) {
            mpz_divexact(Z(w1_j), Z(w1_j), ajp->q);
            /* verify we don't double up on any allocated primes */
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
    oc_size = wv_o;
    qsort(need_other, noc, sizeof(uint), &other_comparator);
    if (!test_1multi(need_other, noc, t, walk_1_failure))
        return;
    candidate(Z(w1_v));
    return;
}

/* test a set of cases where v_i will have all divisors accounted for:
 * v_i = q_i . p^{x-1} for primes p with plow < p <= phigh.
 */
void walk_1_set(
    t_node *prev_node, t_act *cur_act,
    uint vi, ulong plow, ulong phigh, uint x
) {
    t_node *cur_node = &nodes[cur_act->level];
#ifdef SQONLY
    if (!cur_node->have_square)
        return;
#endif
    /* p must exceed minp[x - 1] */
    if (!cur_node->have_min && plow < minp[x - 1])
        plow = minp[x - 1];

    t_value *vip = &value[vi];
    uint vil = cur_vlevel[vi];
    t_allocation *aip = &vip->alloc[vil - 1];
    if (mpz_sgn(zmin) > 0) {
        /* v_0 > zmin needs p^{x-1} > (zmin + i) / q_i, rounded down */
        mpz_add_ui(Z(temp), zmin, TYPE_OFFSET(vi));
        mpz_fdiv_q(Z(temp), Z(temp), aip->q);
        mpz_root(Z(temp), Z(temp), x - 1);
        if (!mpz_fits_ulong_p(Z(temp)))
            return;
        ulong pmin = mpz_get_ui(Z(temp));
        if (plow < pmin)
            plow = pmin;
    }

    mpz_divexact(Z(w1_m), prev_node->aq, aip->q);
    bool need_mod = (mpz_cmp_ui(Z(w1_m), 1) == 0) ? 0 : 1;
    if (need_mod) {
        /* we need p == (rq + TYPE_OFFSET(vi)) / aip->q (mod aq / aip->q) */
        mpz_add_ui(Z(w1_mr), prev_node->rq, TYPE_OFFSET(vi));
        mpz_divexact(Z(w1_mr), Z(w1_mr), aip->q);
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
        uint vjl = cur_vlevel[vj];
        t_allocation *ajp = &vjp->alloc[vjl - 1];
        t[vj] = ajp->t;
        if (t[vj] == 1)
            fail("should never see multiple values with t==1");
        if (t[vj] == 2)
            need_prime[npc++] = vj;
        else
            need_other[noc++] = vj;
    }

    level_setp(cur_act, plow);
    while (1) {
        ulong p = prime_iterator_next(&cur_act->piter);
        if (p > phigh)
            break;
        if (known_prime(prev_node, p))
            continue;
        /* Must diag before need_mod checks, which can reject a high
         * proportion of primes.
         */
        if (need_work)
            diag_attempt(cur_node, vi, p, x);
        mpz_ui_pow_ui(Z(w1_v), p, x - 1);
        if (need_mod) {
            /* TODO: think about a more efficient approach when the modulus
             * is large: at a certain point generating each am+r and testing
             * primality is going to be less work than generating every prime
             * and testing p == r (mod m).
             */
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
            uint vjl = cur_vlevel[vj];
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
        oc_size = wv_o;
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
 * with (i, p, x - x'). For the second call we set retry=x'.
 * If fold is non-zero, v_i is known to be fold.p^e (mod p^{e+1}) for
 * its whole power p^e (see t_forcebatch); when called twice, the first
 * call passes 0.
 * This function was originally designed around the assumption that,
 * other than for the retry case, p would not previously have been
 * seen; however modular fixes via -m or -c change that, requiring a
 * rethink of the logic as a whole.
 */
bool update_residues(t_node *old, t_node *new,
        uint vi, ulong p, uint x, mpz_t px, uint retry, uint fold) {
    uint vj = sq0;
    t_value *vjp = &value[vj];
    uint jlevel = cur_vlevel[vj] - 1;
    if (x == 0) {
        res_copy(new->level, old->level);
        return 1;
    }
    /* under -a4, the square may be fully allocated: nothing to track */
    if (vjp->alloc[jlevel].t == 1)
        return 1;
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

        if (fold) {
            /* We have residues mod m, but the fold makes aq / q_j
             * (p.m): v_j / q_j == fold / q'_j (mod p), with q'_j the
             * old q_j. So extend them by the roots mod p of that.
             * For p = 2 that takes the odd one of (r, r + m).
             */
            ulong a = mulmod_u64(fold, invert_u64(
                mpz_fdiv_ui(vjp->alloc[jlevel - 1].q, p), p
            ), p);
            mpz_set_ui(Z(ur_a), a);
            mpz_set_ui(Z(ur_ipg), p);
            zroot_extend(new->level, new->level, Z(ur_m), Z(ur_a),
                    oldg, p, 1, Z(ur_ipg));
            if (res_array(new->level)->count == 0)
                return 0;
            /* update ur_m for passing to zroot_extract */
            mpz_mul_ui(Z(ur_m), Z(ur_m), p);
        }

        sqg[jlevel] = newg;
        if (oldg == newg)
            return 1;

        /* we want to upgrade the roots from oldg to newg
         * It is guaranteed that oldg | newg. */
        zroot_extract(new->level, new->level, newg / oldg, Z(ur_m));
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
    if (fold) {
        /* v_i == fold.p^e (mod p^{e+1}) for its whole power p^e,
         * e = x - 1 + retry
         */
        ++x;
        mpz_ui_pow_ui(Z(ur_ipg), p, retry);
        mpz_mul(Z(ur_ipg), Z(ur_ipg), px);
        mpz_addmul_ui(Z(ur_a), Z(ur_ipg), fold);
        mpz_mul_ui(Z(ur_ipg), px, p);
        ppx = ZP(ur_ipg);
    } else {
        ppx = PARAM_TO_PTR(px);
    }

    /* in the non-retry case, m = old->aq / q_j; in the retry case, we
     * need to take the previous value of q_j */
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

    /* p may already divide m, via fold (a p^0 tail) or modfix */
    if ((fold || have_modfix) && mpz_divisible_ui_p(Z(ur_m), p)) {
        /* zroot_extend() needs coprime moduli to deal with, so we must
         * downgrade the input roots before calling it */
        uint fix = 0;
        while (mpz_divisible_ui_p(Z(ur_m), p)) {
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

    zroot_extend(new->level, from, Z(ur_m), Z(ur_a), g, p, x - 1, *ppx);
    if (res_array(new->level)->count == 0)
        return 0;
    return 1;
}

/* Combine v_0 == -i (mod px) for the allocation of px = p^{x-1} at v_i
 * with old->rq, old->aq into new->rq, new->aq; returns FALSE if they
 * are inconsistent. p usually does not divide old->aq, but it may via
 * a modfix, a 2^0 tail (apply_null()) or a clashing -I pattern.
 * If fold is non-zero, v_i / px == fold (mod p), so we can combine
 * instead v_0 == fold.px - i (mod p.px): see t_forcebatch.
 */
bool update_chinese(
    t_node *old, t_node *new, uint vi, ulong p, mpz_t px, uint fold
) {
    ulong off = TYPE_OFFSET(vi);
    /* chinese_ppow() needs m < 2^62 for invert_u64() */
    if (mpz_cmp_ui(px, (1UL << 62) / p) < 0) {
        ulong m = mpz_get_ui(px);
        ulong s = fold * m;
        if (fold)
            m *= p;
        s = (s + m - off % m) % m;
        return chinese_ppow(new->rq, new->aq, old->rq, old->aq, p, m, s);
    }
    /* px > off, so fold.px - off is a valid residue, or px - off */
    mpz_mul_ui(Z(uc_minusvi), px, fold ? fold : 1);
    mpz_sub_ui(Z(uc_minusvi), Z(uc_minusvi), off);
    if (fold) {
        mpz_mul_ui(Z(uc_px), px, p);
        return chinese_ppow_z(new->rq, new->aq, old->rq, old->aq, p,
                Z(uc_px), Z(uc_minusvi));
    }
    return chinese_ppow_z(new->rq, new->aq, old->rq, old->aq, p,
            px, Z(uc_minusvi));
}

/* An unforced allocation of p^e at one v_i fixes v_i / p^e (mod p)
 * only for p = 2: see t_forcebatch.
 */
static inline uint single_fold(ulong p) {
    return (p == 2) ? 1 : 0;
}

/* Allocate p^{x-1} to v_{vi}. Returns FALSE if it is invalid.
 * On success updates value[vi] and cur_vlevel[vi], and checks if this
 * creates a new square.
 * Does not update existing square residues, see update_residues() for that.
 */
bool apply_allocv(t_node *prev_node, t_node *cur_node,
        uint vi, ulong p, uint x, mpz_t px) {
    t_value *v = &value[vi];
    uint vlevel = cur_vlevel[vi];
    t_allocation *prev = &v->alloc[vlevel - 1];
    t_allocation *cur = &v->alloc[vlevel];

    /* invalid if x does not divide remaining tau */
    if (prev->t % x)
        return 0;

    ++cur_vlevel[vi];   /* needed before alloc_square() */
    cur->p = p;
    cur->x = x;
    cur->t = prev->t / x;
    cur->level = cur_node->level;
    mpz_mul(cur->q, prev->q, px);

    if (highpow && ispow2_u64(cur->t)) {
        mpz_add_ui(cur->lim, zmax, TYPE_OFFSET(vi));
        if (cur->t > 1) {
            mpz_fdiv_q(cur->lim, cur->lim, cur->q);
            mpz_root(cur->lim, cur->lim, divisors[cur->t].sumpm);
        }
    }

    /* is this newly a square? */
    if ((cur->t > 1) && (cur->t & 1) && !(prev->t & 1))
        if (!alloc_square(cur_node, vi)) {
            --cur_vlevel[vi];
            return 0;
        }

    return 1;
}

void apply_pfreev(t_node *prev_node, t_node *cur_node, ulong p) {
    uint *pfreev = cur_node->pfreev;
    memcpy(pfreev, prev_node->pfreev, pfree_vecsize * sizeof(uint));
    if (p == 0 || p > lastprime)
        return;
    uint pi = ptoi[p];
    pfreev[pi >> 5] &= ~(1U << (pi & 0x1f));
}

/* Update the level for the allocation of p^{x-1} to v_{vi}.
 * Does not update node.rq, node.aq: see update_chinese() for that.
 */
void apply_level(t_node *prev, t_node *cur, uint vi, ulong p, uint x) {
    t_act *cur_act = &acts[cur->level];
    cur_act->vi = vi;
    cur_act->p = p;
    cur_act->x = x;
    cur->have_square = prev->have_square;
    cur->nextpi = prev->nextpi;
    cur->fp_need = prev->fp_need;
    /* init cur->pfreev, with new prime now unavailable if used */
    apply_pfreev(prev, cur, (x > 1) ? p : 0);
    if (p == sprimes[cur->nextpi])
        cur->nextpi = find_nextpi(cur, cur->nextpi);
    cur->maxp = (x > 1 && p > prev->maxp) ? p : prev->maxp;
    cur->cap = prev->cap;
    cur->kern = NULL;
}

/* Apply a notional level of p^0 at v_0.
 * Also sets node.rq, node.aq and residues.
 */
void apply_null(t_node *prev, t_node *cur, ulong p) {
    uint vi = 0;    /* clarify where we are using this */
    apply_level(prev, cur, vi, p, 1);
    cur->have_min = prev->have_min;
    if (p == 2 && mpz_odd_p(prev->aq)
            && !(unforce_all && unforce_all <= 2)) {
        /* Without -F, a tail value of 2^0 can only occur with k=3,
         * force_all < 2, and implies v_1 is even so v_0 is odd. We
         * manually calculate the effective update_chinese().
         * Under -F with unforce_all <= 2 the tail also stands for
         * batches with 2 at several positions, including v_0, that
         * were left for the walk to find, so we cannot fix v_0's
         * parity.
         */
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
        update_residues(prev, cur, vi, p, 0, Z(zone), 0, 0);
    cur->vi_depth = cur_vlevel[vi];
}

/* Allocate a non-fixed (non-batch) prime p^{x-1} to v_{vi}. Returns FALSE
 * if it is invalid, or if no work to do.
 * Updates level and value, updates or propagates square residues.
 */
bool apply_single(t_node *prev, t_node *cur, uint vi, ulong p, uint x) {
    apply_level(prev, cur, vi, p, x);
    cur->have_min = prev->have_min || (minp[x - 1] && p > minp[x - 1]);
    mpz_ui_pow_ui(px, p, x - 1);
    if (!update_chinese(prev, cur, vi, p, px, single_fold(p)))
        return 0;

#ifdef CHECK_OVERFLOW
    /* if rq > zmax, no solution <= zmax is possible */
    if (mpz_cmp(cur->rq, zmax) > 0 && !any_bound)
        return 0;
#endif

    /* this can fail only by requiring an impossible square */
    if (!apply_allocv(prev, cur, vi, p, x, px))
        return 0;

    t_value *vp = &value[vi];
    uint t = vp->alloc[ cur_vlevel[vi] - 1 ].t;
    if (t == 1) {
        walk_1(cur, vi);
        /* nothing more to do */
        --cur_vlevel[vi];
        return 0;
    }

    /* did we already have a square? */
    if (prev->have_square) {
        if (!update_residues(prev, cur, vi, p, x, px, 0, single_fold(p))) {
            --cur_vlevel[vi];
            return 0;
        }
    }
    cur->vi_depth = cur_vlevel[vi];
    return 1;
}

bool apply_secondary(t_node *prev, t_node *cur, uint vi, ulong p, uint x) {
    mpz_ui_pow_ui(px, p, x - 1);
    if (!apply_allocv(prev, cur, vi, p, x, px))
        return 0;
#if defined(TYPE_o)
    if (p == 2 && x == 2 && vi >= 2 && (n % 4) == 2 && cur->have_square == 1) {
        /* n_i = 2z^2 -> n_{i-2} = 2(z-1)(z+1)
         * Switch to a strategy that takes advantage of this; the strategy
         * itself will revert when the conditions no longer hold.
         */
        if (strategy != STRATEGY_6X)
            prev_strategy = strategy;
        strategy = STRATEGY_6X;
    }
#endif
    return 1;
}

bool apply_primary(
    t_node *prev, t_node *cur, uint vi, ulong p, uint x, uint fold
) {
    apply_level(prev, cur, vi, p, x);
    mpz_ui_pow_ui(px, p, x - 1);
    /* this is wasted effort if x does not divide v_i.t, but we need it
     * for the alloc_square() calculation */
    if (!update_chinese(prev, cur, vi, p, px, fold))
        return 0;
    if (!apply_allocv(prev, cur, vi, p, x, px))
        return 0;

    /* check if we overshot */
    if (mpz_cmp(cur->rq, zmax) > 0) {
        --cur_vlevel[vi];
        return 0;
    }

    cur->vi_depth = cur_vlevel[vi];
    return 1;
}

static inline void mint_init_state(t_node *cur_node) {
    t_mint_state *s = &mint_state;
    s->pfreev = cur_node->pfreev;
    s->pfreenext = 0;
    s->pfreedepth = 0;
}

/* needs MAX_NSPRIMES < 32768 */
static inline void state_extend(signed short i) {
    t_mint_state *s = &mint_state;
    uint *pv = s->pfreev;
    uint next = s->pfreenext;
    uint nextoff = next >> 5;
    uint nextbit = next & 0x1f;
    uint depth = s->pfreedepth;
    while (depth <= i) {
        assert(nextoff < pfree_vecsize && nextbit < 8 * sizeof(uint));
        uint v = pv[nextoff] & ~((1U << nextbit) - 1);
        nextbit = ffs_u32(v);
        if (nextbit) {
            assert(depth < mint_maxdepth);
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
/* needs MAX_NSPRIMES < 32768 */
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
        /* needs MAX_NSPRIMES < 32768 */
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
        /* needs MAX_NSPRIMES < 32768 */
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
    uint maxdepth = depth0 - 1 + dp->sumpm;

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
void mintau(t_node *cur_node, mpz_t mint, uint t) {
    if (t == 1) {
        mpz_set_ui(mint, 1);
        return;
    }
    mint_init_state(cur_node);
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
    uint maxdepth = depth0 - 1 + dp->sumpm;

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
void mintau_restricted(t_node *cur_node, mpz_t mint, uint t, uint r) {
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
    mint_init_state(cur_node);
    mintau_restricted_r(0, mint, t, r, ri);
}

/* What -k does in a batch, planned once the batch is complete and kept
 * with its node (see kern_state()): whether it applies at all, its bound,
 * and as bit vectors the positions it applies to and those passed over.
 * It applies to a batch that fixes exactly one square, unless that is
 * one STRATEGY_6X takes (2.z^2 at v_i, i >= 2), which has its own loop
 * at v_{i-2} and gains nothing from the pass.
 */
typedef struct s_kern {
    int id;             /* batch_alloc when it was planned */
    bool on;
    ulong b;            /* the bound of -k, 0 if it is not to apply */
    ulong at, passed;   /* needs MAXK_KERN <= 64 */
} t_kern;

/* the plan of -k for the current batch, if any */
static inline t_kern *kern_cur(void) {
    return nodes[cur_batch_level].kern;
}

/* true if -k applies to this batch */
static inline bool kern_batch(void) {
    t_kern *ks = kern_cur();
    return ks && ks->b && ks->on;
}

/* True if the strategies may allocate p^{2^z-1}. Not in a batch that -k
 * applies to: walk_midp() has tried each prime up to its bound as the odd
 * power, limit_unforced_x() refuses the rest, and with the squares left
 * to the walk a strategy would otherwise loop over p^1 wherever else it
 * could.
 */
static inline bool kern_highpow(void) {
    return highpow && !kern_batch();
}

/* the tau left at v_i once the current batch was complete */
static inline uint kern_tau(uint vi) {
    t_value *vp = &value[vi];
    uint vil = cur_vlevel[vi];
    while (vil > 1 && vp->alloc[vil - 1].level > cur_batch_level)
        --vil;
    return vp->alloc[vil - 1].t;
}

/* true if the current batch is one STRATEGY_6X takes, see apply_secondary() */
static bool kern_6x(void) {
#if defined(TYPE_o)
    if ((n & 3) == 2 && sq0 >= 2) {
        t_value *vp = &value[sq0];
        for (uint i = 1; i < cur_vlevel[sq0]; ++i)
            if (vp->alloc[i].p == 2)
                return vp->alloc[i].x == 2;
    }
#endif
    return 0;
}

/* What -k does in the batch complete at np, see t_kern: planned when
 * first asked for, and then kept with the node until it is applied
 * afresh. Only one batch is complete at a time, so one plan is enough.
 * Returns NULL without -k.
 * The positions -k applies to are those that needed a prime to an odd
 * power and something more besides once the batch was complete.
 * A position with tau 6 left takes a single p^2 besides, with p up to
 * the square root of what is left, far too many to loop over until
 * little else remains. Where another position will take a square as its
 * last allocation after others, that square has a lower limit and
 * leaves a smaller walk, so it is always preferred, and by then the
 * walk is too small for more. So the first is then passed over: nothing
 * is allocated there at all, by walk_midp() or by any strategy, and the
 * walks cover it. (Recursion counts were unchanged by this for D(n,4),
 * D(n,5), n in 18, 30, 54, 90, 126.)
 */
static t_kern kern_ks;
static t_kern *kern_state(t_node *np) {
    if (np->kern)
        return np->kern;
    if (!kern_b)
        return NULL;
    assert(np->level == cur_batch_level);
    t_kern *ks = &kern_ks;
    bool later = 0;
    ks->id = batch_alloc;
    ks->b = kern_b;
    ks->at = 0;
    ks->passed = 0;
    ks->on = (np->have_square == 1 && !kern_6x());
    np->kern = ks;
    if (!ks->on)
        return ks;
    /* the rest need MAXK_KERN <= 64 */
    for (uint vi = 0; vi < k; ++vi) {
        uint t = kern_tau(vi);
        if (t > 2 && (t & 3) == 2) {
            ks->at |= 1UL << vi;
            if (t > 6 && t % 6 == 0)
                later = 1;
        }
    }
    if (later)
        for (uint vi = 0; vi < k; ++vi)
            if (kern_tau(vi) == 6) {
                ks->at &= ~(1UL << vi);
                ks->passed |= 1UL << vi;
            }
    return ks;
}

/* True if v_i is a position that -k applies to in this batch; needs
 * MAXK_KERN <= 64, as does kern_passed().
 */
bool kern_at(uint vi) {
    return kern_batch() && ((kern_cur()->at >> vi) & 1);
}

/* true if v_i is passed over in this batch */
bool kern_passed(uint vi) {
    return kern_batch() && ((kern_cur()->passed >> vi) & 1);
}

/* As mintau() for the tau t left at v_i, but under -k the prime taking
 * the odd power exceeds the batch's bound: the powers that could be less
 * were all tried by walk_midp().
 * Here t / 2 need not divide n/h(n): prep_mintau() allows for that.
 */
void mintau_at(t_node *cur_node, mpz_t mint, uint t, uint vi) {
    if ((t & 3) == 2 && kern_at(vi)) {
        mintau(cur_node, mint, t >> 1);
        mpz_mul_ui(mint, mint, kern_cur()->b);
    } else
        mintau(cur_node, mint, t);
}

/* as mintau_restricted() for the tau t left at v_i, see mintau_at() */
void mintau_restricted_at(
    t_node *cur_node, mpz_t mint, uint t, uint r, uint vi
) {
    if ((t & 3) == 2 && kern_at(vi)) {
        mintau_restricted(cur_node, mint, t >> 1, r);
        mpz_mul_ui(mint, mint, kern_cur()->b);
    } else
        mintau_restricted(cur_node, mint, t, r);
}

/* Order by maxp descending, then by vi ascending, then x in the order
 * of divisors[].div (cmp_high), which is the order prep_midp() pushes
 * them. Midp recovery resumes by position in this list.
 */
int midpp_comparator(const void *va, const void *vb) {
    t_midpp *ma = (t_midpp *)va;
    t_midpp *mb = (t_midpp *)vb;
    if (ma->maxp != mb->maxp)
        return (mb->maxp > ma->maxp) - (mb->maxp < ma->maxp);
    if (ma->vi != mb->vi)
        return (ma->vi > mb->vi) - (ma->vi < mb->vi);
    return cmp_high(&ma->x, &mb->x);
}

/* The caps that np's own allocation kept to, before any sweep at np. */
static inline ulong *cap_above(t_node *np) {
    return nodes[np->level - 1].cap;
}

/* Whether the sweep at np caps the allocations below it, as -W does;
 * under -k alone it does not.
 */
static inline bool sweep_caps(t_node *np) {
    return np->cap != cap_above(np);
}

/* Populate midpp[] with the capped min and max p for each possible
 * allocation of p^{x-1} at each v_i.
 */
void prep_midp(t_node *prev_node) {
    ulong *upper = cap_above(prev_node);
    ulong *lower = sweep_caps(prev_node) ? prev_node->cap : NULL;
    for (uint vi = 0; vi < k; ++vi) {
        t_value *vp = &value[vi];
        uint vil = cur_vlevel[vi];
        t_allocation *ap = &vp->alloc[vil - 1];
        uint t = ap->t;
        bool kern = kern_at(vi) && (t & 3) == 2;
        if (kern) {
            /* Each even x leaves a square here: try them all, but p^1
             * only as far as the batch's bound.
             */
            ulong b = kern_cur()->b;
            t_divisors *dp = &divisors[t];
            for (uint di = 0; di < dp->alldiv; ++di) {
                uint x = dp->div[di];
                if (x & 1)
                    continue;
                ulong target_maxp = upper ? upper[x - 1] : 0;
                if (x == 2 && (!target_maxp || b < target_maxp))
                    target_maxp = b;
                mpz_add_ui(Z(temp), zmax, TYPE_OFFSET(vi));
                mintau(prev_node, Z(wv_cand), t / x);
                mpz_fdiv_q(Z(temp), Z(temp), Z(wv_cand));
                mpz_fdiv_q(Z(temp), Z(temp), ap->q);
                mpz_root(Z(temp), Z(temp), x - 1);
                if (mpz_fits_ulong_p(Z(temp))) {
                    ulong target_limit = mpz_get_ui(Z(temp));
                    if (!target_maxp || target_limit < target_maxp)
                        target_maxp = target_limit;
                } else if (!target_maxp)
                    fail("prep_midp target %Zu out of range for %u:%u",
                            Z(temp), vi, x - 1);
                if (target_maxp <= maxforce[vi])
                    continue;
                t_midpp *this = &midpp[midppc++];
                this->vi = vi;
                this->x = x;
                this->maxp = target_maxp;
                this->minp = maxforce[vi];
            }
        }
        if (!lower)
            continue;
        if (highpow ? t == 1 : ispow2_u64(t))
            continue;
        /* Under -k no strategy allocates at any square, see below, nor
         * at a position passed over.
         */
        if (((t & 1) && kern_batch()) || kern_passed(vi))
            continue;
        /* Below a sweep allocations are capped, and then no strategy
         * allocates at a position whose remaining tau is an odd prime:
         * best_v0() .. best_v4() skip it ("skip prime powers when
         * capped"), and best_fixed() and best_6x() walk instead. Such a
         * position is a fixed square (or higher power), covered by the
         * walks for every size of root, so a p^{x-1} allocation here
         * would only duplicate that.
         */
        if ((t & 1) && divisors[t].alldiv == 2)
            continue;
        t_divisors *dp = &divisors[t];
        /* try all divisors until we reach the powers of 2 */
        for (uint di = 0; di < dp->alldiv; ++di) {
            uint x = dp->div[di];
            if (highpow ? x == 1 : ispow2_u64(x))
                break;
            if (lower[x - 1] == 0)
                continue;
            /* already done above for every p */
            if (kern && !(x & 1))
                continue;
            /* find range of p for allocating p^e at v_i */
            mpz_add_ui(Z(temp), zmax, TYPE_OFFSET(vi));
            mintau_at(prev_node, Z(wv_cand), t / x, vi);
            mpz_fdiv_q(Z(temp), Z(temp), Z(wv_cand));
            mpz_fdiv_q(Z(temp), Z(temp), ap->q);
            mpz_root(Z(temp), Z(temp), x - 1);

            /* our range of interest is p: lower[e] < p <= upper[e] */
            ulong target_maxp = upper ? upper[x - 1] : 0;
            ulong target_minp = lower[x - 1];
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

uint suffix_midp(t_act *cur_act, char *buf) {
    return sprintf(buf, " W(%lu,%u,%u)", cur_act->p, cur_act->x, cur_act->vi);
}

char *parse_midp(char *s) {
    act_recover.p = strtoul(s, &s, 10);
    if (s[0] != ',')
        fail("505 unexpected character in W(...) recovery");
    ++s;
    act_recover.x = strtoul(s, &s, 10);
    if (s[0] != ',')
        fail("505 unexpected character in W(...) recovery");
    ++s;
    act_recover.vi = strtoul(s, &s, 10);
    if (s[0] != ')')
        fail("505 unexpected character in W(...) recovery");
    return s + 1;
}

static ulong square_endr(t_node *np);
static inline bool reject_square(ulong p, long d, ulong endr);

/* Try all ways of allocating p^{x-1} at v_i for any p above the selected
 * -W limit.
 * If 'recover' is true, we initialize the state from act_recover, and
 * resume any partial walk_v() if have_rwalk.
 */
void walk_midp(t_node *prev_node, bool recover) {
    t_node *cur_node = &nodes[prev_node->level + 1];
    t_act *cur_act = &acts[prev_node->level + 1];

    uint vi, x, mi;
    ulong p;
    t_midpp *mp;
    bool used;

    cur_act->action = A_MIDP;
    midppc = 0;
    prep_midp(prev_node);
    if (midppc == 0)
        goto walk_midp_done;
    /* for reject_square() */
    ulong endr = square_endr(prev_node);

    level_setp(cur_act, midpp[0].maxp);
    /* setp has set to a prime <= target */
    prime_iterator_next(&cur_act->piter);

    if (recover && act_recover.action == A_MIDP) {
        p = act_recover.p;
        x = act_recover.x;
        vi = act_recover.vi;
        act_recover.action = A_NONE;

        level_setp(cur_act, p);
        for (mi = 0 ; mi < midppc; ++mi) {
            mp = &midpp[mi];
            if (mp->vi != vi || mp->x != x)
                continue;
            /* This is the (p,x,vi) tuple we were working on, we now
             * duplicate the tail of the main loop to continue the work.
             * The apply may fail again if progress showed it failing,
             * but not below a partial walk; the next diag point should
             * be what we recover to, so must not diag here if have_rwalk.
             */
            bool ok = apply_single(prev_node, cur_node, vi, p, x);
            /* the stack is now rebuilt */
            if (have_pend202) {
                apply_pend202();
                if (ok && mpz_cmp(cur_node->rq, zmax) > 0) {
                    /* it no longer fits, so there is nothing to walk */
                    --cur_vlevel[vi];
                    have_rwalk = 0;
                    ok = 0;
                }
            }
            if (ok) {
                if (need_work && !have_rwalk)
                    diag_plain(cur_node);
                walk_v(cur_node, have_rwalk ? rwalk_from : Z(zero));
                --cur_vlevel[vi];   /* unallocate */
            } else if (have_rwalk)
                fail("midp recovery: could not reapply %lu^%u at v_%u",
                        p, x, vi);
            /* we were working on p, so it is not already allocated */
            used = 0;
            goto next_mi;
        }
        fail("midp recovery x=%u vi=%u invalid", x, vi);
    }

    while (midppc) {
        p = prime_iterator_prev(&cur_act->piter);

        /* If p is already allocated must still prune any completed powers,
         * skipping only the apply.
         */
        used = known_prime(prev_node, p);
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
            if (used)
                continue;
            vi = mp->vi;
            x = mp->x;
            if (endr && x == 3 && vi != sq0 && reject_square(p,
                    (long)TYPE_OFFSET(sq0) - (long)TYPE_OFFSET(vi), endr)) {
                /* as apply_single() would leave it, for the progress line */
                cur_act->vi = vi;
                cur_act->p = p;
                cur_act->x = x;
                if (need_work)
                    diag_attempt(cur_node, vi, p, x);
                continue;
            }
            if (apply_single(prev_node, cur_node, vi, p, x)) {
                if (need_work)
                    diag_plain(cur_node);
                walk_v(cur_node, Z(zero));
                --cur_vlevel[vi];   /* unallocate */
            } else if (need_work)
                diag_attempt(cur_node, vi, p, x);
          next_mi:
            ;
        }
    }
  walk_midp_done:
    cur_act->action = A_UNFORCED;
}

uint relative_valuation(uint i, ulong p, uint e) {
    uint re = simple_valuation(TYPE_OFFSET(i), p);
    if (re < e)
        return re;
    return e;
}

/* Unapply a fully or partially applied batch by decrementing the
 * relevant vlevels. 'count' should be k for a fully applied batch.
 */
static inline void unapply_batch(uint fpi, uint bi, uint count) {
    t_forcebatch *bp = forcebatch_p(&forcep[fpi], bi);
    if (bp->x[bp->primary] == 0)
        return;
    for (uint vj = 0; vj < count; ++vj)
        if (bp->x[vj] != 0)
            --cur_vlevel[vj];
}

/* Whether to walk np now as a Pell case, two or more squares being fixed:
 * as soon as they are, except that under -jp a batch waits until it is
 * counted (see process_batch()).
 */
static inline bool pell_now(t_node *np, bool counted) {
    return np->have_square > 1 && (counted || !defer_pell);
}

/* Apply this batch and return TRUE if there is work to do for it, else
 * change nothing and return FALSE.
 */
bool apply_batch(
    t_node *prev_node, t_node *cur_node, uint fpi, uint bi
) {
    t_forcep *fp = &forcep[fpi];
    assert(fp->count > bi);
    t_value *vp;
    t_act *cur_act = &acts[cur_node->level];
    cur_act->action = A_FORCED;
    cur_act->bi = bi;
    t_forcebatch *bp = forcebatch_p(fp, bi);
    uint terminal = k;
    uint vi = bp->primary;

    if (bp->x[vi] == 0) {
        apply_null(prev_node, cur_node, fp->p);
        cur_node->fp_need &= ~(1U << fpi);
        return 1;
    }
    cur_node->have_min = prev_node->have_min;

    uint ep = bp->x[vi] - 1;
    if (!apply_primary(prev_node, cur_node, vi, fp->p, ep + 1, bp->fold))
        return 0;
    vp = &value[vi];
    if (vp->alloc[ cur_vlevel[vi] - 1 ].t == 1)
        terminal = vi;

    for (uint vj = 0; vj < k; ++vj) {
        if (vi == vj || bp->x[vj] == 0)
            continue;
        if (!apply_secondary(prev_node, cur_node, vj, fp->p, bp->x[vj])) {
            unapply_batch(fpi, bi, vj);
            if (vi > vj)
                --cur_vlevel[vi];
            return 0;
        }
        vp = &value[vj];
        if (vp->alloc[ cur_vlevel[vj] - 1 ].t == 1)
            terminal = vj;
    }
    cur_node->fp_need &= ~(1U << fpi);

    if (terminal < k && !(opt_alloc & 4)) {
        /* we have a value fully allocated, so test it unless we are
         * in a mode only to report batches.
         */
        bool valid = 1;
        if (mpz_sgn(zmin)) {
            vp = &value[terminal];
            uint vlevel = cur_vlevel[terminal];
            mpz_sub_ui(Z(temp), vp->alloc[vlevel - 1].q, terminal);
            if (mpz_cmp(Z(temp), zmin) <= 0)
                valid = 0;
        }
        if (valid) {
            walk_1(cur_node, terminal);
            if (seen_best)
                seen_valid = 1;
        }
        /* nothing more to do */
        unapply_batch(fpi, bi, k);
        return 0;
    }

    /* did we already have a square? */
    if (prev_node->have_square) {
        /* Need extra care only when a secondary hits the square,
         * so not if a) the primary hits it, or b) nothing hits it.
         */
        if (vi == sq0 || bp->x[sq0] == 0) {
            mpz_ui_pow_ui(px, fp->p, ep);
            if (!update_residues(
                prev_node, cur_node, vi, fp->p, ep + 1, px, 0, bp->fold
            )) {
                unapply_batch(fpi, bi, k);
                return 0;
            }
        } else {
            /* apply the secondary first, then the primary */
            uint eq = bp->x[sq0] - 1;
            uint e2 = ep - eq;
            /* a square with the primary's power has a fold of its own */
            uint fold = 0;
            if (e2 == 0 && bp->fold) {
                ulong d = TYPE_OFFSET(sq0 - vi);
                for (uint e = 0; e < ep; ++e)
                    d /= fp->p;
                fold = (bp->fold + d) % fp->p;
            }
            mpz_ui_pow_ui(px, fp->p, eq);
            if (!update_residues(
                prev_node, cur_node, sq0, fp->p, eq + 1, px, 0, fold
            )) {
                unapply_batch(fpi, bi, k);
                return 0;
            }
            if (e2 > 0) {
                mpz_ui_pow_ui(px, fp->p, e2);
                if (!update_residues(
                    prev_node, cur_node, vi, fp->p, e2 + 1, px, eq,
                    bp->fold
                )) {
                    unapply_batch(fpi, bi, k);
                    return 0;
                }
            }
        }
    }
    if (!(opt_alloc & 4) && pell_now(cur_node, 0)) {
        seen_valid = 1;
        walk_v(cur_node, Z(zero));
        unapply_batch(fpi, bi, k);
        return 0;
    }
    /* under -a4, a value fully allocated ends the batch: list it now */
    if (terminal < k)
        cur_node->fp_need = 0;
    return 1;
}

/* A batch is complete at np: under -W it is to be swept above the -W
 * threshold, which then caps the allocations below it. Under -k it is
 * also swept for the odd powers -k tries, with no cap below unless -W
 * gives one. Returns TRUE if it is to be swept.
 */
static inline bool sweep_batch(t_node *np) {
    kern_state(np);
    if (need_midp) {
        np->cap = maxp;
        return 1;
    }
    return kern_batch();
}
/* What follows any sweep of the batch complete at np: returns TRUE if
 * the allocation of unforced primes goes on below np, else FALSE, under
 * -WW or once a Pell walk has covered everything below np.
 */
static inline bool after_sweep(t_node *np) {
    if (midp_only)
        return 0;
    if (pell_now(np, 1)) {
        seen_valid = 1;
        walk_v(np, Z(zero));
        return 0;
    }
    return 1;
}

/* A complete set of forced primes has been allocated, or under -a4 a
 * set cut short by a value fully allocated. We may process
 * this batch or skip it, according to batch options; we also handle
 * midp ("-W") here, and skip the rest (i.e. allocation of unforced
 * primes) if midp_only. Returns FALSE if there is nothing more to
 * do for this batch, TRUE if the program should continue with standard
 * allocation of unforced primes, and terminates via longjmp() if we've
 * completed a requested subset of batches.
 * 'recover' is set when recovery resumes at a batch that the log has
 * already counted: it is processed afresh, but not counted again.
 */
bool process_batch(t_node *cur_node, bool recover) {
    if (!recover) {
        slong batch_id = batch_alloc++;
        cur_batch_level = cur_node->level;
        seen_valid = 1;
        if (debugB)
            disp_batch();
        if (opt_alloc) {
            /* check if this is a batch we want to process */
            if ((opt_alloc & 4) == 0
                && opt_batch_min >= 0
                && batch_id >= opt_batch_min
            ) {
                /* past the last batch we want: stop */
                if (batch_id > opt_batch_max)
                    longjmp(jmp_finish, 1);
                /* show it, with the time taken to reach it */
                if (!debugB)
                    disp_batch();
                goto do_process;
            }
            if (opt_batch_min < 0)
                disp_batch();
            return 0;
        }
    }
  do_process:
    if (sweep_batch(cur_node))
        walk_midp(cur_node, 0);
    return after_sweep(cur_node);
}

/* Whether allocations at cur_act's level are capped (see t_node.cap). */
static inline bool is_capped(t_act *cur_act) {
    return nodes[cur_act->level - 1].cap != NULL;
}

uint best_v(t_act *cur_act);

/* Choose that v_i with the highest t_i still to fulfil, or (on equality)
 * with the highest q_i, but having at least one factor to allocate.
 * If there is no best entry, returns BV_WALK.
 */
uint best_v0(t_act *cur_act) {
    bool capped = is_capped(cur_act);
    uint vi, ti = 0;
    mpz_t *qi;

    assume(k > 0);
    for (uint vj = 0; vj < k; ++vj) {
        t_value *vpj = &value[vj];
        uint vjl = cur_vlevel[vj];
        t_allocation *apj = &vpj->alloc[vjl - 1];
        uint tj = apj->t;
        mpz_t *qj = &apj->q;

        /* skip if no odd prime factor */
        if (divisors[tj].high <= (kern_highpow() ? 1 : 2))
            continue;
        /* skip prime powers when capped, and any square under -k */
        if ((tj & 1) && (kern_batch()
                || (capped && divisors[tj].alldiv == 2)))
            continue;
        if (kern_passed(vj))
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
    return ti ? vi : BV_WALK;
}

/* Choose that v_i with the highest prime dividing t_i still to fulfil,
 * or on equality with the highest t_i, or on equality with the highest
 * q_i.
 * If there is no best entry, returns BV_WALK.
 */
uint best_v1(t_act *cur_act) {
    bool capped = is_capped(cur_act);
    uint vi, ti = 0;
    mpz_t *qi;

    assume(k > 0);
    for (uint vj = 0; vj < k; ++vj) {
        t_value *vpj = &value[vj];
        uint vjl = cur_vlevel[vj];
        t_allocation *apj = &vpj->alloc[vjl - 1];
        uint tj = apj->t;
        mpz_t *qj = &apj->q;

        /* skip if no odd prime factor */
        if (divisors[tj].high <= (kern_highpow() ? 1 : 2))
            continue;
        /* skip prime powers when capped, and any square under -k */
        if ((tj & 1) && (kern_batch()
                || (capped && divisors[tj].alldiv == 2)))
            continue;
        if (kern_passed(vj))
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
    return ti ? vi : BV_WALK;
}

/* Choose that v_i with the lowest t_i still to fulfil, or (on equality)
 * with the highest q_i, but having at least one factor to allocate.
 * If there is no best entry, returns BV_WALK.
 */
uint best_v2(t_act *cur_act) {
    bool capped = is_capped(cur_act);
    uint vi, ti = 0;
    mpz_t *qi;

    assume(k > 0);
    for (uint vj = 0; vj < k; ++vj) {
        t_value *vpj = &value[vj];
        uint vjl = cur_vlevel[vj];
        t_allocation *apj = &vpj->alloc[vjl - 1];
        uint tj = apj->t;
        mpz_t *qj = &apj->q;

        /* skip if no odd prime factor */
        if (divisors[tj].high <= (kern_highpow() ? 1 : 2))
            continue;
        /* skip prime powers when capped, and any square under -k */
        if ((tj & 1) && (kern_batch()
                || (capped && divisors[tj].alldiv == 2)))
            continue;
        if (kern_passed(vj))
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
    return ti ? vi : BV_WALK;
}

/* Same as best_v0, except that if the last power allocated on some v_i
 * was the square root of the remaining tau (and unforced), always take it.
 */
uint best_v3(t_act *cur_act) {
    bool capped = is_capped(cur_act);
    uint vi, ti = 0;
    mpz_t *qi;

    assume(k > 0);
    for (uint vj = 0; vj < k; ++vj) {
        t_value *vpj = &value[vj];
        uint vjl = cur_vlevel[vj];
        t_allocation *apj = &vpj->alloc[vjl - 1];
        uint tj = apj->t;
        mpz_t *qj = &apj->q;

        /* skip if no odd prime factor */
        if (divisors[tj].high <= (kern_highpow() ? 1 : 2))
            continue;
        /* skip prime powers when capped, and any square under -k */
        if ((tj & 1) && (kern_batch()
                || (capped && divisors[tj].alldiv == 2)))
            continue;
        if (kern_passed(vj))
            continue;
        /* shortcircuit if single allocation of (even) sqrt(n) */
        if ((tj & 1) == 0 && apj->x == apj->t) {
            /* shortcircuit if last allocation was of sqrt(t) */
            /* but only if it was unforced */
            ulong p = apj->p;
            for (uint li = final_level + 1; li < cur_act->level; ++li) {
                t_act *actp = &acts[li];
                if (actp->action == A_UNFORCED)
                    break;
                if (actp->p == p)
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
    return ti ? vi : BV_WALK;
}

/* Choose that v_i with the highest prime dividing t_i still to fulfil,
 * or on equality with the highest t_i, or on equality with the highest
 * q_i. If all qualifying t_i are a power of 2, instead choose the one
 * with the smallest range.
 * If there is no best entry, returns BV_WALK.
 */
uint best_v4(t_act *cur_act) {
    bool capped = is_capped(cur_act);
    uint vi, ti = 0, hi;
    ulong mini;
    mpz_t *qi, *limi;

    assume(k > 0);
    for (uint vj = 0; vj < k; ++vj) {
        t_value *vpj = &value[vj];
        uint vjl = cur_vlevel[vj];
        t_allocation *apj = &vpj->alloc[vjl - 1];
        uint tj = apj->t;
        mpz_t *qj = &apj->q;
        mpz_t *limj = &apj->lim;
        ulong minj;

        /* skip if no odd prime factor */
        if (divisors[tj].high <= (kern_highpow() ? 1 : 2))
            continue;
        /* skip prime powers when capped, and any square under -k */
        if ((tj & 1) && (kern_batch()
                || (capped && divisors[tj].alldiv == 2)))
            continue;
        if (kern_passed(vj))
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
                    minj = ispow2_u64(apj->x) ? apj->p : maxforce[vj];
                    if (mini > minj)
                        mpz_sub_ui(Z(temp), *limi, mini - minj);
                    else
                        mpz_add_ui(Z(temp), *limi, minj - mini);
                    if (mpz_cmp(Z(temp), *limj) <= 0)
                        continue;
                }
            }
        } else if (hj == 2) {
            minj = ispow2_u64(apj->x) ? apj->p : maxforce[vj];
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
    return ti ? vi : BV_WALK;
}

/* Show the candidate walk_6x() is about to try: the prime Z(j4p), from
 * the subset a of the allocations at its position.
 */
void diag_6x(t_act *cur_act, uint a) {
    cur_act->bi = a;   /* spare at an unforced level */
    diag_plain(&nodes[cur_act->level]);
}

uint suffix_6x(t_act *cur_act, char *buf) {
    return gmp_sprintf(buf, " 6X(%Zu,%u,%u)", Z(j4p), cur_act->vi, cur_act->bi);
}

char *parse_6x(char *s) {
    int pend = 0;
    sscanf(s, "%*[0-9]%n", &pend);
    if (pend == 0)
        fail("514 could not parse 6X(...) recovery prime: '%s'", s);
    /* skip the prime, it is not needed for recovery */
    s += pend;
    if (s[0] != ',')
        fail("515 unexpected character in 6X(...) recovery");
    ++s;
    act_recover.vi = strtoul(s, &s, 10);
    if (s[0] != ',')
        fail("515 unexpected character in 6X(...) recovery");
    ++s;
    act_recover.a = strtoul(s, &s, 10);
    if (s[0] != ')')
        fail("515 unexpected character in 6X(...) recovery");
    return s + 1;
}

ulong limit_p(t_act *cur_act, uint vi, uint x, uint nextt);

/* The limit of the loop at v_i for its first x, the highest prime of
 * tau: that dominates the primes recursion there would try, the later x
 * needing at least a (2h-1)th root. A limit of 2^64 or more (0 from
 * limit_p(), forcing a walk) is given as ULONG_MAX.
 */
ulong loop_limit(t_act *cur_act, uint vi) {
    t_value *vp = &value[vi];
    uint t = vp->alloc[cur_vlevel[vi] - 1].t;
    uint x = divisors[t].div[0];
    ulong limp = limit_p(cur_act, vi, x, t / x);
    return limp ? limp : ULONG_MAX;
}

/* STRATEGY_6X: if we have the pattern "...2^e . 2z^2...", allocating 2^e
 * at v_i and 2 or 2y^2 at v_{i+2} leaving an odd square, v_i must be of
 * the form 2(z-1)(z+1), which is very restrictive (and requires e >= 4,
 * forced by the quadratic residue check).
 *
 * We force allocation at v_i until the remaining tau is odd (in which
 * case we can finish with a Pell walk) or 2, in which case we return
 * BV_6X to invoke the fast walk_6x().
 *
 * But until tau at v_i is 2, we take instead the position prev_strategy
 * would choose if its loop has a lower limit: our loop of q^2 at v_i
 * runs to about (zmax/8)^{1/4} whatever n is, while a high power
 * elsewhere may have a far lower limit (e.g. p^28 for n = 174). The
 * choice depends on zmax, see updated_zmax().
 */
uint best_6x(t_act *cur_act) {
    /* check if conditions for STRATEGY_6X still hold */
    t_node *prev_node = &nodes[cur_act->level - 1];
    if (!prev_node->have_square || sq0 < 2) {
        strategy = prev_strategy;
        return best_v(cur_act);
    }

    uint vi = sq0 - 2;
    t_value *vp = &value[vi];
    uint vlevel = cur_vlevel[vi];
    uint t = vp->alloc[vlevel - 1].t;
    /* odd t makes v_i a second square: Pell case, walk will be fast;
     * prep_midp() relies on us not allocating here when t is an odd prime */
    if (t & 1)
        return BV_WALK;
    if (t != 2) {
        uint vj = strategies[prev_strategy](cur_act);
        if (vj < BV_SPECIAL && vj != vi
                && loop_limit(cur_act, vj) < loop_limit(cur_act, vi))
            return vj;
        return vi;          /* allocate some more */
    }
    return BV_6X;           /* walk_6x() can now handle this */
}

/* STRATEGY_6X: we have t_i = 2, t_{i+2} odd, such that v_{i+2} must be of
 * the form 2z^2 (z odd) and v_i must be of the form 16abp (p as yet
 * unallocated) with 8abp = (z-1)(z+1) so a = bp +/- 1.
 * Thus from here the only solutions possible involve a pair of coprime
 * factors ab that yield a prime p for the unallocated part: we generate
 * all such coprime pairs for testing, and invoke walk_1() for each
 * resulting p that is prime.
 */
void walk_6x(void) {
    t_node *cur_node = &nodes[level];
    t_node *prev_node = &nodes[level - 1];
    t_act *cur_act = &acts[level];
    assert(sq0 >= 2);
    uint vi = sq0 - 2;
    t_value *vp = &value[vi];
    uint vlevel = cur_vlevel[vi];
    t_allocation *ap;
    t_allocation *ap_last = &vp->alloc[vlevel - 1];
    t_allocation *ap_next = &vp->alloc[vlevel];
    ap_next->t = 1;
    ap_next->p = 0; /* the real value may well not fit */
    ap_next->x = 2;
    ap_next->level = level;
    cur_vlevel[vi] = vlevel + 1;
    cur_node->have_min = 1;
    cur_act->vi = vi;
    cur_act->action = A_6X;
    /* We will fully fix v_i, so we don't need to roll the prime we
     * allocate into rq/aq by calling update_chinese each time: the
     * previous values tell us everything we need to know.
     */
    mpz_set(cur_node->aq, prev_node->aq);
    mpz_set(cur_node->rq, prev_node->rq);

    /* We need prime p: v_i = 8abp with a = bp +/- 1.
     * We find that by iterating 'a' over all combinations of the prime power
     * allocations (excluding the constant factor 8).
     */
    /* find the actual power of 2 allocated */
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
    /* take out the constant factor */
    mpz_fdiv_q_2exp(Z(j4q), ap_last->q, 3);

    /* Iterate j4a over all combinations of the prime power allocations
     * via a bit vector of which allocations to include. (We don't need
     * to check 0 case of the vector, since it gives j4a = 1.)
     * Maybe TODO: a simple (vlevel - 2)-deep recursion would save
     * duplicate multiplications here, worth considering when we start
     * dealing with higher values of n.
     */
    if (vlevel > sizeof(uint) * 8 - 1)
        fail("FIXME: too many factors for STRATEGY_6X");
    uint a_start = (1U << vlevel) - 2;
    if (act_recover.action == A_6X) {
        /* on recover, skip to the bit-vector value that was in progress */
        if (act_recover.vi != vi)
            fail("panic: STRATEGY_6X recovery wants vi=%u, but we have vi=%u",
                    act_recover.vi, vi);
        if (act_recover.a & 1)
            fail("panic: STRATEGY_6X recovery has invalid bit-vector %u",
                    act_recover.a);
        a_start = act_recover.a;
        act_recover.action = A_NONE;        /* consumed */
    }
    for (uint a = a_start; a; a -= 2) {
        mpz_set_ui(Z(j4a), 1);
        for (uint i = 1; i < vlevel; ++i) {
            if ((a & (1U << i)) == 0)
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
        /* CHECKME: we want a > b, would it be a saving to compare
         * against sqrt(q) in the loop instead? Probably yes: since
         * we need a ~ bp, we could actually compare against something
         * like sqrt(q p_m) where p_m is the least unallocated prime.
         */
        if (mpz_cmp(Z(j4a), Z(j4b)) < 0)
            continue;
        mpz_sub_ui(Z(temp), Z(j4a), 1);
        mpz_fdiv_qr(Z(j4p), Z(j4m), Z(temp), Z(j4b));
        if (mpz_cmp_ui(Z(j4m), 2) <= 0) {
            if (_GMP_is_prob_prime(Z(j4p))) {
                /* p = Z(j4p) is prime and yields v_{i+2} = 2z^2 */
                mpz_mul(ap_next->q, ap_last->q, Z(j4p));
                if (need_work)
                    diag_6x(cur_act, a);
                walk_1(cur_node, vi);
            }
            if (mpz_cmp_ui(Z(j4b), 2) <= 0) {
                mpz_add_ui(Z(j4p), Z(j4p), 2 / mpz_get_ui(Z(j4b)));
                if (_GMP_is_prob_prime(Z(j4p))) {
                    mpz_mul(ap_next->q, ap_last->q, Z(j4p));
                    if (need_work)
                        diag_6x(cur_act, a);
                    walk_1(cur_node, vi);
                }
            }
        }
    }
    cur_vlevel[vi] = vlevel;    /* restore */
    cur_act->action = A_UNFORCED;
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
uint best_fixed(t_act *cur_act) {
    uint effective_level = cur_act->level - (cur_batch_level + 1);
    if (effective_level >= fixed_level)
        return BV_WALK;
    uint vi = fixed_v[effective_level];
    t_value *vp = &value[vi];
    uint vlevel = cur_vlevel[vi];
    t_allocation *ap_last = &vp->alloc[vlevel - 1];
    uint t = ap_last->t;
    if (t == 1)
        return BV_WALK;
    /* skip prime powers when capped, and any square under -k (invariant) */
    if ((t & 1) && (kern_batch()
            || (is_capped(cur_act) && divisors[t].alldiv == 2)))
        return BV_WALK;
    /* nor a -k position with only its odd power to come, or passed over */
    if ((t == 2 && kern_at(vi)) || kern_passed(vi))
        return BV_WALK;
    return vi;
}

/* Find the best entry to allocate to next, using the selected strategy.
 * If there is no such entry, returns BV_WALK; if there is no work to
 * do for this x, returns BV_NEXTX.
 */
uint best_v(t_act *cur_act) {
    return strategies[strategy](cur_act);
}

/* Decide what the act at a new level is to do: the batches of the next
 * forced prime if there are any, else an unforced loop at the position
 * best_v() chooses, unless a walk or other search covers all below this
 * point instead. Sets cur_act->vi for CH_UNFORCED.
 * The gate and the flip are decided per x as the unforced loop runs,
 * see prep_unforced_x().
 */
static inline e_choice choose_action(t_act *cur_act) {
    t_node *prev_node = &nodes[cur_act->level - 1];
    t_act *prev_act = &acts[cur_act->level - 1];
    if (prev_node->fp_need && prev_act->action != A_UNFORCED
            && forcep[next_fpi(prev_node)].count)
        return CH_FORCED;
    if (cur_act->next_best)
        return CH_WALK;
    uint vi = best_v(cur_act);
    cur_act->choice_strategy = strategy;
    cur_act->unsorted = 0;
    if (vi < BV_SPECIAL) {
        cur_act->vi = vi;
        return CH_UNFORCED;
    }
    switch (vi - BV_SPECIAL) {
      case BV_6X - BV_SPECIAL:
        return CH_6X;
      case BV_NEXTX - BV_SPECIAL:
        return CH_NOTHING;
      case BV_WALK - BV_SPECIAL:
        /* failure result is stable if last allocation unforced */
        if (prev_act->action == A_UNFORCED)
            cur_act->next_best = 1;
        return CH_WALK;
    }
    fail("panic: unknown best_v() result %u (k=%u)", vi, k);
}

/* Returns the greatest p for which p^{x-1} needs to be tried at v_i
 * leaving remaining tau nextt: 1 signifies no primes, 0 that the answer
 * is 2^64 or more.
 * A lower zmax never gives a higher result, all else being equal, with 0
 * counted as greater than any other: recurse() relies on this when it
 * recalculates a limit.
 */
ulong limit_p(t_act *cur_act, uint vi, uint x, uint nextt) {
    t_value *vp = &value[vi];
    uint vil = cur_vlevel[vi];
    t_allocation *ap = &vp->alloc[vil - 1];
    mpz_add_ui(Z(lp_x), zmax, TYPE_OFFSET(vi));
    mpz_div(Z(lp_x), Z(lp_x), ap->q);

    if (ispow2_u64(x)) {
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
    } else if (strategy == STRATEGY_6X && nextt == 2 && vi + 2 == sq0) {
        /* v_i = q_i p^{x-1} r => q_i p^{x-1} = 8ab such that br = a +/- 1.
         * When p^{x-1} dominates, we minimize v_i by setting a = p^{x-1}
         * giving r >= 8(p^{x-1} - 1)/q_i so v_i >= 8 p^{x-1} (p^{x-1} - 1).
         * We can therefore constrain p : p < 1 + (zmax / 8)^{1 / (2(x-1))}.
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
        t_node *prev_node = &nodes[cur_act->level - 1];
        /* this is mintau using hb: b > a */
        mintau_restricted_at(prev_node, Z(lp_mint), nextt, x, vi);
        bool have_value = 0;
        if (mpz_sgn(Z(lp_mint))) {
            have_value = 1;
            mpz_div(Z(lp_mint), Z(lp_x), Z(lp_mint));
        }
        uint itert = nextt, iter = 1;
        while ((itert % x) == 0) {
            ++iter;
            itert /= x;
            mintau_restricted_at(prev_node, Z(lp_mint2), itert, x, vi);
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
            t_node *prev_node = &nodes[cur_act->level - 1];
            mintau_at(prev_node, Z(lp_mint), nextt, vi);
            mpz_div(Z(lp_x), Z(lp_x), Z(lp_mint));
        }
        mpz_root(Z(lp_x), Z(lp_x), x - 1);
    }

    ulong *cap = nodes[cur_act->level - 1].cap;
    if (cap && cap[x - 1] && mpz_cmp_ui(Z(lp_x), cap[x - 1]) > 0)
        return cap[x - 1];
    if (!mpz_fits_ulong_p(Z(lp_x)))
        return 0;
    if (mpz_sgn(Z(lp_x)) <= 0)
        return 1;
    return mpz_get_ui(Z(lp_x));
}

/* The x of the previous allocation at v_i if it was unforced, else 0. */
static inline uint prev_x(uint vi) {
    t_allocation *ap = &value[vi].alloc[cur_vlevel[vi] - 1];
    return (ap->p > maxforce[vi] && !never_unforced(ap->p)) ? ap->x : 0;
}

/* Returns true if a fresh x at v_i (leaving nextt) can be skipped, because
 * the same powers taken in the other order have already covered it.
 */
static inline bool done_in_reverse(uint vi, uint x, uint nextt) {
    uint prevx = prev_x(vi);
    if (ispow2_u64(x) || x == prevx)
        return 0;
    /* we already did this in reverse */
    if (x < prevx && divisors[x].high == divisors[prevx].high)
        return 1;
    /* we already did any possible continuation in reverse */
    return x > nextt && divisors[x].high == divisors[nextt].high;
}

/* The prime after which to start a fresh x at v_i. */
static inline ulong start_p(uint vi, uint x) {
    t_allocation *ap = &value[vi].alloc[cur_vlevel[vi] - 1];
    uint prevx = prev_x(vi);
    /* powers of 2: increasing p, not decreasing powers */
    if (ispow2_u64(x) ? (prevx && ispow2_u64(prevx)) : (x == prevx))
        return ap->p;   /* skip smaller p */
    return maxforce[vi];
}

/* True if run_flip_pqsq() can take over from p^{x-1} at a v_i left with
 * tau 2z: that relies on z and 2z being the only powers still to try there,
 * every smaller one having been done in reverse (see done_in_reverse()).
 * z does not need to be prime. Powers of 2 are instead tried in order
 * of p, whatever the power, so they do not qualify.
 */
static inline bool can_flip(uint x) {
    return !ispow2_u64(x);
}

/* If t is of the form 2x^2 for an x that can_flip(), returns x, else
 * returns 0.
 */
static inline uint flip_xs_tau(uint t) {
    uint x = (t & 1) ? 0 : divisors[t / 2].sqrt;
    return (x && can_flip(x)) ? x : 0;
}

/* Make cur_act, holding p^{z-1} at its v_i, the act of a flip that replaces
 * that allocation, so with it withdrawn (see run_flip_pqsq()).
 */
static inline void flip_withdraw(t_act *cur_act) {
    cur_act->action = A_FLIP;
    cur_act->limp = cur_act->p;   /* it will see this x is complete on return */
    --cur_vlevel[cur_act->vi];
}

/* Most primes tried by a loop of allocations are rejected for giving a
 * least v_0 = rq + mult.aq > zmax, with mult the multiple the CRT finds:
 * that is, for mult > floor((zmax - rq) / aq), which is the same for
 * every prime of the loop. So where that bound (rj_mult) fits in a limb,
 * a prime can be rejected on mult alone, calculated in single limbs,
 * without the cost of apply_single(). As zmax can only fall, the bound
 * found when the loop is prepared stays valid, if no longer the least.
 */
static inline void reject_prep(t_node *prev, t_act *cur_act) {
    cur_act->rj_ok = 0;
#ifdef CHECK_OVERFLOW
    if (mpz_cmp(prev->rq, zmax) > 0)
        return;
    mpz_sub(Z(temp), zmax, prev->rq);
    mpz_fdiv_q(Z(temp), Z(temp), prev->aq);
    if (!mpz_fits_ulong_p(Z(temp)))
        return;
    cur_act->rj_mult = mpz_get_ui(Z(temp));
    /* rq < aq, so rq fits in a limb if aq does */
    cur_act->rj_limb = (mpz_size(prev->aq) == 1);
    cur_act->rj_ok = 1;
#endif
}

/* The greatest root z of a fixed square v_j = q.z^2 within zmax, given
 * exactly one fixed and that a square; else 0, or if it would not fit.
 */
static ulong square_endr(t_node *np) {
    if (np->have_square != 1)
        return 0;
    uint sql = cur_vlevel[sq0];
    if (sqg[sql - 1] != 2)
        return 0;
    mpz_add_ui(Z(temp), zmax, TYPE_OFFSET(sq0));
    mpz_fdiv_q(Z(temp), Z(temp), value[sq0].alloc[sql - 1].q);
    mpz_sqrt(Z(temp), Z(temp));
    return mpz_fits_ulong_p(Z(temp)) ? mpz_get_ui(Z(temp)) : 0;
}

/* prepare for reject_square() on a loop of p^{x-1} at v_i below prev */
static inline void reject_prep_square(
    t_node *prev, t_act *cur, uint vi, uint x
) {
    cur->rs_ok = 0;
    if (x != 3 || vi == sq0)
        return;
    cur->rs_endr = square_endr(prev);
    if (!cur->rs_endr)
        return;
    cur->rs_d = (long)TYPE_OFFSET(sq0) - (long)TYPE_OFFSET(vi);
    cur->rs_ok = 1;
}

/* a square root of the quadratic residue a mod an odd prime p */
static inline ulong sqrtmod_u64(ulong a, ulong p) {
    if ((p & 3) == 3)
        return powmod_u64(a, (p + 1) >> 2, p);
    /* Tonelli-Shanks */
    ulong q = p - 1, n = 2;
    uint s = trailing_zeroes_u64(q);
    q >>= s;
    while (jacobi_u64(n, p) != -1)
        ++n;
    ulong c = powmod_u64(n, q, p);
    ulong r = powmod_u64(a, (q + 1) >> 1, p);
    ulong t = powmod_u64(a, q, p);
    while (t != 1) {
        uint i = 0;
        for (ulong u = t; u != 1; u = mulmod_u64(u, u, p))
            ++i;
        ulong b = c;
        for (uint j = i + 1; j < s; ++j)
            b = mulmod_u64(b, b, p);
        r = mulmod_u64(r, b, p);
        c = mulmod_u64(b, b, p);
        t = mulmod_u64(t, c, p);
        s = i;
    }
    return r;
}

/* True if allocating p^2 at a position d places before the fixed square
 * v_j = q.z^2 is sure to be rejected for having no root z up to endr; if
 * false, it may still be. We need q.z^2 == d (mod p^2). Half the primes
 * fail that mod p, which the Jacobi symbol shows without extending the
 * residues of z to p. Of the rest, once p^2 > endr at most the two roots
 * +-z mod p^2 can be in range, and usually neither is: one root mod p,
 * lifted to p^2, shows that. Only what is left need have the residues
 * extended.
 */
static inline bool reject_square(ulong p, long d, ulong endr) {
    if (!(p & 1))
        return 0;
    mpz_t *q = &value[sq0].alloc[cur_vlevel[sq0] - 1].q;
    ulong qm = mpz_fdiv_ui(*q, p);
    ulong dm = (d < 0) ? (ulong)(-d) % p : (ulong)d % p;
    if (qm == 0 || dm == 0)
        return 0;
    if (d < 0)
        dm = p - dm;
    if (jacobi_u64(mulmod_u64(dm, qm, p), p) != 1)
        return 1;
    if (p <= endr / p)
        return 0;
#ifdef HAVE_UINT128
    /* z == s (mod p) */
    ulong s = sqrtmod_u64(mulmod_u64(dm, invert_u64(qm, p), p), p);
    /* z == s + p.t (mod p^2), with 2.q.s.t == (d - q.s^2) / p (mod p) */
    mpz_mul_ui(Z(temp), *q, s);
    mpz_mul_ui(Z(temp), Z(temp), s);
    if (d < 0)
        mpz_add_ui(Z(temp), Z(temp), (ulong)(-d));
    else
        mpz_sub_ui(Z(temp), Z(temp), (ulong)d);
    mpz_neg(Z(temp), Z(temp));
    mpz_divexact_ui(Z(temp), Z(temp), p);
    ulong u = mpz_fdiv_ui(Z(temp), p);
    ulong den = mulmod_u64(mulmod_u64(2, qm, p), s, p);
    ulong t = mulmod_u64(u, invert_u64(den, p), p);
    uint128 z = (uint128)p * t + s;
    return z > endr && (uint128)p * p - z > endr;
#else
    /* that needs 128 bits: without them, p is not rejected here */
    return 0;
#endif
}

/* aq and rq of prev, mod m */
static inline void reject_mod(
    t_node *prev, bool limb, ulong m, ulong *am, ulong *rm
) {
    if (limb) {
        *am = mpz_getlimbn(prev->aq, 0) % m;
        *rm = mpz_get_ui(prev->rq) % m;
    } else {
        *am = mpz_fdiv_ui(prev->aq, m);
        *rm = mpz_fdiv_ui(prev->rq, m);
    }
}

/* Returns true if allocating p^{x-1} at v_i over prev is sure to be
 * rejected for v_0 > zmax, or false if uncertain. The caller checks
 * that p is odd, and that reject_prep() set cur_act->rj_ok.
 * The CRT gives v_0 = rq + mult.aq, where 0 <= mult < p^{x-1} and
 *   mult == -(rq + i) / aq (mod p^{x-1}).
 * Taken mod p, that gives mult0 = mult % p from an inverse mod p alone;
 * mult >= mult0, so mult0 > rj_mult is enough to reject. Otherwise
 * we need more of mult: for p^2 its other digit base p comes from the
 * same inverse, and for higher powers we invert mod m = p^e, the
 * largest power of p up to p^{x-1} below 2^61: mult >= mult % m, so
 * that too is enough to reject if above rj_mult, and it is mult itself
 * if m = p^{x-1}.
 */
static inline bool reject_single(
    t_node *prev, t_act *cur_act, uint vi, ulong p, uint x
) {
    ulong off = TYPE_OFFSET(vi), am, rm;
    if (p < (1UL << 31)) {
        reject_mod(prev, cur_act->rj_limb, p, &am, &rm);
        if (am == 0)
            return 0;
        ulong inv = invert_u32(am, p);
        /* -(i + rq) mod p */
        ulong c = ((off < p ? off : off % p) + rm) % p;
        if (c)
            c = p - c;
        ulong mult0 = c * inv % p;
        if (mult0 > cur_act->rj_mult)
            return 1;
        if (x == 2)
            return 0;
        if (x == 3) {
            /* aq.(mult0 + p.mult1) == c (mod p^2), so
             * mult1 == ((c - aq.mult0) / p) / aq (mod p).
             */
            ulong m = p * p;
            reject_mod(prev, cur_act->rj_limb, m, &am, &rm);
            c = (off % m + rm) % m;
            if (c)
                c = m - c;
            ulong d = c + m - mulmod_u64(am, mult0, m);
            if (d >= m)
                d -= m;
            return mult0 + p * (d / p * inv % p) > cur_act->rj_mult;
        }
    }
    /* as update_chinese(): m = p^e < 2^61 for e < x, not dividing aq */
    ulong m = p;
    for (uint e = 2; e < x; ++e) {
        if (m >= (1UL << 61) / p)
            break;
        m *= p;
    }
    if (m >= (1UL << 61) || m <= cur_act->rj_mult)
        return 0;
    reject_mod(prev, cur_act->rj_limb, m, &am, &rm);
    if (am % p == 0)
        return 0;
    ulong c = (off % m + rm) % m;
    if (c)
        c = m - c;
    return mulmod_u64(c, ppow_invert(am, p, m), m) > cur_act->rj_mult;
}

/* Act on the limit limp for p^{x-1} at cur_act, given the last prime
 * done p (the prime before the first to try, if fresh).
 *
 * Returns:
 *   PUX_NOTHING_TO_DO if nothing more to do at this level for any x;
 *   PUX_FLIP_PQSQ if this strategy is available now (see run_flip_pqsq());
 *   PUX_SKIP_THIS_X if nothing more to do for this x;
 *   PUX_DO_THIS_X if there are p to allocate.
 */
e_pux limit_unforced_x(
    t_node *prev_node, t_act *cur_act, ulong p, ulong limp, bool fresh
) {
    uint ti = cur_act->ti;
    uint x = divisors[ti].div[cur_act->di];
    uint vi = cur_act->vi;
    uint nextt = ti / x;

    /* under -k walk_midp() has tried every such power that can apply */
    if (!(x & 1) && kern_at(vi))
        return PUX_SKIP_THIS_X;
    if (limp == 0) {
        /* force walk */
#ifdef SQONLY
        if (prev_node->have_square)
            walk_v(prev_node, Z(zero));
#else
        walk_v(prev_node, Z(zero));
#endif
        return PUX_NOTHING_TO_DO;
    }
    if (limp < p) {
        /* If tau at the previous level is 2z^2 and its current prime is
         * already too high to split as (z, z, 2) then we can not only
         * skip this z but also profitably invert the process for the
         * remainder, splitting as (2z, z) rather than (z, 2z). That holds
         * for any z that can_flip(), prime or not, except where -k applies.
         */
        if (nextt == 2 && acts[prev_node->level].vi == vi && x == prev_x(vi)
                && can_flip(x) && !kern_at(vi))
            return PUX_FLIP_PQSQ;
        return PUX_SKIP_THIS_X; /* nothing to do here */
    }
    /* TODO: rather than diverting odd-prime-tau positions to a walk where
     * capped, consider handling them always via walk_1_set(), as the
     * uncapped search does. That would mean not applying the cap in
     * limit_p() when nextt == 1 with t prime (so walk_1_set() covers every p
     * itself, even under -W/-p), and removing the "skip prime powers when
     * capped" checks from best_v0() .. best_v4() and best_fixed();
     * prep_midp() skip would remain valid, and capped and uncapped runs
     * would then choose positions identically. Correctness should be
     * unaffected, but performance would change in both directions:
     * walk_1_set() does a CRT check for every prime up to (zmax/q)^{1/(t-1)},
     * while a square walk visits only the rc residue classes mod qq.
     * Note also that the nextt == 1 path in prep_unforced_x() is taken
     * before the gate, so walk_1_set() is never weighed against a walk.
     * Ideally the cost model would make that choice, as the gate does
     * for walk vs recurse.
     * This probably needs more progress on calibration before we consider it.
     */
    if (nextt == 1) {
        nodes[cur_act->level].have_min = prev_node->have_min;
        /* a recovered p is the one in progress, so still to try */
        walk_1_set(prev_node, cur_act, vi, fresh ? p : p - 1, limp, x);
        return PUX_SKIP_THIS_X;
    }
    return PUX_DO_THIS_X;
}

/* The gate: true if the gain heuristics say to walk prev_node, rather
 * than recurse by allocating at v_i each prime after p up to limp.
 */
bool gate_walk(t_node *prev_node, uint vi, ulong p, ulong limp) {
    mpz_add_ui(Z(r_walk), zmax, TYPE_OFFSET(vi));
#ifdef LARGE_MIN
    /* needs zmin <= zmax */
    mpz_sub(Z(r_walk), Z(r_walk), zmin);
#endif
    if (prev_node->have_square) {
        if (prev_node->have_square == 1) {
            /* Let rc be the number of residues. If we fix a square, we will
             * test rc of each a_q / q_i window up to (zmax / q_i)^{1/g};
             * that's a lot of operations, but it does not obviously simplify.
             */
            uint sql = cur_vlevel[sq0];
            uint g = sqg[sql - 1];
            t_value *vp = &value[sq0];
            t_allocation *ap = &vp->alloc[sql - 1];
            mpz_fdiv_q(Z(r_walk), Z(r_walk), ap->q);
            mpz_root(Z(r_walk), Z(r_walk), g);
            mpz_mul(Z(r_walk), Z(r_walk), ap->q);
            mpz_mul_ui(Z(r_walk), Z(r_walk),
                    res_array(prev_node->level)->count);
            mpz_fdiv_q(Z(r_walk), Z(r_walk), prev_node->aq);
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
        mpz_fdiv_q(Z(r_walk), Z(r_walk), prev_node->aq);
        if (gain > 1)
            mpz_mul_ui(Z(r_walk), Z(r_walk), gain);
        if (antigain > 1)
            mpz_fdiv_q_ui(Z(r_walk), Z(r_walk), antigain);
    }
    ulong cap = (limp_cap && limp_cap < limp) ? limp_cap : limp;
    return mpz_fits_ulong_p(Z(r_walk))
            && mpz_get_ui(Z(r_walk)) < ((cap < p) ? 0 : cap - p);
}

/* Set cur_act to allocate its current x for the primes after p up to limp. */
static inline void set_unforced_x(
    t_node *prev_node, t_act *cur_act, ulong p, ulong limp
) {
    uint x = divisors[cur_act->ti].div[cur_act->di];
    level_setp(cur_act, p);
    cur_act->x = x;
    cur_act->limp = limp;
    cur_act->max_at = seen_best;
    reject_prep(prev_node, cur_act);
    reject_prep_square(prev_node, cur_act, cur_act->vi, x);
    /* TODO: do some constant alloc stuff in advance */
}

/* Prepare to allocate p^{x-1} at v_i for a range of p, starting a fresh x.
 * This is the one place we choose between walking and recursing: once we
 * recurse here we stay committed to it, whatever the maximum does.
 *
 * Returns:
 *   PUX_NOTHING_TO_DO if nothing more to do at this level for any x;
 *   PUX_FLIP_PQSQ if this strategy is available now (see run_flip_pqsq());
 *   PUX_SKIP_THIS_X if nothing more to do for this x;
 *   PUX_DO_THIS_X if prepped for this x with work to do.
 */
e_pux prep_unforced_x(t_node *prev_node, t_act *cur_act) {
    uint ti = cur_act->ti;
    uint x = divisors[ti].div[cur_act->di];
    uint vi = cur_act->vi;
    uint nextt = ti / x;

    if (done_in_reverse(vi, x, nextt))
        return PUX_SKIP_THIS_X;
    ulong p = start_p(vi, x);

    /* try p^{x-1} for all p until q_i . p^{x-1} . minrest > zmax + i */
    ulong limp = limit_p(cur_act, vi, x, nextt);
    e_pux pux = limit_unforced_x(prev_node, cur_act, p, limp, 1);
    if (pux != PUX_DO_THIS_X)
        return pux;

    if (gate_walk(prev_node, vi, p, limp)) {
#ifdef SQONLY
        t_act *prev_act = &acts[prev_node->level];
        if (prev_node->have_square)
            walk_v(prev_node, Z(zero));
        else if (prev_act->action == A_UNFORCED)
            level_setp(prev_act, prev_act->limp);
#else
        walk_v(prev_node, Z(zero));
#endif
        return PUX_NOTHING_TO_DO;
    }
    set_unforced_x(prev_node, cur_act, p, limp);
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

/* Discard whatever a recovery line shows beyond the point reached. */
void stack_drop(t_fact *s) {
    for (uint vi = 0; vi < k; ++vi)
        s[vi].count = 0;
    have_rwalk = 0;
    act_recover.action = A_NONE;
}

/* On recovery, true if p^{x-1} at v_i is out of range below prev only
 * because the least value it allows is the best candidate.
 *
 * A run finds a candidate beneath the allocations then in place, and stays
 * committed to them until it returns to each: the progress lines written
 * meanwhile still show them, with whatever is tried beneath. Each was in
 * range while that candidate was, but the maximum is now one less, which
 * can rule an allocation out along with everything beneath it. This and
 * limit_was_best() recognise the two ways that can happen.
 */
bool least_is_best(
    t_node *prev, t_node *cur, uint vi, ulong p, uint x, uint fold
) {
    if (!improve_max || !seen_best)
        return 0;
    mpz_ui_pow_ui(px, p, x - 1);
    return update_chinese(prev, cur, vi, p, px, fold)
            && mpz_cmp(cur->rq, best) == 0;
}

/* On recovery, true if p is above the limit for p^{x-1} at v_i leaving
 * nextt only because the best candidate is no longer in range: see
 * least_is_best().
 */
bool limit_was_best(t_act *cur_act, uint vi, ulong p, uint x, uint nextt) {
    if (!improve_max || !seen_best)
        return 0;
    /* the limit as it was with the best candidate still in range */
    mpz_add_ui(zmax, zmax, 1);
    ulong limp = limit_p(cur_act, vi, x, nextt);
    mpz_sub_ui(zmax, zmax, 1);
    return limp == 0 || p <= limp;
}

/* Given an init or recovery stack, check for the specified forced prime
 * and any related batch, and apply it removing the corresponding factors
 * from the stack.
 * Returns true if we are ok to continue, or false if no further inserts
 * should be done: we reached the end of the stack, or we failed to apply
 * a found element, in which case *jump is updated to IS_NEXT. If that
 * was only because the best candidate rules the batch out, the rest of
 * a recovery stack is discarded.
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
        /* a W(...) line shows a sweep, so its batch is complete */
        if ((more || act_recover.action == A_MIDP) && has_tail(fp))
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
    bool applied = 1, ruled_out = 0;
    if (!init || !is_tail(bp)) {
        t_node *prev_node = &nodes[level - 1];
        t_node *cur_node = &nodes[level];
        cur_batch_level = level;
        /* progress is shown just before we apply, so on recovery it is
         * legitimate for the last one to fail */
        if (apply_batch(prev_node, cur_node, fpi, bi))
            ++level;
        else {
            *jump = IS_NEXT;
            applied = 0;
            ruled_out = (!init && maxx && least_is_best(
                prev_node, cur_node, mini, p, maxx, bp->fold
            ));
        }
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
    if (ruled_out)
        stack_drop(stack);
    return applied;
}

/* Given an init or recovery stack, check for a floating prime to insert
 * at the specified position, and apply it removing the corresponding factor
 * from the stack.
 * Returns true if we are ok to continue, or false if no further inserts
 * should be done.
 * If we fail to apply a found element, may update *jump to IS_NEXTX or
 * IS_NEXT. If that was only because the best candidate rules the element out,
 * the rest of a recovery stack is discarded.
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

    t_node *prev_node = &nodes[level - 1];
    t_node *cur_node = &nodes[level];
    t_act *cur_act = &acts[level];

    t_value *vp = &value[vi];
    uint vil = cur_vlevel[vi];
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
    cur_act->vi = vi;
    cur_act->ti = ti;
    cur_act->di = di;

    e_pux pux;
    if (init) {
        /* we never continue from an init pattern, so need no checks */
        set_unforced_x(prev_node, cur_act, p, 0);
        pux = PUX_DO_THIS_X;
    } else {
        /* the log shows that we recursed here, so the gate is not asked */
        ulong limp = limit_p(cur_act, vi, x, ti / x);
        pux = limit_unforced_x(prev_node, cur_act, p, limp, 0);
        if (pux == PUX_DO_THIS_X)
            set_unforced_x(prev_node, cur_act, p, limp);
    }
    switch (pux) {
      case PUX_FLIP_PQSQ:
      case PUX_SKIP_THIS_X:
        if (ti == x) {
            /* legitimate skip after walk_1_set */
            *jump = IS_NEXTX;
            return 0;
        }
        if (limit_was_best(cur_act, vi, p, x, ti / x)) {
            /* as recurse() will find on returning here */
            stack_drop(stack);
            *jump = IS_NEXTX;
            return 0;
        }
        fail("prep_nextt %u for %lu^%u at %u\n", pux, p, x, vi);
      case PUX_NOTHING_TO_DO:
        /* we have now acted on this */
        *jump = IS_NEXT;
        return 0;
    }

    level_setp(cur_act, p);
    /* progress is shown just before we apply, so on recovery it is
     * legitimate for the last one to fail */
    if (!apply_single(prev_node, cur_node, vi, p, x)) {
        if (!init && least_is_best(
            prev_node, cur_node, vi, p, x, single_fold(p)
        ))
            stack_drop(stack);
        *jump = IS_NEXT;
        return 0;
    }
    ++level;
    return 1;
}

/* If conditions are met, absorb the remaining 1 or 2 unapplied allocations
 * ready for run_flip_pqsq recovery and return TRUE, else return FALSE.
 * The flip's level is then left as run_flip_pqsq() leaves it while it
 * runs, and act_recover says where to resume.
 */
bool restore_flip(uint vi, t_fact *rs) {
    if (act_recover.vi != vi)
        return 0;   /* Current vi is not valid for us to kick in */
    uint ti = value[vi].alloc[ cur_vlevel[vi] - 1 ].t;
    uint xs = flip_xs_tau(ti);
    if (xs == 0)
        return 0;   /* Current tau is not valid for us to kick in */
    uint xl = 2 * xs;

    /* An earlier tau here can be of the same form, so the allocations
     * still to make must also be just those of the flip: p^{xl-1}, then
     * maybe q^{xs-1}.
     */
    uint c = rs->count;
    if (c == 0 || c > 2 || rs->ppow[c - 1].e != xl - 1
            || (c == 2 && rs->ppow[0].e != xs - 1))
        return 0;

    t_ppow *outerp = &rs->ppow[c - 1];
    act_recover.p_outer = outerp->p;
    stack_remove(rstack->f, NULL, vi, outerp->p, outerp->e);

    if (rs->count) {
        t_ppow *innerp = &rs->ppow[rs->count - 1];
        act_recover.p_inner = innerp->p;
        stack_remove(rstack->f, NULL, vi, innerp->p, innerp->e);
    }

    /* set up the stack ready for a call to run_flip_pqsq */
    t_node *prev_node = &nodes[level - 1];
    t_node *cur_node = &nodes[level];
    t_act *cur_act = &acts[level];
    t_divisors *dp = &divisors[ti];
    uint di;
    for (di = 0; di < dp->highdiv; ++di)
        if (dp->div[di] == xs)
            break;
    cur_act->ti = ti;
    cur_act->di = di;
    /* the flip will end this level by its limit, which needs the iterator */
    level_setp(cur_act, act_recover.p);
    /* The flip does not search below this level, so it need not fit: a
     * candidate found during the flip can put it out of range.
     */
    any_bound = 1;
    bool ok = apply_single(prev_node, cur_node, vi, act_recover.p, xs);
    any_bound = 0;
    if (!ok)
        fail("panic: could not reapply %u^%u at %u for flip recovery",
                act_recover.p, xs, vi);
    flip_withdraw(cur_act);
    ++level;
    acts[level].vi = vi;
    return 1;
}

/* On recovery, set up the recursion stack to the point we had reached.
 * Returns IS_DEEPER if we should continue by recursing deeper from this
 * point; returns IS_NEXTX if we should continue by advancing the power
 * applied at the current position; returns IS_NEXT if we should continue
 * by advancing the current level; returns IS_RWALK if we should continue
 * by completing a partial walk_v() call; returns IS_MIDP if we should
 * complete a partial walk_midp(); and returns IS_BATCH if we should first
 * call process_batch().
 * If the entire run is already complete, returns IS_FINISH.
 */
e_is insert_stack(void) {
    e_is jump = IS_DEEPER;

    if (istack) {
        /* insert any init forced primes */
        for (uint fpi = 0; fpi < forcedp; ++fpi) {
            t_fact *rf = (rstack) ? rstack->f : NULL;
            insert_forced(istack->f, rf, fpi, &jump, 1);
            /* failure should mean that there is nothing more to do */
            if (jump != IS_DEEPER)
                return IS_FINISH;
        }

        /* insert anything else */
        for (uint vi = 0; vi < k; ++vi) {
            t_fact *rs = &istack->f[vi];
            while (rs->count) {
                t_fact *rf = (rstack) ? rstack->f : NULL;
                if (insert_float(istack->f, rf, vi, &jump, 1))
                    continue;
                /* failure should mean that there is nothing more to do */
                if (jump == IS_DEEPER)
                    fail("panic: init_pattern complete, but going deeper");
                return IS_FINISH;
            }
        }

        for (uint l = final_level + 1; l < level; ++l)
            acts[l].action = A_FIXED;
        /* do not recurse back into elements set by init_pattern */
        final_level = level - 1;
    }

    if (rstack) {
        /* insert recovery forced primes */
        for (uint fpi = 0; fpi < forcedp; ++fpi) {
            /* skip if already inserted via init pattern */
            if ((nodes[level - 1].fp_need & (1U << fpi)) == 0)
                continue;
            if (!insert_forced(rstack->f, NULL, fpi, &jump, 0))
                goto insert_check;
        }

        /* the batch is complete: cap below it as process_batch() does */
        if (!nodes[level - 1].fp_need)
            sweep_batch(&nodes[level - 1]);

        /* Insert the rest in strategy-allocated order except as
         * overridden by explicit levels marked in a 315 recovery line.
         */
        while (1) {
            uint vi;
            t_act *cur_act = &acts[level];
            if (level < rstack->force && rstack->forced[level]) {
                vi = rstack->forced[level] - 1;
                cur_act->choice_strategy = strategy;
                cur_act->unsorted = 1;
            } else {
                e_choice ch = choose_action(cur_act);
                if (ch != CH_UNFORCED) {
                    if (ch == CH_6X)
                        jump = IS_6X;
                    /* CHECKME: should we be handling the other cases here?
                     * CH_WALK -> IS_RWALK, CH_NOTHING -> IS_NEXTX */
                    break;
                }
                vi = cur_act->vi;
            }
            if (act_recover.action == A_FLIP
                    && restore_flip(vi, &rstack->f[vi])) {
                /* restore_flip() has handled all remaining allocations */
                jump = IS_FLIP;
                break;
            }
            if (!insert_float(rstack->f, NULL, vi, &jump, 0))
                break;
        }

      insert_check:
        /* check we have them all */
        for (uint vi = 0; vi < k; ++vi) {
            t_fact *rs = &rstack->f[vi];
            uint c = rs->count;
            while (c) {
                t_ppow pp = rs->ppow[--c];
                fail("failed to inject %lu^%u at v_%u", pp.p, pp.e, vi);
            }
        }
        if (act_recover.action == A_FLIP && jump != IS_FLIP)
            fail("failed to inject flip at v_%u", act_recover.vi);
    }

    if (jump == IS_DEEPER) {
        if (act_recover.action == A_MIDP) {
            if (nodes[level - 1].fp_need)
                fail("W(...) recovery found an incomplete batch");
            jump = IS_MIDP;     /* Note: may also have_rwalk */
        } else if (have_rwalk)
            jump = IS_RWALK;
        else if (acts[level - 1].action != A_UNFORCED
                && !nodes[level - 1].fp_need)
            /* need process_batch() */
            jump = IS_BATCH;
    } else if (act_recover.action == A_MIDP)
        fail("data mismatch");

    return jump;
}

/* cur_act->p is the prime of the p^{z-1} the flip replaces */
uint suffix_flip(t_act *cur_act, char *buf) {
    return sprintf(buf, " F(%u,%lu)", cur_act->vi, cur_act->p);
}

char *parse_flip(char *s) {
    act_recover.vi = strtoul(s, &s, 10);
    if (s[0] != ',')
        fail("516 unexpected character in F(...) recovery");
    ++s;
    act_recover.p = strtoul(s, &s, 10);
    if (s[0] != ')')
        fail("516 unexpected character in F(...) recovery");
    return s + 1;
}

/* We have an allocation of eg p^z leaving t = 2z for some z that can_flip(),
 * and p is high enough that there are no partitions (z, z, 2) left to try
 * so all remaining candidates for that power represent a (z, 2z) partition.
 *
 * We leave the entry for p^z in the level stack, but make it an A_FLIP
 * level with its allocation withdrawn, and instead manually run
 * partitions (2z, z) - this should be more efficient
 * than running a much higher number of (z, 2z) partitions, especially
 * since if z is odd each p^{2z} allocation fixes a square.
 * On completion, we restore the p^z allocation but with p as its limit, to
 * mark that power as fully handled.
 */
void run_flip_pqsq(uint vi) {
    t_node *anc_node = &nodes[level - 2];
    t_node *cur_node = &nodes[level];
    t_node *next_node = &nodes[level + 1];
    t_act *prev_act = &acts[level - 1];
    t_act *cur_act = &acts[level];
    t_act *next_act = &acts[level + 1];
    ulong oldp = prev_act->p;
    uint xs = prev_act->x;
    uint xl = xs << 1;
    ulong resume_plow = 0;     /* only meaningful if resuming */
    bool recover = (act_recover.action == A_FLIP);
    if (recover) {
        /* restore_flip() has already withdrawn prev_act */
        if (vi != act_recover.vi)
            fail("panic: flip wants to recover at %u, not %u",
                    act_recover.vi, vi);
        resume_plow = act_recover.p_inner;
        if (resume_plow == 0)
            resume_plow = oldp;
        act_recover.action = A_NONE;    /* consumed */
    } else {
        assert(prev_act->vi == vi);
        flip_withdraw(prev_act);
    }

    t_value *vp = &value[vi];
    uint vil = cur_vlevel[vi];
    t_allocation *ap = &vp->alloc[vil - 1];

    cur_act->x = xl;
    mpz_add_ui(Z(r_walk), zmax, TYPE_OFFSET(vi));
    mpz_fdiv_q(Z(r_walk), Z(r_walk), ap->q);
    mpz_root(Z(r_walk), Z(r_walk), xl - 1);
    if (!mpz_fits_ulong_p(Z(r_walk)))
        fail("Tried to flip with target > max_ulong^%u", xl - 1);
    cur_act->limp = mpz_get_ui(Z(r_walk));

    level_setp(cur_act, recover ? act_recover.p_outer - 1 : maxforce[vi]);
    while (1) {
      redo_flip: ;
        ulong p = prime_iterator_next(&cur_act->piter);
        if (p > cur_act->limp)
            break;
        if (known_prime(anc_node, p))
            goto redo_flip;

        /* Failure most likely means it does not leave a valid square;
         * we pass the grandparent as prev_node to reflect our notional
         * deallocation of prev_act's allocation. */
        if (!apply_single(anc_node, cur_node, vi, p, xl)) {
            /* only the recovered p resumes at the recovered inner prime */
            recover = 0;
            continue;
        }
        ap = &vp->alloc[cur_vlevel[vi] - 1];
        if (need_work)
            diag_plain(cur_node);
        mpz_add_ui(Z(temp), zmax, TYPE_OFFSET(vi));
        mpz_fdiv_q(Z(temp), Z(temp), ap->q);
        mpz_root(Z(temp), Z(temp), xs - 1);
        if (!mpz_fits_ulong_p(Z(temp)))
            fail("Tried to flip with target > max_ulong^%u", xs - 1);
        ulong phigh = mpz_get_ui(Z(temp));
        next_node->have_min = cur_node->have_min;
        /* the flip has taken over oldp's own subtree, so oldp (like a
         * recovered p) is still to try
         */
        walk_1_set(cur_node, next_act, vi,
                (recover ? resume_plow : oldp) - 1, phigh, xs);
        recover = 0;
        --cur_vlevel[vi];
    }
    /* a candidate found meanwhile is no reason to recalculate limp */
    prev_act->max_at = seen_best;
    prev_act->action = A_UNFORCED;
    ++cur_vlevel[vi];
}

/* Undo what cur_act applied, as unwinding passes it. */
static inline void unapply_level(t_act *cur_act) {
    t_undo_op undo = action_ops[cur_act->action].undo;
    if (undo == NULL)
        fail("panic: unwinding level %u of action %u",
                cur_act->level, cur_act->action);
    undo(cur_act);
}

void undo_forced(t_act *cur_act) {
    unapply_batch(next_fpi(&nodes[cur_act->level - 1]), cur_act->bi, k);
}

void undo_unforced(t_act *cur_act) {
    --cur_vlevel[cur_act->vi];
}

void undo_flip(t_act *cur_act) {
    /* its allocation is already withdrawn */
    cur_act->action = A_UNFORCED;
}

/* Apply the batches of cur_act's forced prime from bi on, until one leaves
 * work to do below it. Returns FALSE if none does.
 */
static inline bool try_batches(t_act *cur_act, uint bi) {
    t_node *prev_node = &nodes[cur_act->level - 1];
    t_node *cur_node = &nodes[cur_act->level];
    uint fpi = next_fpi(prev_node);
    t_forcep *fp = &forcep[fpi];
    for (; bi < fp->count; ++bi) {
        if (!apply_batch(prev_node, cur_node, fpi, bi))
            continue;
        /* the batch is still partial */
        if (cur_node->fp_need)
            return 1;
        /* complete: process it, if wanted (under -W, runs walk_midp()) */
        if (process_batch(cur_node, 0))
            return 1;
        unapply_batch(fpi, bi, k);
    }
    return 0;
}

bool next_forced(t_act *cur_act) {
    return try_batches(cur_act, cur_act->bi + 1);
}

/* Prepare cur_act's loop for the first x from its di on that has primes to
 * try. Returns FALSE if there is none, any walk or flip it made having
 * covered the rest.
 */
static inline bool find_unforced_x(t_act *cur_act) {
    t_node *prev_node = &nodes[cur_act->level - 1];
    for (; cur_act->di < divisors[cur_act->ti].highdiv; ++cur_act->di) {
        switch (prep_unforced_x(prev_node, cur_act)) {
          case PUX_NOTHING_TO_DO:
            return 0;
          case PUX_FLIP_PQSQ:
            run_flip_pqsq(cur_act->vi);
            return 0;
          case PUX_SKIP_THIS_X:
            continue;
          case PUX_DO_THIS_X:
            return 1;
        }
    }
    return 0;
}

/* Allocate the next prime that applies at cur_act's v_i, moving on to each
 * further x as one is done. Returns FALSE when none is left.
 */
bool next_unforced(t_act *cur_act) {
    t_node *prev_node = &nodes[cur_act->level - 1];
    t_node *cur_node = &nodes[cur_act->level];
    while (1) {
        /* recalculate limit if we have an improved maximum */
        if (improve_max && seen_best > cur_act->max_at) {
            ulong limp = limit_p(cur_act, cur_act->vi, cur_act->x,
                    cur_act->ti / cur_act->x);
            /* see limit_p(): it was not 0, so cannot be now */
            if (limp == 0 || limp > cur_act->limp)
                fail("panic: limit for p^%u at v_%u rose from %lu to %lu",
                        cur_act->x - 1, cur_act->vi, cur_act->limp, limp);
            cur_act->limp = limp;
            cur_act->max_at = seen_best;
            reject_prep(prev_node, cur_act);
            reject_prep_square(prev_node, cur_act, cur_act->vi, cur_act->x);
        }
        /* note: only valid to use from just below here */
      redo_unforced: ;
        ulong p = prime_iterator_next(&cur_act->piter);
        if (p > cur_act->limp) {
            ++cur_act->di;
            if (!find_unforced_x(cur_act))
                return 0;
            continue;
        }
        if (known_prime(prev_node, p))
            goto redo_unforced;
        /* p stays the cursor, as when apply_single() fails */
        if ((cur_act->rj_ok && (p & 1) && reject_single(
            prev_node, cur_act, cur_act->vi, p, cur_act->x
        )) || (cur_act->rs_ok
            && reject_square(p, cur_act->rs_d, cur_act->rs_endr)
        )) {
            cur_act->p = p;
            if (need_work)
                diag_attempt(cur_node, cur_act->vi, p, cur_act->x);
            goto redo_unforced;
        }
        /* note: this returns 0 if t=1 */
        if (!apply_single(prev_node, cur_node, cur_act->vi, p, cur_act->x)) {
            if (need_work)
                diag_attempt(cur_node, cur_act->vi, p, cur_act->x);
            /* not redo_unforced, we may have improved zmax */
            continue;
        }
        return 1;
    }
}

/* Start an unforced loop at cur_act's v_i. Returns TRUE if it has made
 * its first child.
 */
static inline bool start_unforced(t_act *cur_act) {
    /* Note: cur_act->action is always either A_UNFORCED by calloc(), or
     * gets set to it on the tail of a batch.
     */
    assert(A_UNFORCED == 0);
    uint vi = cur_act->vi;
    uint ti = value[vi].alloc[cur_vlevel[vi] - 1].t;
    if (divisors[ti].high <= (highpow ? 1 : 2))
        fail("best_v() returned %u, but nothing to do there", vi);
    cur_act->ti = ti;
    cur_act->di = 0;
    return find_unforced_x(cur_act) && next_unforced(cur_act);
}

/* Walk everything below cur_act's level, in place of an act there. */
static inline void start_walk(t_act *cur_act) {
    t_node *prev_node = &nodes[cur_act->level - 1];
#ifdef SQONLY
    t_act *prev_act = &acts[cur_act->level - 1];
    if (prev_node->have_square)
        walk_v(prev_node, Z(zero));
    else if (prev_act->action == A_UNFORCED)
        level_setp(prev_act, prev_act->limp);
#else
    walk_v(prev_node, Z(zero));
#endif
}

/* Start the act at a new level as choose_action() decides. Returns TRUE
 * if it has made its first child.
 */
static inline bool start_act(t_act *cur_act) {
    switch (choose_action(cur_act)) {
      case CH_FORCED:
        return try_batches(cur_act, 0);
      case CH_UNFORCED:
        return start_unforced(cur_act);
      case CH_WALK:
        start_walk(cur_act);
        return 0;
      case CH_6X:
        walk_6x();
        return 0;
      case CH_NOTHING:
        return 0;
    }
    fail("panic: unknown choice at level %u", cur_act->level);
}

/* We emulate recursive calls via the nodes[] and acts[] arrays: starting
 * the act at a new level makes its first child node, its next op makes
 * each further child, and its undo op unapplies one as we unwind.
 */
void recurse(e_is jump_continue) {
    t_act *actp = &acts[level];

    /* Find a suitable entry point when not starting from scratch due to
     * init_pattern or recovery.
     */
    switch (jump_continue) {
      case IS_DEEPER:
        goto deeper;
      case IS_NEXT:
        goto next;
      case IS_NEXTX:
        ++actp->di;
        if (find_unforced_x(actp) && next_unforced(actp))
            goto made;
        goto unwind;
      case IS_RWALK:
        walk_v(&nodes[level - 1], rwalk_from);
        goto unwind;
      case IS_BATCH:
        /* count a batch the log has not, to honour any specified batch id */
        if (process_batch(&nodes[level - 1], batch_alloc > 0))
            goto deeper;
        goto unwind;
      case IS_MIDP:
        walk_midp(&nodes[level - 1], 1);
        if (after_sweep(&nodes[level - 1]))
            goto deeper;
        goto unwind;
      case IS_6X: {
        e_choice ch = choose_action(actp);  /* re-verify */
        if (ch != CH_6X)
            fail("panic: choose_action() on recovery chose %u, not %u",
                    ch, CH_6X);
        walk_6x();
        goto unwind;
      }
      case IS_FLIP:
        /* run_flip_pqsq() finishes with everything below it explored */
        run_flip_pqsq(actp->vi);
        goto unwind;
      default:
        fail("panic: recurse() entered at %u", jump_continue);
    }

  made:
    if (need_work)
        diag_plain(&nodes[level]);
    ++level;
  deeper:
    ++countr;
    if (start_act(&acts[level]))
        goto made;
  unwind:
    acts[level + 1].next_best = 0;
    --level;
    if (level <= final_level)
        return;
    actp = &acts[level];
    unapply_level(actp);
  next: ;
    t_next_op next = action_ops[actp->action].next;
    if (next == NULL)
        fail("panic: continue_recurse at level %u of action %u",
                level, actp->action);
    if (next(actp))
        goto made;
    goto unwind;
}

/* A trailing candidate has just lowered zmax below the bound under which
 * the recovered stack was built. If an unforced level no longer fits (its
 * residue exceeds zmax, or its prime exceeds the limit for its power),
 * nothing below it can hold a solution: unwind to the shallowest such
 * level, so that no progress line shows it. Returns where recurse() should
 * pick up.
 * A level that stays keeps its old limit for now: recurse() recalculates
 * it on returning there, as after any new candidate.
 */
e_is prune_stale(e_is jump) {
    if (jump == IS_FINISH || jump == IS_BATCH)
        return jump;
    for (uint li = final_level + 1; li < level; ++li) {
        t_act *actp = &acts[li];
        /* unforced levels only: a flip's does not search below it */
        if (actp->action != A_UNFORCED || actp->x < 2)
            continue;
        if (mpz_cmp(nodes[li].rq, zmax) <= 0) {
            /* find the limit with v_i as it was when this level was set */
            uint vi = actp->vi;
            t_allocation *alloc = value[vi].alloc;
            uint save = cur_vlevel[vi];
            uint d = 1;
            while (d < save && alloc[d].level != li)
                ++d;
            if (d == save)
                continue;
            cur_vlevel[vi] = d;
            ulong limp = limit_p(actp, vi, actp->x, actp->ti / actp->x);
            cur_vlevel[vi] = save;
            if (limp == 0 || actp->p <= limp)
                continue;
        }
        while (level > li) {
            acts[level + 1].next_best = 0;
            --level;
            unapply_level(&acts[level]);
        }
        have_rwalk = 0;
        act_recover.action = A_NONE;
        return IS_NEXT;
    }
    return jump;
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
        else if (arg[1] == 'k')
            kern_b = ulston(&arg[2]);
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
        else if (strncmp("-Lc", arg, 3) == 0) {
            char *end;
            cyc_ghz = strtod(&arg[3], &end);
            if (end == &arg[3] || *end || !(cyc_ghz >= 0))
                fail("invalid -Lc clock rate '%s'", &arg[3]);
        } else if (arg[1] == 'r') {
            rpath = malloc(strlen(&arg[2]) + 1);
            strcpy(rpath, &arg[2]);
        } else if (arg[1] == 'R')
            skip_recover = 1;
        else if (strcmp("-ix", arg) == 0)
            ignore_exceptions = 1;
        else if (arg[1] == 'I')
            init_pattern = &arg[2];
        else if (arg[1] == 'f') {
            if (arg[2] == 'r')
                restrict_forced = 1;
            else
                force_all = strtoul(&arg[2], NULL, 10);
        } else if (arg[1] == 'F') {
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
                break;
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
              case 'c':
                debugc = 1;
                break;
              case 'C':
                debugC = 1;
                debugc = 1;
                break;
              case 'm':
                debugm = 1;
              case 'l':
                log_full = 1;
                break;
              case 'L':
                debugL = 1;
                debugL_count = strtoul(&arg[3], NULL, 10);
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
        if (k > MAXK)
            fail("require k <= %u, not %u", MAXK, k);
        if (kern_b && k > MAXK_KERN)
            fail("-k requires k <= %u, not %u", MAXK_KERN, k);
    } else
        fail("wrong number of arguments");
    if (force_all > k)
        fail("require force_all <= k");
    if (mpz_cmp(zmin, zmax) >= 0)
        fail("require min < max, not %Zu:%Zu", zmin, zmax);

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

        cvec_mult(cx0, &nodes[0].rq, &nodes[0].aq);
        if (mpz_cmp_ui(nodes[0].aq, 1) > 0)
            have_modfix = 1;
        done_modfix();
        if (!check)
            check = 1;
    }
    prep_presquare();

    e_is jump = IS_DEEPER;
    /* If a pending candidate would leave an empty search range, apply now
     * and finish; else wait until after we have built the stack against
     * the previous search range, to ensure we create the levels in the
     * correct order.
     */
    if (have_pend202 && mpz_cmp(zmin, Z(rec_trail)) >= 0)
        apply_pend202();
    if (mpz_cmp(zmin, zmax) >= 0)
        jump = IS_FINISH;   /* nothing to search */
    else if (rstack || istack)
        jump = insert_stack();
    else if (forcedp == 0)
        jump = IS_BATCH;    /* the whole search is one batch */
    /* midp recovery reapplies its allocation inside walk_midp() */
    if (have_pend202 && act_recover.action != A_MIDP) {
        apply_pend202();
        jump = prune_stale(jump);
    }
    if (jump != IS_FINISH && setjmp(jmp_finish) == 0)
        recurse(jump);
    /* it is still a candidate if nothing got as far as applying it */
    if (have_pend202)
        apply_pend202();
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
