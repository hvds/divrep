#ifndef COULINT_H
#define COULINT_H

/* Internals of coul.c shared with its helpers (coulcost.c, coulplan.c,
 * mock.c, trace.c, bench.c), not needed by the other modules.
 */

#include "coul.h"
#include "coultau.h"
#include "coulfact.h"
#include "builtins.h"

/* the offset of the i-th value: v_i = v_0 + TYPE_OFFSET(i) */
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

/* the clock for timing parts of the work, and its unit (see coul.c) */
extern double work_clock(void);
extern double work_clock_ghz(void);

extern uint maxfact, sq0, *sqg, *cur_vlevel, *oc_t, seen_best;
extern mpz_t zmin, zmax, *wv_o, *wv_qq;
extern int other_comparator(const void *va, const void *vb);

/* What the run has done, counted for costing it (see cc_work()); tests
 * outside tau_multi_prep(), tau_prime_prep() and tau_multi_run(), which
 * price their own, are priced as they are made. The cost counted before
 * a recovery is kept as base.
 */
typedef struct {
    bool on;
    ulong lin_walks, lin_iter, lin_inv, sq_walks, sq_iter, sq_inv,
            pell_iter, w1s_prime, w1s_check, rec_prime, rec_applied,
            rec_sq, rec_root, rec_fail;
    /* inverse-filter entries set up by linear walks, and root residues
     * walked by those below a fixed power, for the cost of their setup
     */
    ulong lin_setinv, sq_setres;
    ulong w1s_calls;    /* walk_1_set() calls, for their setup */
    double test, base;
} t_cc;
extern t_cc cc;

/* Test values in batch: append each (test_*_append() steals the input,
 * and returns FALSE if it is already known to fail), then run the batch.
 */
extern uint tm_count;
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

/* for the planner (coulplan.c) */

#define MAXK_KERN 64    /* under -k: positions are bits of a ulong */
/* Sentinel values returned by best_v() and strategies[] functions.
 * Any real v_i is < BV_SPECIAL; BV_WALK means there is no v_i to allocate
 * to; BV_NEXTX means there is no work left to do for this x.
 */
#define BV_SPECIAL k
#define BV_WALK (BV_SPECIAL + 0)

/* What -k does in a batch, planned once the batch is complete and kept
 * with its node (see kern_state()): whether it applies at all, its bound
 * and count of -K, and as bit vectors the positions it applies to and
 * those passed over.
 * It applies to a batch that fixes exactly one square. One that
 * STRATEGY_6X can take (2.z^2 at v_i, i >= 2) has its own loop at
 * v_{i-2}, and gains nothing from the pass: it is left to that, unless
 * the search under -k is estimated to cost less (see ke_batch()), when
 * best_6x() stands aside. That loop runs to the 4th root of zmax
 * whatever n is, while under -k the limits fall as the powers of n
 * rise, so for n = 6p the batch with 2^{p-1} at v_{i-2} goes to -k from
 * about p = 5.
 */
typedef struct s_kern {
    int id;             /* batch_alloc when it was planned */
    bool on;
    ulong b;            /* the bound of -k, 0 if it is not to apply */
    uint keep;          /* the count of -K */
    ulong at, passed;   /* needs MAXK_KERN <= 64 */
    /* Under -ka: whether a choice was made for this batch, which then
     * gives b and keep; the bound of -W (0 for as the options gave) and
     * the estimated cost; and for a bound of -W chosen, the caps below
     * the batch (see sweep_batch()).
     */
    bool planned;
    ulong w;
    double est, price;
    ulong *wcap;
} t_kern;

/* The outcomes of classify_x() */
typedef enum {
    XR_WALK = 0,    /* no p: the node must be walked */
    XR_SKIP,        /* nothing to do for this x */
    /* Nothing to do for this x, and the rest of the loop above is best
     * done by run_flip_pqsq().
     */
    XR_FLIP,
    XR_WALK1,       /* the range is for walk_1_set(): v_i is then complete */
    XR_RANGE        /* the range is for a loop of allocations */
} e_xr;

extern void walk_v_inner(t_node *cur_node, mpz_t start);
#if defined(TYPE_r)
    extern uint *target_tau;
    extern uint target_lcm;
    static inline uint target_t(uint vi) { return target_tau[vi]; }
#else
#   define target_lcm (n)
    static inline uint target_t(uint vi) { return n; }
#endif

extern double zmax_given;
extern mpz_t best;
extern uint auto_level;
extern ulong *minp, *maxp, *midp;
extern bool highpow;
extern ulong limp_cap;
extern bool midp_only, need_midp;
extern ulong kern_b;
extern uint kern_keep;
extern bool kern_auto;
extern bool kern_keep_given;
extern slong batch_alloc;
extern uint cur_batch_level;
extern uint strategy;
extern t_fact nf;
extern uint *maxforce;
extern void done(void);
extern ulong next_prime(ulong cur);
extern bool walk_v_price_prep(t_node *cur_node);
extern double walk_v_price(uint *t);
extern bool kern_6x(void);
extern void kern_sets(uint keep, ulong *atp, ulong *passedp);
extern t_kern *kern_state(t_node *np);
extern bool kern_at(uint vi);
extern bool kern_passed(uint vi);
extern ulong limit_p(t_act *cur_act, uint vi, uint x, uint nextt);
extern e_xr classify_x(
    t_node *prev_node, uint vi, uint x, ulong p, ulong limp
);

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
 * power, classify_x() refuses the rest, and with the squares left to the
 * walk a strategy would otherwise loop over p^1 wherever else it could.
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

/* what was allocated at v_i once the current batch was complete */
static inline mpz_t *kern_q(uint vi) {
    t_value *vp = &value[vi];
    uint vil = cur_vlevel[vi];
    while (vil > 1 && vp->alloc[vil - 1].level > cur_batch_level)
        --vil;
    return &vp->alloc[vil - 1].q;
}

/* true if -ka has made a choice for the current batch */
static inline bool kern_planned(void) {
    t_kern *ks = kern_cur();
    return ks && ks->planned;
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

#endif
