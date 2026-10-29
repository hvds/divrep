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
 * price their own, are priced as they are made.
 */
typedef struct {
    bool on;
    ulong lin_walks, lin_iter, lin_inv, sq_walks, sq_iter, sq_inv,
            pell_iter, w1s_prime, w1s_check, rec_prime, rec_applied,
            rec_fail;
    /* inverse-filter entries set up by linear walks, and root residues
     * walked by those below a fixed power, for the cost of their setup
     */
    ulong lin_setinv, sq_setres;
    ulong w1s_calls;    /* walk_1_set() calls, for their setup */
    double test;
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

extern void walk_v_inner(t_node *cur_node, mpz_t start);

extern uint auto_level;

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
