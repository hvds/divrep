#ifndef COULINT_H
#define COULINT_H

/* Internals of coul.c shared with its helpers (mock.c), not needed by
 * the other modules.
 */

#include "coul.h"
#include "coultau.h"

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

extern uint maxfact, sq0, *sqg, *cur_vlevel, *oc_t, seen_best;
extern mpz_t zmin, zmax, *wv_o, *wv_qq;
extern int other_comparator(const void *va, const void *vb);

/* test values in batch: append each (test_*_append() steals the input,
 * and returns FALSE if it is already known to fail), then run the batch
 */
/* What the run has done, counted for costing it (see cc_work()); tests
 * outside tau_multi_prep(), tau_prime_prep() and tau_multi_run(), which
 * price their own, are priced as they are made. The cost counted before
 * a recovery is kept as base.
 */
typedef struct {
    bool on;
    ulong lin_walks, lin_iter, lin_inv, sq_walks, sq_iter, sq_inv,
            pell_iter, w1s_prime, w1s_check, rec_prime, rec_applied,
            rec_sq, rec_root;
    double test, base;
} t_cc;
extern t_cc cc;

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

#endif
