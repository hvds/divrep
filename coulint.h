#ifndef COULINT_H
#define COULINT_H

/* Internals of coul.c shared with its helpers (mock.c), not needed by
 * the other modules.
 */

#include "coul.h"

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

#endif
