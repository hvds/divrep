#ifndef MOCK_H
#define MOCK_H

/* The mocks, for calibration only: never for a real search, since no
 * candidate is ever tested. In a MOCK build walk_v() and walk_1_set()
 * charge the modelled cost of their walks, from the machine's cost
 * table (see coulcost.h), instead of walking; and recurse() stubs or
 * samples the innermost loops. A run then reports its real time outside
 * what is mocked plus the modelled time, see seconds(). See mock.c.
 */

#include "coul.h"

/* The cost modelled so far, and the mocks' own CPU time, which is not
 * part of it; both always 0 without MOCK.
 */
extern double g_mock_spent_s;
extern double g_mock_overhead_s;

extern void mock_init(void);
extern void mock_report(void);
extern bool mock_walk_v(t_node *cur_node, mpz_t **q, uint *t, uint nqc,
        uint *need_square, uint *need_prime, uint npc, uint *need_other,
        uint noc, t_mod *inv, uint inv_count, mpz_t ati, mpz_t end);
extern void mock_w1s_start(void);
extern bool mock_w1s_prime(ulong p, ulong phigh);
extern void mock_w1s_pass(mpz_t v, uint *t, uint *need_prime, uint npc,
        uint *need_other, uint noc);

typedef enum {
    MOCK_LOOP_GO = 0,   /* try this prime as usual */
    MOCK_LOOP_SKIP,     /* skip this prime, its cost charged */
    MOCK_LOOP_END       /* end the loop, the rest charged */
} e_mock_loop;
extern void mock_leaf_w1s(uint level);
extern void mock_loop_start(uint level);
extern bool mock_loop_leaf(t_act *cur_act);
extern e_mock_loop mock_loop_prime(t_node *prev_node, t_act *cur_act,
        ulong p);

#endif
