#ifndef MOCK_H
#define MOCK_H

/* The mocks, for calibration only: never for a real search, since no
 * candidate is ever tested. With MOCK_WALK, walk_v() and walk_1_set()
 * charge the modelled cost of their walks, from the machine's cost
 * table ($MOCK_WALK_TABLE, see multibench-table), instead of walking;
 * with MOCK_LEAF as well, recurse() stubs or samples the innermost
 * loops. A run then reports its real time outside what is mocked plus
 * the modelled time, see seconds(). See mock.c for the models.
 */

#include "coul.h"

/* the cost modelled so far, and the mocks' own CPU time, which is not
 * part of it; both always 0 without MOCK_WALK
 */
extern double g_mock_spent_s;
extern double g_mock_overhead_s;

/* the expected cost of tau_multi_run() on these values, or -1 without a
 * cost table: in every build, for learning costs
 */
extern double cm_ladder_cost(uint count, t_tm *tm);
/* the same table's prices of the tests and its scalar costs, for
 * counting the cost of what a run does
 */
extern bool cm_have_table(void);
extern const char cm_default_table[];   /* costtab.c, from cost-table */
extern const char *cm_table_sha(const char *section);
extern double cm_price_prime(mpz_t n);
extern double cm_const(uint which);
extern double cm_prep_price(uint nbits, const t_ct_work *w);
extern double cm_pprep_price(uint nbits, int res);
extern double cm_ptest_price(uint nbits);
enum { CM_LOOP0, CM_LOOPTEST, CM_SQSETUP, CM_SQLOOP0, CM_SQTEST,
        CM_CPRIME, CM_CPRIMESQ, CM_W1SITER, CM_W1SCHECK, CM_CTAIL,
        CM_LINSETUP, CM_CAPPLY, CM_COUNT };

#ifdef MOCK_WALK
extern void mock_init(void);
extern void mock_report(void);
extern bool mock_walk_v(t_level *cur_level, mpz_t **q, uint *t, uint nqc,
        uint *need_square, uint *need_prime, uint npc, uint *need_other,
        uint noc, t_mod *inv, uint inv_count, mpz_t ati, mpz_t end);
extern void mock_w1s_start(void);
extern bool mock_w1s_prime(ulong p, ulong phigh);
extern void mock_w1s_pass(mpz_t v, uint *t, uint *need_prime, uint npc,
        uint *need_other, uint noc);
#endif

#ifdef MOCK_LEAF
typedef enum {
    MOCK_LOOP_GO = 0,   /* try this prime as usual */
    MOCK_LOOP_SKIP,     /* skip this prime, its cost charged */
    MOCK_LOOP_END       /* end the loop, the rest charged */
} e_mock_loop;
extern void mock_leaf_w1s(uint level);
extern void mock_loop_start(uint level);
extern bool mock_loop_leaf(uint level, t_level *cur_level);
extern e_mock_loop mock_loop_prime(uint level, t_level *prev_level,
        t_level *cur_level, ulong p);
#endif

#endif
