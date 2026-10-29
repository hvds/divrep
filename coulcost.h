#ifndef COULCOST_H
#define COULCOST_H

/* The cost table (see multibench-table) and the models built on it, in
 * every build. See coulcost.c.
 */

#include "coul.h"

extern const char cm_default_table[];   /* timings.c, from timings */
extern const char *cm_table_sha(const char *section);
extern double cm_table_ghz(const char *section);
extern double cm_const(uint which);
enum { CM_LOOP0, CM_LOOPTEST, CM_SQSETUP, CM_SQLOOP0, CM_SQTEST,
        CM_W1SITER, CM_W1SCHECK, CM_LINSETUP, CM_CAPPLY, CM_COUNT };

/* For mock.c: the model of what the candidates of a walk cost, see
 * coulcost.c.
 */
#define CMK_LINEAR 0
#define CMK_FIXED 1     /* in a walk of a fixed power */
#define CMK_EXACT 2     /* wv_o[] is the value itself */
/* CMK_ROOT is the root of a fixed power: coprime to the allocated
 * primes, else no information.
 */
#define CMK_ROOT 3
typedef struct {
    uint kind;
    uint s, xi;         /* CMK_FIXED: the fixed power's position, root degree */
    bool pp;            /* CMK_FIXED: the root must be prime */
    mpz_t *qs;          /* CMK_FIXED: q_s */
    ulong khash;        /* CMK_FIXED: hash of q_s free of xi-th powers */
    ulong *alloc;       /* primes allocated anywhere */
    uint nalloc;
} t_cmwalk;
typedef struct s_mwtest t_cmtest;
extern double cm_pinv(t_mod *inv, uint inv_count, double *tests);
extern void cm_walk_init(t_cmwalk *wk, uint kind, ulong *alloc, uint s,
        uint xi, bool pp);
extern double cm_tail(double zb, mpz_t **q, uint *t, uint *need_prime,
        uint npc, uint *need_other, uint noc, t_cmwalk *wk, t_mod *inv,
        uint inv_count, t_cmtest *root);
extern double cm_root_cost(double zb, double rbits, mpz_t **q, uint *t,
        uint sqi, uint *need_prime, uint npc, uint *need_other, uint noc,
        t_mod *inv, uint inv_count);

#endif
