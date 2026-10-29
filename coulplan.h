#ifndef COULPLAN_H
#define COULPLAN_H

/* The planner (see coulplan.c): what coul.c uses of it. */

#include "coulint.h"

extern double cc_work(void);
extern double gr_clock(void);
extern void gr_init(void);
extern void walk_v_gr(t_node *cur_node, mpz_t start);
extern void ja_learnt(t_act *lp);
extern void ja_learnx(t_act *lp);
extern void ja_unwind(t_act *lp);
/* true if ja_unwind() has anything to do at lp */
static inline bool ja_pending(t_act *lp) {
    return lp->ja_t0 > 0 || lp->ja_on;
}
extern uint ja_choose(t_node *prev_node, t_act *cur_act, uint sv);
extern bool ja_gate(
    t_node *prev_node, t_act *cur_act, ulong p, ulong cap, bool do_walk
);

#endif
