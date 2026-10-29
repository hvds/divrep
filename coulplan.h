#ifndef COULPLAN_H
#define COULPLAN_H

/* The planner (see coulplan.c): what coul.c uses of it. */

#include "coulint.h"

extern double cc_work(void);
extern double gr_clock(void);
extern void gr_init(void);
extern void walk_v_gr(t_node *cur_node, mpz_t start);
extern bool ke_prefer_6x(ulong at);
extern void kern_plan(t_kern *ks);
extern void kern_tags(char *buf);
extern void kern_show(void);
extern void kern_show_total(void);
extern void ja_save(FILE *fp);
extern void ja_restore(char *s);
extern void ja_learnt(t_act *lp);
extern void ja_learnx(t_act *lp);
extern void ja_unwind(t_act *lp);
/* true if ja_unwind() has anything to do at lp */
static inline bool ja_pending(t_act *lp) {
#ifdef VERBOSE
    if (lp->ja_vb)
        return 1;
#endif
    return lp->ja_t0 > 0 || lp->ja_on;
}
extern uint ja_choose(t_node *prev_node, t_act *cur_act, uint sv);
extern bool ja_gate(
    t_node *prev_node, t_act *cur_act, ulong p, ulong cap, bool do_walk
);
#ifdef VERBOSE
extern int ja_force;
extern double ja_stol;
extern bool ja_sblind;
extern double ja_e2min;
extern void ja_vb_close(t_act *lp);
#endif

#endif
