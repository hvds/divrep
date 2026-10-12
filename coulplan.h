#ifndef COULPLAN_H
#define COULPLAN_H

/* The planner (see coulplan.c): what coul.c uses of it. */

#include "coulint.h"

extern double cc_work(void);
extern double gr_clock(void);
extern void walk_v_gr(t_level *cur_level, mpz_t start);
extern bool ke_prefer_6x(ulong at);
extern void ja_save(FILE *fp);
extern void ja_restore(char *s);
extern void ja_learnt(t_level *lp);
extern void ja_learnx(t_level *lp);
extern uint ja_choose(t_level *prev_level, t_level *cur_level, uint sv);
extern bool ja_gate(
    t_level *prev_level, t_level *cur_level, ulong p, ulong cap, bool do_walk
);

#endif
