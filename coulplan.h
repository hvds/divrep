#ifndef COULPLAN_H
#define COULPLAN_H

/* The planner (see coulplan.c): what coul.c uses of it. */

#include "coulint.h"

extern double cc_work(void);
extern void gr_init(void);
extern void walk_v_gr(t_node *cur_node, mpz_t start);
extern bool ja_gate(
    t_node *prev_node, t_act *cur_act, ulong p, ulong cap, bool do_walk
);

#endif
