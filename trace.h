#ifndef TRACE_H
#define TRACE_H

/* Instrumentation: a build with VERBOSE=1 has it all, and -dv<bits>
 * chooses what is output (none by default), as the sum of:
 *   VB_TRACE   1: the human-readable trace of recursion, walks and tests
 *   VB_GATE    2: records of each gate decision, recursion loop, walk,
 *                 walk_1_set(), flip, walk_6x() and midp phase, to the
 *                 file named by $GATE_STATS (see trace.c)
 *   VB_STAGE   4: with VB_GATE, the time inside each test stage of the
 *                 walks (two clock reads per candidate tested)
 *   VB_CHOICE  8: with -ja, a J record of each choice of position by
 *                 estimated cost, to the same file (see ja_choose())
 *   VB_PREP   16: a T record of 1 in 8 of the test preparations
 *                 (tau_multi_prep()), with what each did and its time,
 *                 and a U record of 1 in 8 of those for prime tests,
 *                 to the same file, for pricing them (see trace.c)
 *   VB_COUNTS 32: a W record at the end of the run, of what it did as
 *                 counted for costing it and the CPU time it took, to
 *                 the same file, for pricing what is counted (see
 *                 gs_count_record())
 * The same build also runs the benches ($MULTIBENCH, see bench.c).
 */

#include <stdio.h>
#include "coulint.h"
#include "rootmod.h"

#ifdef VERBOSE
extern uint verbose;
#   define VB_TRACE 1
#   define VB_GATE 2
#   define VB_STAGE 4
#   define VB_CHOICE 8
#   define VB_PREP 16
#   define VB_COUNTS 32
#   define VB(bits) (verbose & (bits))

#   define GS_MAXLEVEL 256
extern char gs_origin;
extern double gs_ati;
extern int gs_nqc;
extern char gs_cause;
extern double gs_rm, gs_raq;
extern uint gs_inv, gs_npc, gs_noc;
extern ulong gs_mp_tried, gs_w1s_primes, gs_w1_pass;
extern double gs_w1_tprime, gs_w1_tmulti;
extern double gs_pbits, gs_obits;
extern ulong gs_n_inv, gs_n_prime, gs_n_multi;
extern double gs_t_prime, gs_t_multi;
extern double gs_pinv_pred, gs_pprime_pred;
extern ulong gs_sq_iter, gs_n_sq;
extern double gs_t_sq, gs_rbits;
extern double gs_sq_pinv_pred;
extern double gs_tests_pred;
extern uint gs_rc, gs_xi, gs_pp;

extern FILE *gs_file(void);
extern void gs_prep_record(uint nbits, const t_ct_work *w, double dt);
extern void gs_pprep_record(uint nbits, int res, double dt);
extern void gs_count_record(const t_cc *c, double charged);
extern double gs_now(void);
extern double gs_rel(void);
extern void gs_rec_start(uint lvl, ulong p);
extern void gs_rec_prime(uint lvl, ulong p);
extern void gs_rec_end(uint lvl);
extern void gs_gate(
    uint lvl, uint vi, uint x, uint ti, ulong p, ulong cap, double rw,
    uint sq, bool walk
);
extern void gs_walk_setup(
    mpz_t **q, uint *need_prime, uint npc, uint *need_other, uint noc,
    t_mod *inv, uint inv_count, uint nqc
);
extern double gs_square_pinv(
    t_mod *inv, uint inv_count, t_results *xr, mpz_t qq, mpz_t o, uint g,
    mpz_t endr
);
extern void trace_walk_v(
    t_level *cur_level, mpz_t start, void (*inner)(t_level *, mpz_t)
);
extern void trace_walk_1_set(
    t_level *prev_level, t_level *cur_level, uint vi, ulong plow,
    ulong phigh, uint x,
    void (*inner)(t_level *, t_level *, uint, ulong, ulong, uint)
);

/* time a test stage into *acc, if VB_STAGE */
static inline double gs_stage_start(void) {
    return VB(VB_STAGE) ? gs_now() : 0;
}
static inline void gs_stage_add(double *acc, double t0) {
    if (VB(VB_STAGE))
        *acc += gs_now() - t0;
}
/* count, and time a test stage: the counts are cheap, so always kept */
#   define GS_INC(c) (++(c))
#   define GS_STAGE(acc, test) ({ \
        double gs_st0_ = gs_stage_start(); \
        bool gs_sr_ = (test); \
        gs_stage_add(&(acc), gs_st0_); \
        gs_sr_; \
    })
#   define GS_ORIGIN(c) (gs_origin = (c))
#else
#   define VB(bits) 0
#   define GS_INC(c)
#   define GS_STAGE(acc, test) (test)
#   define GS_ORIGIN(c)
#endif

#endif
