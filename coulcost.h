#ifndef COULCOST_H
#define COULCOST_H

/* The cost table (see multibench-table) and the models built on it, in
 * every build: -ja and -ka count the cost of what a run does, and price
 * what it might do, from them. See coulcost.c.
 */

#include "coul.h"

/* The expected cost of tau_multi_run() on these values, or -1 without a
 * cost table: in every build, for learning costs.
 */
extern double cm_ladder_cost(uint count, t_tm *tm);
/* The same table's prices of the tests and its scalar costs, for
 * counting the cost of what a run does.
 */
extern bool cm_have_table(void);
/* Once the log is open, report what was wrong with the table. */
extern void cm_table_report(void);
extern const char cm_default_table[];   /* timings.c, from timings */
extern const char *cm_table_sha(const char *section);
extern double cm_table_ghz(const char *section);
extern double cm_price_prime(mpz_t n);
extern double cm_const(uint which);
extern double cm_prep_price(uint nbits, const t_ct_work *w);
extern double cm_pprep_price(uint nbits, int res);
extern double cm_ptest_price(uint nbits, bool prime);
/* Report each D series priced beyond its data (see coulcost.c). */
extern void cm_dreport(void);
enum { CM_LOOP0, CM_LOOPTEST, CM_SQSETUP, CM_SQLOOP0, CM_SQTEST,
        CM_CPRIME, CM_CPRIMESQ, CM_W1SITER, CM_W1SCHECK, CM_CTAIL,
        CM_LINSETUP, CM_CAPPLY, CM_LINSETUPINV, CM_SQSETUPRES, CM_W1SCALL,
        CM_CFAIL, CM_COUNT };

/* The modelled cost per root of walking a single fixed power, or a
 * negative value if the table cannot price it.
 */
extern double cm_root_price(double z, mpz_t **q, uint *t, uint sqi,
        uint *need_prime, uint npc, uint *need_other, uint noc, t_mod *inv,
        uint inv_count);

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

/* In-situ cost samples: with $COST_SAMPLES naming a file, every run
 * times a sample of what the recursion loops do, and on exit appends the
 * statistics to that file as D rows (see cs_write()), for multibench-
 * table -S to add to a cost table. The run itself never reads them, so
 * its decisions are the same whether it samples or not.
 * A prime a loop tries is the interval between its counts of
 * cc.rec_prime, or for one that reaches apply_single() up to that call,
 * which is a sample of its own, by its outcome. Since a prime costs much
 * less than reading the clock, primes are timed in windows of up to
 * CS_WINDOW in a row, ending early at such a call, for their mean.
 * Samples are by class and by the limbs of the aq of the node the loop
 * extends (see CR_COUNT, cr_limbs()).
 */
#define CS_EVERY 4096   /* a window of primes begun once in this many */
#define CS_WINDOW 64    /* primes in a window */
#define CS_AEVERY 256   /* one apply_single() call sampled in this many */
extern bool cs_on;
extern uint cs_left, cs_aleft;
extern double work_clock(void);
extern void cs_init(void);
extern void cs_add(uint which, uint l, double t0, uint k);
extern void cs_write(void);
/* the sample to start, if this is the one in every to take, else 0 */
static inline double cs_start(uint *left, uint every) {
    if (--*left)
        return 0;
    *left = every;
    return work_clock();
}
/* At each count of cc.rec_prime: if a window of primes is open, count
 * the prime it has seen to the end, and close it if full (*t is then
 * 0); else maybe open one, of class c.
 */
static inline void cs_prime(double *t, uint *k, uint *cls, uint c,
        uint l) {
    if (*t) {
        if (++*k == CS_WINDOW) {
            cs_add(*cls, l, *t, *k);
            *t = 0;
        }
    } else if ((*t = cs_start(&cs_left, CS_EVERY))) {
        *k = 0;
        *cls = c;
    }
}
/* Before a call of apply_single(): close any window of primes, counting
 * the one now reaching the call.
 */
static inline void cs_close(double *t, uint k, uint cls, uint l) {
    if (*t) {
        cs_add(cls, l, *t, k + 1);
        *t = 0;
    }
}

#endif
