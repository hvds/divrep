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
/* the price of an item of recursion work of class c, aq of l limbs */
extern double cm_rec_price(uint c, uint l);
/* Whether the table prices deep primes by path (see RP_COUNT); if so,
 * a prime of path rp for aq of l limbs with a modulus of size kp (see
 * rd_kp()) costs cm_rd_price(rp, l), plus cm_rd_mbit(rp) per bit of kp
 * and cm_rd_knee(rp) per bit of kp beyond RD_KNEE.
 */
extern bool cm_rd_have(void);
extern double cm_rd_price(uint rp, uint l);
extern double cm_rd_mbit(uint rp);
extern double cm_rd_knee(uint rp);
enum { CM_LOOP0, CM_LOOPTEST, CM_SQSETUP, CM_SQLOOP0, CM_SQTEST,
        CM_CPRIME, CM_CPRIMESQ, CM_W1SITER, CM_W1SCHECK, CM_CTAIL,
        CM_LINSETUP, CM_CAPPLY, CM_LINSETUPINV, CM_SQSETUPRES, CM_W1SCALL,
        CM_CFAIL, CM_COUNT };

/* The modelled cost per root of walking a single fixed power, or a
 * negative value if the table cannot price it.
 */
extern double cm_iter_price(double z, mpz_t **q, uint *t, uint *need_prime,
        uint npc, uint *need_other, uint noc, t_mod *inv, uint inv_count);
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
 * statistics to that file as D rows, and E rows for the deep primes by
 * path (see cs_write()), for multibench-table -S to add to a cost
 * table. The run itself never reads them, so its decisions are the
 * same whether it samples or not.
 * A prime a loop tries is timed from where the loop takes it to where
 * it leaves the checks (see CR_COUNT), which for one going on to
 * apply_single() is that call, a sample of its own by its outcome.
 * Samples are by class and by the limbs of the aq of the node the loop
 * extends (see cr_limbs()); those of the deep primes also by path (see
 * RP_COUNT), the bits of p and, on the general path, e. The clock
 * is read in user mode with the cycle counter open (see work_clock()),
 * so that a single prime can be timed; without it, reading the clock
 * costs more than a prime, and the samples of primes read high.
 */
#define CS_EVERY 1024   /* one prime sampled in this many */
#define CS_AEVERY 256   /* one apply_single() call sampled in this many */
#define CS_PPEVERY 256  /* one tau_prime_prep() call sampled in this many */
extern bool cs_on;
extern uint cs_left, cs_aleft;
extern double work_clock(void);
extern void cs_init(void);
extern double cs_add(uint which, uint l, double t0, uint k);
extern void cs_rd_add(uint rp, uint l, uint pbits, uint e, double dt);
extern void cs_write(void);
/* the sample to start, if this is the one in every to take, else 0 */
static inline double cs_start(uint *left, uint every) {
    if (--*left)
        return 0;
    *left = every;
    return work_clock();
}

#endif
