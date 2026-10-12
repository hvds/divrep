/* The mocks for calibration (a MOCK build): see mock.h. */

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <errno.h>
#include <math.h>
#include <time.h>

#include "coulint.h"
#include "coulfact.h"
#include "rootmod.h"
#include "coultau.h"
#include "coulcost.h"
#include "mock.h"

/* The walk mock: calibration-only stub for walk_v(). Everything up to
 * the iteration loops runs for real; the loops themselves are replaced
 * by their expected cost (see coulcost.c), added to g_mock_spent_s, so
 * that a run reports real non-walk time plus modelled walk time,
 * deterministically. Never use for a real search: no candidate is ever
 * tested. Pell walks (nqc > 1) still run for real.
 *
 * walk_1_set() runs for real over its first MOCK_W1S_PREFIX primes, but
 * with each surviving prime's tests replaced by their expected cost;
 * the rest of its primes are then charged per prime, plus the prefix's
 * rate of survivors times the cost of the checks and its mean test cost.
 *
 * The mock's own CPU time is measured and discounted.
 */
#define MOCK_W1S_PREFIX 10000
#define MOCK_W1S_SAMPLE 8

/* the cost table's scalar costs (see cm_const()), read by mock_init() */
static double mc[CM_COUNT];
#define MC(i) (mc[i])

/* the logarithmic integral, for counting primes */
static double mock_li(double x) {
    if (x < 2)
        return 0;
    double l = log(x);
    return x / l * (1 + 1 / l + 2 / (l * l));
}

/* CPU time, to measure (and discount) the mock's own overhead, and
 * time stride samples; CPU time is unaffected by other load. Not
 * CLOCK_PROCESS_CPUTIME_ID: while a CPU-time timer is armed (as the
 * diag and log timers are, see init_time()), Linux samples the process
 * clock from the thread group's cputimer, which advances only at
 * scheduler ticks (4ms here), so almost every interval read as 0 or
 * one tick. The thread clock stays precise, and pcoul has one thread.
 * It is a system call (~0.25us here).
 */
static inline double mock_clock(void) {
    struct timespec ts;
    clock_gettime(CLOCK_THREAD_CPUTIME_ID, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

/* The CPU time of one mock_clock(), which is itself overhead: an interval
 * between two reads includes about one read's worth, and about one more
 * falls outside it.
 */
double g_mock_read = 0;
static void mock_clock_init(void) {
    double t0 = mock_clock(), t1 = t0;
    for (uint i = 0; i < 1000; ++i)
        t1 = mock_clock();
    g_mock_read = (t1 - t0) / 1000;
}

/* The leaf mock: also stub innermost recurse loops - those whose
 * children all walk. A loop is pending from when it starts; if the
 * first child to survive apply_single() walks (a linear walk), that
 * walk's per-iteration cost and expected size are recorded, and when the
 * loop resumes, the remaining primes up to its cap are replaced by
 * c_prime each plus their walks, whose size scales as (p0/p)^(x-1). If
 * the first child recurses, or does anything not yet modelled, the loop
 * runs normally.
 * If instead the first child walks a fixed power (nqc == 1), whose cost
 * varies too irregularly with p to integrate, the loop is sampled: above
 * ML_SQ_PMIN (so that the cost changes little across a stride) every
 * ML_STRIDE-th prime runs normally, and each prime in between is only
 * iterated, and charged c_prime_sq plus the walk cost of the last prime
 * run. If a sampled child recurses, the loop reverts to running normally.
 * Loops above the leaves (ML_NOT) are strided likewise above ML_SQ_PMIN:
 * of each ML_STRIDE * ML_BLOCK primes the first ML_BLOCK run normally,
 * timed together (real time, and mock cost charged within them), and
 * each of the rest is charged their mean. Timing a block rather than a
 * single child spreads the cost of the clock reads over ML_BLOCK
 * children.
 * With $MOCK_LEAF_OFF set, leaf loops are identified but not stubbed,
 * so that comparing the two gives c_prime and c_prime_sq (the counts of
 * primes stubbed are reported at the end of the run).
 */
#define ML_MAX 256
#define ML_PENDING 1
#define ML_LEAF 2
#define ML_NOT 3
#define ML_SQ 4
#define ML_STRIDE 16
#define ML_BLOCK 8
#define ML_SQ_PMIN 65536
static uint ml_state[ML_MAX];
static double ml_iter_cost[ML_MAX], ml_r0[ML_MAX];
static ulong ml_p0[ML_MAX];
static ulong ml_count[ML_MAX];      /* ML_SQ: primes seen */
static double ml_walk[ML_MAX];      /* ML_SQ: walk cost of last prime run */
/* Striding other loops: whether a sample block is running and how many
 * of its children have finished, when it started (clock, mock overhead
 * and mock cost so far), and the mean cost of the last complete block.
 */
static bool ml_samp[ML_MAX], ml_have[ML_MAX];
static uint ml_nsamp[ML_MAX];
static double ml_t0[ML_MAX], ml_ov0[ML_MAX], ml_m0[ML_MAX], ml_cost[ML_MAX];
double g_ml_strided = 0;    /* primes skipped by striding */
double g_ml_primes = 0;     /* primes stubbed, for calibrating cprime */
double g_ml_primes_sq = 0;  /* likewise, for cprime_sq */
bool g_ml_off = 0;          /* $MOCK_LEAF_OFF: leave leaf loops real */

/* the cost of the rest of a leaf loop at level lvl, after prime p */
static double ml_stub_cost(uint lvl, ulong p, ulong limp, uint x) {
    if (limp <= p)
        return 0;
    double np = mock_li(limp) - mock_li(p);
    double s = x - 1, cost = MC(CM_CPRIME) * np;
    g_ml_primes += np;
    double sum = 0, step = pow(2.0, 0.125);
    for (double lo = p; lo < limp; lo *= step) {
        double hi = lo * step;
        if (hi > limp)
            hi = limp;
        double n = mock_li(hi) - mock_li(lo);
        if (n > 0)
            sum += n * pow(ml_p0[lvl] / sqrt(lo * hi), s);
    }
    return cost + ml_iter_cost[lvl] * ml_r0[lvl] * sum;
}

/* The leaf mock also stubs the ends of loops whose primes apply_single()
 * would almost all reject on rq > zmax (CHECK_OVERFLOW), as in deep
 * recursion. With r = prev->rq < a = prev->aq, allocating p^(x-1) gives
 * rq = r + a.t for t roughly uniform mod p^(x-1), rejected when
 * t > T = floor((zmax - r) / a); so a prime passes with chance about
 * (T + 1) / p^(x-1), and for x >= 3 the rest of the loop from p expects
 * S <= (T + 1) / ((x - 2) p^(x-2) ln p) survivors. Once p passes the P*
 * where S falls to MR_TAIL_EPS (at once if r > zmax), the loop is ended
 * and its remaining primes (by li) are charged c_tail each, dropping
 * the few survivors expected: the bias is at most S times the cost of
 * a survivor. With $MOCK_TAIL_OFF set, such loops run to the end, so
 * that comparing the two gives c_tail (the count of primes stubbed is
 * reported at the end).
 */
#define MR_TAIL_EPS 0.01
static mpz_t mr_t;
static bool mr_set[ML_MAX];     /* mr_pstar[] is set for this loop */
static uint mr_seen[ML_MAX];    /* seen_best when it was set */
static double mr_pstar[ML_MAX]; /* P* */
double g_mr_tail = 0;           /* primes stubbed in loop tails */
bool g_mr_tail_off = 0;         /* $MOCK_TAIL_OFF: run loop tails */

static void mr_setup(uint lvl, t_level *prev, uint x) {
    mr_set[lvl] = 1;
    mr_seen[lvl] = seen_best;
    mr_pstar[lvl] = INFINITY;
    mpz_sub(mr_t, zmax, prev->rq);
    if (mpz_sgn(mr_t) < 0) {
        mr_pstar[lvl] = 0;
        return;
    }
    if (x < 3)
        return;
    /* Solve (T + 1) / ((x - 2) p^(x-2) ln p) = MR_TAIL_EPS for p: the
     * fixed point converges fast, since ln p changes slowly.
     */
    mpz_fdiv_q(mr_t, mr_t, prev->aq);
    double c = (mpz_get_d(mr_t) + 1) / ((x - 2) * MR_TAIL_EPS);
    double e = 1.0 / (x - 2), p = pow(c, e);
    for (uint i = 0; i < 4; ++i)
        p = pow(c / log(p < 3 ? 3 : p), e);
    mr_pstar[lvl] = p;
}

/* TRUE if the rest of the loop at lvl from p is stubbed */
static bool mr_tail(uint lvl, t_level *prev, t_level *cur, ulong p) {
    if (!mr_set[lvl] || mr_seen[lvl] != seen_best)
        mr_setup(lvl, prev, cur->x);
    if (p <= mr_pstar[lvl])
        return 0;
    double np = mock_li(cur->limp) - mock_li(p) + 1;
    if (np < 1)
        np = 1;
    g_mr_tail += np;
    g_mock_spent_s += np * MC(CM_CTAIL);
    return 1;
}

/* what the mocks stubbed, at the end of a run or on -Ld timeout */
void mock_report(void) {
    report("368 mock %.3fs (overhead %.3fs)", g_mock_spent_s,
            g_mock_overhead_s);
    report(", leaf primes %.0f, sq primes %.0f, strided %.0f", g_ml_primes,
            g_ml_primes_sq, g_ml_strided);
    report(", tail %.0f", g_mr_tail);
    report("\n");
}

/* Set up the mocks, once options are handled. */
void mock_init(void) {
    mock_clock_init();
    for (uint i = 0; i < CM_COUNT; ++i)
        mc[i] = cm_const(i);
    mpz_init(mr_t);
    g_ml_off = getenv("MOCK_LEAF_OFF") != NULL;
    g_mr_tail_off = getenv("MOCK_TAIL_OFF") != NULL;
}

/* walk_v(): for a linear walk or one of a single fixed power (nqc < 2),
 * charge its modelled cost instead of walking, and return TRUE. The
 * arguments are those walk_v() has prepared: the positions' q, target
 * tau and classification, the inverse filter, and for a linear walk
 * the range of ati.
 */
bool mock_walk_v(
    t_level *cur_level, mpz_t **q, uint *t, uint nqc, uint *need_square,
    uint *need_prime, uint npc, uint *need_other, uint noc, t_mod *inv,
    uint inv_count, mpz_t ati, mpz_t end
) {
    if (nqc >= 2)
        return 0;
    double mo0 = mock_clock();
    double cost;
    uint L = cur_level->level;
    if (nqc == 0) {
        ulong mock_alloc[k * maxfact];
        t_cmwalk wk;
        cm_walk_init(&wk, CMK_LINEAR, mock_alloc, k, 0, 0);
        double tail = cm_tail(log2(mpz_get_d(zmax)), q, t, need_prime, npc,
                need_other, noc, &wk, inv, inv_count, NULL);
        double tests;
        double pinv = cm_pinv(inv, inv_count, &tests);
        double iters = mpz_get_d(end) - mpz_get_d(ati) + 1;
        if (iters < 0)
            iters = 0;
        double loop = MC(CM_LOOP0) + tests * MC(CM_LOOPTEST);
        cost = iters * (loop + pinv * tail);
        if (L < ML_MAX && ml_state[L] == ML_PENDING) {
            ml_state[L] = ML_LEAF;
            ml_iter_cost[L] = loop + pinv * tail;
            ml_r0[L] = (mpz_get_d(zmax) - mpz_get_d(zmin))
                    / mpz_get_d(cur_level->aq);
            ml_p0[L] = cur_level->p;
        }
    } else {
        if (L < ML_MAX && ml_state[L] == ML_PENDING) {
            ml_state[L] = ML_SQ;
            ml_count[L] = 1;
            ml_walk[L] = 0;
        }
        uint sqi = need_square[0];
        uint xi = divisors[t[sqi]].gcddm;
        t_results *xr = res_array(cur_level->level);
        double qd = mpz_get_d(*q[sqi]), qqd = mpz_get_d(wv_qq[sqi]);
        double hi = pow((mpz_get_d(zmax) + TYPE_OFFSET(sqi)) / qd, 1.0 / xi);
        double lo = (mpz_sgn(zmin) > 0)
                ? pow((mpz_get_d(zmin) + TYPE_OFFSET(sqi)) / qd, 1.0 / xi) : 0;
        double iters = xr->count * (hi - lo) / qqd;
        double rbits = log2(hi > 2 ? hi : 2);
        double setup = MC(CM_SQSETUP) * (iters < 1 ? iters : 1);
        cost = setup + iters * cm_root_cost(log2(mpz_get_d(zmax)), rbits, q,
                t, sqi, need_prime, npc, need_other, noc, inv, inv_count);
        if (L < ML_MAX && ml_state[L] == ML_SQ)
            ml_walk[L] += cost;
    }
    g_mock_spent_s += cost;
    g_mock_overhead_s += mock_clock() - mo0 + g_mock_read;
    return 1;
}

/* walk_1_set(): its first MOCK_W1S_PREFIX primes run for real, the tests
 * of those that reach them modelled (every MOCK_W1S_SAMPLE-th exactly, the
 * rest charged the mean), and the rest of the primes charged at the
 * prefix's rates. walk_1_set() is not reentrant, so the state is here.
 */
static struct {
    mpz_t **q;
    ulong *alloc;
    t_cmwalk wk;
    ulong primes, pass, nsample;
    double tailsum;
} mw1;

void mock_w1s_start(void) {
    if (!mw1.q) {
        mw1.q = malloc(k * sizeof(mpz_t *));
        mw1.alloc = malloc(k * maxfact * sizeof(ulong));
    }
    for (uint vj = 0; vj < k; ++vj)
        mw1.q[vj] = &value[vj].alloc[cur_vlevel[vj] - 1].q;
    mw1.primes = mw1.pass = mw1.nsample = 0;
    mw1.tailsum = 0;
    cm_walk_init(&mw1.wk, CMK_EXACT, mw1.alloc, k, 0, 0);
}

/* the next prime p, up to phigh: TRUE if the rest has been charged */
bool mock_w1s_prime(ulong p, ulong phigh) {
    if (++mw1.primes <= MOCK_W1S_PREFIX)
        return 0;
    double rem = mock_li(phigh) - mock_li(p) + 1;
    double rate = (double)mw1.pass / MOCK_W1S_PREFIX;
    double tail = mw1.nsample ? mw1.tailsum / mw1.nsample : 0;
    g_mock_spent_s += rem * (MC(CM_W1SITER)
            + rate * (MC(CM_W1SCHECK) + tail));
    return 1;
}

/* A prime reaching the tests, with the value at w1_v and the positions'
 * values in wv_o[].
 */
void mock_w1s_pass(
    mpz_t v, uint *t, uint *need_prime, uint npc, uint *need_other, uint noc
) {
    ++mw1.pass;
    /* tested in the same order as walk_1_set() */
    oc_t = t;
    qsort(need_other, noc, sizeof(uint), &other_comparator);
    if ((mw1.pass - 1) % MOCK_W1S_SAMPLE == 0) {
        double mo0 = mock_clock();
        mw1.tailsum += cm_tail(log2(mpz_get_d(v)), mw1.q, t, need_prime,
                npc, need_other, noc, &mw1.wk, NULL, 0, NULL);
        ++mw1.nsample;
        g_mock_overhead_s += mock_clock() - mo0 + g_mock_read;
    }
    g_mock_spent_s += mw1.tailsum / mw1.nsample;
}

/* walk_1_set() from the loop at this level: not a leaf loop */
void mock_leaf_w1s(uint level) {
    if (level < ML_MAX && ml_state[level] == ML_PENDING)
        ml_state[level] = ML_NOT;
}

/* recurse() starts a loop at this level */
void mock_loop_start(uint level) {
    if (level < ML_MAX) {
        mr_set[level] = 0;
        ml_state[level] = ML_PENDING;
        ml_count[level] = 0;
        ml_samp[level] = ml_have[level] = 0;
    }
    if (level >= 1 && level - 1 < ML_MAX
            && (ml_state[level - 1] == ML_PENDING
                || ml_state[level - 1] == ML_SQ))
        ml_state[level - 1] = ML_NOT;
}

/* recurse() resumes the loop at this level: TRUE if it is a leaf loop,
 * now charged in full.
 */
bool mock_loop_leaf(uint level, t_level *cur_level) {
    if (level >= ML_MAX || ml_state[level] != ML_LEAF || g_ml_off)
        return 0;
    g_mock_spent_s += ml_stub_cost(level, cur_level->p, cur_level->limp,
            cur_level->x);
    ml_state[level] = 0;
    return 1;
}

/* recurse() has the next prime p for the loop at this level: go on with
 * it, skip it (charged), or end the loop (its tail charged).
 */
e_mock_loop mock_loop_prime(
    uint level, t_level *prev_level, t_level *cur_level, ulong p
) {
    if (level >= ML_MAX)
        return MOCK_LOOP_GO;
#ifdef CHECK_OVERFLOW
    if (!g_mr_tail_off && mr_tail(level, prev_level, cur_level, p))
        return MOCK_LOOP_END;
#endif
    if (g_ml_off)
        return MOCK_LOOP_GO;
    if (ml_state[level] == ML_SQ) {
        if (p > ML_SQ_PMIN && ml_count[level]++ % ML_STRIDE) {
            g_mock_spent_s += MC(CM_CPRIMESQ) + ml_walk[level];
            ++g_ml_primes_sq;
            return MOCK_LOOP_SKIP;
        }
        ml_walk[level] = 0;
    }
    if (ml_state[level] == ML_NOT) {
        /* The child just finished was in a sample block: when the block
         * is complete, take its mean cost, real and mocked, less the
         * mock's own overhead (including the clock reads bracketing it).
         */
        if (ml_samp[level] && ++ml_nsamp[level] == ML_BLOCK) {
            ml_cost[level] = ((mock_clock() - ml_t0[level]) - g_mock_read
                    - (g_mock_overhead_s - ml_ov0[level])
                    + (g_mock_spent_s - ml_m0[level])) / ML_BLOCK;
            if (ml_cost[level] < 0)
                ml_cost[level] = 0;
            g_mock_overhead_s += g_mock_read;
            ml_samp[level] = 0;
            ml_have[level] = 1;
        }
        if (p > ML_SQ_PMIN) {
            ulong pos = ml_count[level]++ % (ML_STRIDE * ML_BLOCK);
            if (ml_have[level] && pos >= ML_BLOCK) {
                g_mock_spent_s += ml_cost[level];
                ++g_ml_strided;
                return MOCK_LOOP_SKIP;
            }
            if (!ml_samp[level]) {
                ml_samp[level] = 1;
                ml_nsamp[level] = 0;
                g_mock_overhead_s += g_mock_read;
                ml_t0[level] = mock_clock();
                ml_ov0[level] = g_mock_overhead_s;
                ml_m0[level] = g_mock_spent_s;
            }
        }
    }
    return MOCK_LOOP_GO;
}
