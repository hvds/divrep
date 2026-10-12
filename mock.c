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

/* what the mocks stubbed, at the end of a run or on -Ld timeout */
void mock_report(void) {
    report("368 mock %.3fs (overhead %.3fs)", g_mock_spent_s,
            g_mock_overhead_s);
    report("\n");
}

/* Set up the mocks, once options are handled. */
void mock_init(void) {
    mock_clock_init();
    for (uint i = 0; i < CM_COUNT; ++i)
        mc[i] = cm_const(i);
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
    } else {
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
