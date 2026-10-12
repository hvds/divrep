/* The planner: estimates of what parts of the search would cost, and
 * the choices pcoul makes by them (-ja, -ka). See coulplan.h.
 */

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <ctype.h>

#include "coulint.h"
#include "coulfact.h"
#include "rootmod.h"
#include "coultau.h"
#include "coulcost.h"
#include "coulplan.h"
#include "mock.h"
#include "trace.h"

/* -ja1: the gate decides whether to walk a node or recurse over its
 * next allocation by estimated cost rather than by gain, for nodes with
 * no fixed square, looking one level ahead. Walking now costs GR_SETUP
 * plus its Z/aq iterations (Z = zmax - zmin) at the cost per iteration
 * learnt for its level; recursing costs GR_APPLY per prime p tried, plus
 * the walks of the children as if every one walks: Z/(aq.p^{x-1})
 * iterations, or if that is below 1, one iteration with that chance, the
 * sums over primes in closed form. At the leaf recursion that estimate
 * is right (actual/estimated 0.84-1.07 on D(96,8), D(48,10)); higher up
 * it overestimates recursion, so the estimate is scaled by GR_RSCALE.
 * The cost per iteration is learnt per level from 1 in GR_SAMPLE of the
 * walks made, by the cost counted for each (see gr_clock()).
 */
#define GR_MAXL 64
#define GR_SAMPLE 8
#define GR_SETUP 2e-6
#define GR_APPLY 0.12e-6
#define GR_RSCALE 0.25
#define GR_DEFIT 400e-9     /* per iteration, until a level has samples */
double gr_t[GR_MAXL], gr_i[GR_MAXL];
uint gr_n[GR_MAXL];

static inline double gr_now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_THREAD_CPUTIME_ID, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

/* The cost of what the run has done, counted rather than timed, so that
 * learning depends neither on the machine's load nor on luck, and two
 * identical runs make identical choices: walk iterations and inverse
 * filter entries tested, primes tried by walk_1_set() and the recursion,
 * each at its cost from the cost table; each test's preparation by where
 * its trial division stopped, and the factoring ladder at its expected
 * cost (see cm_prep_price(), cm_pprep_price(), cm_price_prime() and
 * cm_ladder_cost()).
 */
double cc_work(void) {
    static double c[CM_COUNT];
    static bool init = 0;
    if (!init) {
        for (uint i = 0; i < CM_COUNT; ++i)
            c[i] = cm_const(i);
        init = 1;
    }
    return cc.lin_walks * c[CM_LINSETUP]
            + (cc.lin_iter + cc.pell_iter) * c[CM_LOOP0]
            + cc.lin_inv * c[CM_LOOPTEST]
            + cc.sq_walks * c[CM_SQSETUP] + cc.sq_iter * c[CM_SQLOOP0]
            + cc.sq_inv * c[CM_SQTEST]
            + cc.w1s_prime * c[CM_W1SITER] + cc.w1s_check * c[CM_W1SCHECK]
            + cc.rec_prime * c[CM_CPRIME]
            + cc.rec_applied * c[CM_CAPPLY]
            + cc.test + ct_test_charged + ct_ladder_charged;
}

/* The clock for learning costs: the counted cost given a cost table,
 * else thread CPU time, with the mocks' own time replaced by what they
 * model.
 */
static inline double gr_clock(void) {
    if (cc.on)
        return cc_work();
    return gr_now() - g_mock_overhead_s + g_mock_spent_s;
}

/* The iterations of a linear walk at the node lv: the range walked
 * over its modulus (the gain gate's r_walk has zmax alone without
 * LARGE_MIN, but the walk covers zmin..zmax either way).
 */
static inline double gr_iters(t_level *lv) {
    return (mpz_get_d(zmax) - mpz_get_d(zmin)) / mpz_get_d(lv->aq);
}

/* the walks seen, for sampling them */
static uint gr_ctr = 0;
void walk_v_gr(t_level *cur_level, mpz_t start) {
    uint L = cur_level->level;
    if (!auto_level || cur_level->have_square || L >= GR_MAXL
            || mpz_sgn(start) != 0 || (++gr_ctr % GR_SAMPLE)) {
        walk_v_inner(cur_level, start);
        return;
    }
    double za = gr_iters(cur_level);
    double t0 = gr_clock();
    walk_v_inner(cur_level, start);
    double dt = gr_clock() - t0 - GR_SETUP;
    gr_t[L] += dt;
    gr_i[L] += za;
    ++gr_n[L];
}

/* The cost per iteration of a walk at level L, from the nearest level
 * with enough samples.
 */
static double gr_cit(uint L) {
    for (uint d = 0; d < GR_MAXL; ++d) {
        uint l = L + d;
        if (l < GR_MAXL && gr_n[l] >= GR_SAMPLE && gr_i[l] > 0)
            return gr_t[l] > 0 ? gr_t[l] / gr_i[l] : GR_DEFIT;
        l = L - d;
        if (d <= L && gr_n[l] >= GR_SAMPLE && gr_i[l] > 0)
            return gr_t[l] > 0 ? gr_t[l] / gr_i[l] : GR_DEFIT;
    }
    return GR_DEFIT;
}

/* the number of primes up to x, estimated */
static double gr_li(double x) {
    if (x < 2)
        return 0;
    double l = log(x);
    return x / l * (1 + 1 / l + 2 / (l * l));
}

/* The sum over primes q in [lo, hi] of q^-s, as the integral of
 * t^-s / ln t, by Simpson's rule in ln t.
 */
static double gr_psum(double lo, double hi, double s) {
    if (lo < 2)
        lo = 2;
    if (hi <= lo)
        return 0;
    double a = log(lo), b = log(hi), h = (b - a) / 16, sum = 0;
    for (uint i = 0; i <= 16; ++i) {
        double y = a + i * h;
        double f = exp(y * (1 - s)) / y;
        sum += f * ((i == 0 || i == 16) ? 1 : (i & 1) ? 4 : 2);
    }
    return sum * h / 3;
}

/* The estimated cost of recursing from the node at prev_level over
 * p^{x-1} for p in [p, cap], every child walking.
 */
static double gr_recurse(t_level *prev_level, ulong p, ulong cap, uint x) {
    uint L = prev_level->level;
    double za = gr_iters(prev_level);
    double ci = gr_cit(L + 1);
    double s = x - 1, a = (p < 2) ? 2 : p, b = cap;
    double np = gr_li(b) - gr_li(a) + 1;
    /* below q1 a child walks at least one iteration */
    double q1 = pow(za, 1 / s);
    double mA = (q1 < b) ? q1 : b, mB = (q1 > a) ? q1 : a;
    double nA = (mA > a) ? gr_li(mA) - gr_li(a) : 0;
    return np * GR_APPLY + nA * GR_SETUP + ci * za * gr_psum(a, mA, s)
            + (GR_SETUP + ci) * za * gr_psum(mB, b, s);
}

/* the estimated cost of walking the node at lv now */
static inline double gr_wcost(t_level *lv) {
    return GR_SETUP + gr_cit(lv->level) * gr_iters(lv);
}

/* -ja1: walk the node at prev_level now, rather than recurse over
 * p^{x-1} for p in [p, cap]?
 */
static bool gr_walk(t_level *prev_level, ulong p, ulong cap, uint x) {
    if (cap < p)
        return 0;
    double W = gr_wcost(prev_level);
    /* quick answer when the walk costs less than trying the primes */
    if (W < (gr_li(cap) - gr_li(p) + 1) * GR_APPLY)
        return 1;
    return W < gr_recurse(prev_level, p, cap, x) * GR_RSCALE;
}

/* The gate under -ja: true if prev_level should be walked, rather than
 * recursed into by allocating p^{x-1} at cur_level's v_i for each prime
 * after p up to cap, given do_walk as the gain heuristics decided it.
 */
bool ja_gate(
    t_level *prev_level, t_level *cur_level, ulong p, ulong cap, bool do_walk
) {
    uint ti = cur_level->ti;
    uint x = divisors[ti].div[cur_level->di];

    /* -ja1, except a loop whose children can flip (t = 2q^2 allocating
     * p^{q-1}), or with a square fixed, which keep the gain.
     */
    if (!prev_level->have_square && !(ti == 2 * x * x && can_flip(x)))
        do_walk = gr_walk(prev_level, p, cap, x);
    return do_walk;
}
