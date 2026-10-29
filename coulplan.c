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
#define GR_FAIL 1.1e-6
#define GR_RSCALE 0.25
#define GR_DEFIT 400e-9     /* per iteration, until a level has samples */
double gr_t[GR_MAXL], gr_i[GR_MAXL];
uint gr_n[GR_MAXL];
/* Those of the costs above that the cost table also has: when costs are
 * counted (see gr_clock()), the table's, so that a walk learns what was
 * counted for it less exactly the setup that was counted; else the
 * defaults. See gr_init().
 */
static double gr_setup = GR_SETUP, gr_apply = GR_APPLY, gr_fail = GR_FAIL;
/* and the setup per inverse-filter entry of a linear walk, 0 without a
 * table
 */
static double gr_setupinv = 0;
/* -ja2: what walk_1_set() costs per prime iterated, per prime passing the
 * check mod aq / q_i, and per call, the table's when costs are counted;
 * and what the tests of those passing it cost, by a rough constant.
 */
#define JA_W1S 0.1e-6
#define JA_W1T 2e-6
static double ja_w1s = JA_W1S, ja_w1c = 0, ja_w1call = 0;

/* The inverse-filter entries a linear walk of the current node sets up,
 * as walk_v() makes them: one for each prime p allocated at
 * v_i, unless p divides aq / q_i. That is so for p = 2, whose exact
 * power is folded into the modulus, and for a prime allocated at another
 * position to a higher power. (Counted so, this matched walk_v() in
 * every walk of the calibration runs.)
 */
static uint gr_ninv(void) {
    const uint *vl = cur_vlevel;
    uint n = 0;
    for (uint vi = 0; vi < k; ++vi) {
        t_allocation *ap = value[vi].alloc;
        for (uint ai = 1; ai < vl[vi]; ++ai) {
            ulong p = ap[ai].p;
            if (p == 2)
                continue;
            bool higher = 0;
            for (uint vj = 0; vj < k && !higher; ++vj) {
                if (vj == vi)
                    continue;
                t_allocation *bp = value[vj].alloc;
                for (uint aj = 1; aj < vl[vj]; ++aj)
                    if (bp[aj].p == p && bp[aj].x > ap[ai].x) {
                        higher = 1;
                        break;
                    }
            }
            if (!higher)
                ++n;
        }
    }
    return n;
}

/* The setup of a linear walk of the current node, with more entries for
 * a child's; not counting them without a cost for them.
 */
static inline double gr_wsetup(uint more) {
    return gr_setupinv ? gr_setup + gr_setupinv * (gr_ninv() + more)
            : gr_setup;
}

static inline double gr_now(void) {
    return work_clock();
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
    return cc.lin_walks * c[CM_LINSETUP] + cc.lin_setinv * c[CM_LINSETUPINV]
            + (cc.lin_iter + cc.pell_iter) * c[CM_LOOP0]
            + cc.lin_inv * c[CM_LOOPTEST]
            + cc.sq_walks * c[CM_SQSETUP] + cc.sq_setres * c[CM_SQSETUPRES]
            + cc.sq_iter * c[CM_SQLOOP0]
            + cc.sq_inv * c[CM_SQTEST]
            + cc.w1s_prime * c[CM_W1SITER] + cc.w1s_check * c[CM_W1SCHECK]
            + cc.w1s_calls * c[CM_W1SCALL]
            + cc.rec_prime * c[CM_CPRIME]
            + cc.rec_applied * c[CM_CAPPLY]
            + cc.rec_fail * c[CM_CFAIL]
            + cc.test + ct_test_charged + ct_ladder_charged;
}

/* Settle the costs the gates share with the cost table, once it is
 * known whether costs are counted.
 */
void gr_init(void) {
    if (!cc.on)
        return;
    gr_setup = cm_const(CM_LINSETUP);
    gr_apply = cm_const(CM_CPRIME);
    gr_fail = cm_const(CM_CFAIL);
    gr_setupinv = cm_const(CM_LINSETUPINV);
    ja_w1s = cm_const(CM_W1SITER);
    ja_w1c = cm_const(CM_W1SCHECK);
    ja_w1call = cm_const(CM_W1SCALL);
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
static inline double gr_iters(t_node *lv) {
    return (mpz_get_d(zmax) - mpz_get_d(zmin)) / mpz_get_d(lv->aq);
}

/* A sampled walk's cost less its setup, at level L (kind 'q' below a
 * fixed square, else 'r'), from the clock read before and after it.
 * With costs counted it cannot be negative, since what was counted for
 * the walk includes the setup taken off: report the first that is
 * (beyond the rounding of the totals) as a bug, and learn it as
 * nothing. Timed, it can be, from noise.
 */
static double gr_less_setup(char kind, uint L, double t0, double t1,
        double setup) {
    double dt = t1 - t0 - setup;
    if (!cc.on || dt >= 0)
        return dt;
    static bool warned = 0;
    if (!warned && dt < -1e-12 * t1) {
        report("000 -ja: %c walk at level %u learnt cost %g, setup %g\n",
                kind, L, dt, setup);
        warned = 1;
    }
    return 0;
}

/* the walks seen, for sampling them */
static uint gr_ctr = 0;
void walk_v_gr(t_node *cur_node, mpz_t start) {
    uint L = cur_node->level;
    if (!auto_level || cur_node->have_square || L >= GR_MAXL
            || mpz_sgn(start) != 0 || (++gr_ctr % GR_SAMPLE)) {
        walk_v_inner(cur_node, start);
        return;
    }
    double za = gr_iters(cur_node);
    ulong w0 = cc.lin_walks, s0 = cc.lin_setinv;
    double t0 = gr_clock();
    walk_v_inner(cur_node, start);
    double setup = cc.on ? (cc.lin_walks - w0) * gr_setup
            + (cc.lin_setinv - s0) * gr_setupinv : gr_setup;
    gr_t[L] += gr_less_setup('r', L, t0, gr_clock(), setup);
    gr_i[L] += za;
    ++gr_n[L];
}

/* The cost per iteration of a walk at level L, from the nearest level
 * with enough samples: GR_SAMPLE walks, expected to make GR_MINI
 * iterations between them. Walks expected to make almost none cost
 * little beyond their setup, which is taken off, so learnt from those
 * alone the cost per iteration comes out near 0, and the gate would
 * then walk a node of millions (as 30 4 did, under -ka).
 */
#define GR_MINI 100
static double gr_cit(uint L) {
    for (uint d = 0; d < GR_MAXL; ++d) {
        uint l = L + d;
        if (l < GR_MAXL && gr_n[l] >= GR_SAMPLE && gr_i[l] >= GR_MINI)
            return gr_t[l] > 0 ? gr_t[l] / gr_i[l] : GR_DEFIT;
        l = L - d;
        if (d <= L && gr_n[l] >= GR_SAMPLE && gr_i[l] >= GR_MINI)
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

/* Of the primes in [lo, hi] for p^{x-1} below lv, those expected to
 * reach apply_single() and be rejected there, rather than in single
 * limbs by reject_single(). That needs r = (zmax - rq) / aq in a limb,
 * and then decides by the least CRT multiple mod q^e, the largest power
 * up to q^{x-1} below 2^61: exactly if that is q^{x-1}, else rejecting
 * unless the multiple is at most r mod q^e, which has chance about
 * (r + 1) / q^e, at most (r + 1).q / 2^61. It does nothing for primes
 * that lead to a child, so lo should be beyond those.
 */
static double gr_nfail(t_node *lv, double lo, double hi, uint x) {
    if (hi <= lo)
        return 0;
    double n = gr_li(hi) - gr_li(lo);
    double r = (mpz_get_d(zmax) - mpz_get_d(lv->rq)) / mpz_get_d(lv->aq);
    if (r < 0 || r >= 0x1p64)
        return n;
    /* exact for q^{x-1} below 2^61 */
    if (x <= 3)
        return 0;
    double qf = pow(0x1p61, 1.0 / (x - 1));
    if (hi <= qf)
        return 0;
    if (lo < qf)
        lo = qf;
    /* above qc none is rejected in single limbs */
    double r1 = r + 1, qc = 0x1p61 / r1, f = 0;
    if (hi > qc) {
        double l = (lo > qc) ? lo : qc;
        f += gr_li(hi) - gr_li(l);
        hi = l;
    }
    if (hi > lo)
        f += r1 / 0x1p61 * gr_psum(lo, hi, -1);
    return f;
}

/* What a loop over p^{x-1} for p in [p, cap] below prev_node costs for
 * itself: gr_apply per prime tried, and gr_fail more for each that only
 * apply_single() rejects, which are among those beyond the last to lead
 * to a child.
 */
static double gr_own(t_node *prev_node, ulong p, ulong cap, uint x) {
    double a = (p < 2) ? 2 : p, b = cap;
    double q1 = pow(gr_iters(prev_node), 1.0 / (x - 1));
    return (gr_li(b) - gr_li(a) + 1) * gr_apply
            + gr_fail * gr_nfail(prev_node, (q1 > a) ? q1 : a, b, x);
}

/* The estimated cost of recursing from the node at prev_node over
 * p^{x-1} for p in [p, cap], every child walking.
 */
static double gr_recurse(t_node *prev_node, ulong p, ulong cap, uint x) {
    uint L = prev_node->level;
    double za = gr_iters(prev_node);
    double ci = gr_cit(L + 1);
    double s = x - 1, a = (p < 2) ? 2 : p, b = cap;
    /* below q1 a child walks at least one iteration */
    double q1 = pow(za, 1 / s);
    double mA = (q1 < b) ? q1 : b, mB = (q1 > a) ? q1 : a;
    double nA = (mA > a) ? gr_li(mA) - gr_li(a) : 0;
    /* a child sets up an entry more than this node */
    double cs = gr_wsetup(1);
    return gr_own(prev_node, p, cap, x) + nA * cs
            + ci * za * gr_psum(a, mA, s) + (cs + ci) * za * gr_psum(mB, b, s);
}

/* the estimated cost of walking the node at lv now */
static inline double gr_wcost(t_node *lv) {
    return gr_wsetup(0) + gr_cit(lv->level) * gr_iters(lv);
}

/* -ja1: walk the node at prev_node now, rather than recurse over
 * p^{x-1} for p in [p, cap]?
 */
static bool gr_walk(t_node *prev_node, ulong p, ulong cap, uint x) {
    if (cap < p)
        return 0;
    double W = gr_wcost(prev_node);
    /* quick answer when the walk costs less than trying the primes */
    if (W < gr_own(prev_node, p, cap, x))
        return 1;
    return W < gr_recurse(prev_node, p, cap, x) * GR_RSCALE;
}

/* The gate under -ja: true if prev_node should be walked, rather than
 * recursed into by allocating p^{x-1} at cur_act's v_i for each prime
 * after p up to cap, given do_walk as the gain heuristics decided it.
 */
bool ja_gate(
    t_node *prev_node, t_act *cur_act, ulong p, ulong cap, bool do_walk
) {
    uint ti = cur_act->ti;
    uint x = divisors[ti].div[cur_act->di];

    /* -ja1, except a loop whose children can flip (t = 2q^2 allocating
     * p^{q-1}), or with a square fixed, which keep the gain.
     */
    if (!prev_node->have_square && !(ti == 2 * x * x && can_flip(x)))
        do_walk = gr_walk(prev_node, p, cap, x);
    return do_walk;
}
