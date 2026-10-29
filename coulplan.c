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
 * no fixed square (and see gq_recurse() for those with one), looking one
 * level ahead. Walking now costs gr_setup plus its Z/aq iterations
 * (Z = zmax - zmin) at the cost per iteration learnt for its level;
 * recursing costs gr_apply per prime p tried, and gr_fail more for each
 * that only apply_single() can reject (see gr_nfail()), plus the walks
 * of the children as if every one walks: Z/(aq.p^{x-1}) iterations, or
 * if that is below 1, one iteration with that chance, the sums over
 * primes in closed form. At the leaf recursion that estimate is right
 * (actual/estimated 0.84-1.07 on D(96,8), D(48,10)); higher up it
 * overestimates recursion, so the estimate is scaled by GR_RSCALE (-ja2
 * learns the scale instead, see ja_rsize()).
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
/* Likewise below one fixed square: the cost per root of a walk, learnt
 * per level; the setup of such a walk; and what a loop there costs for
 * each prime that reaches apply_single(), where the roots are extended
 * (the cost table's sqsetup, and cprimesq less cprime).
 */
#define GQ_SETUP 1.7e-6
#define GQ_PRIME 2.2e-6
#define GQ_APPLY 0.5e-6
#define GQ_ROOT 0.6e-6      /* per root taken by reject_square() */
#define GQ_RSCALE 1.0
#define GQ_DEFIT 1e-6       /* per root, until a level has samples */
double gq_t[GR_MAXL], gq_i[GR_MAXL];
uint gq_n[GR_MAXL];
/* Those of the costs above that the cost table also has: when costs are
 * counted (see gr_clock()), the table's, so that a walk learns what was
 * counted for it less exactly the setup that was counted; else the
 * defaults. See gr_init().
 */
static double gr_setup = GR_SETUP, gr_apply = GR_APPLY, gr_fail = GR_FAIL;
static double gq_setup = GQ_SETUP, gq_prime = GQ_PRIME, gq_apply = GQ_APPLY;
/* and the setup per inverse-filter entry of a linear walk, and per root
 * residue of one below a fixed square, 0 without a table
 */
static double gr_setupinv = 0, gq_setupres = 0;
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

/* The setup of a walk below a fixed square of the node at lv, by its
 * root residues; a child of it expects as many.
 */
static inline double gq_wsetup(t_node *lv) {
    return gq_setup + gq_setupres * res_array(lv->level)->count;
}

static inline double gr_now(void) {
    return work_clock();
}

/* The cost of what the run has done, counted rather than timed, so that
 * learning depends neither on the machine's load nor on luck, and two
 * identical runs make identical choices: walk iterations and inverse
 * filter entries tested, primes tried by walk_1_set() and the recursion
 * (those reaching apply_single() below a fixed square at cprimesq, and
 * elsewhere those rejected only there at cfail more), each
 * at its cost from the cost table; each test's preparation by where
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
            + cc.rec_sq * (c[CM_CPRIMESQ] - c[CM_CPRIME])
            + cc.rec_root * GQ_ROOT
            + cc.rec_applied * c[CM_CAPPLY]
            + cc.rec_fail * c[CM_CFAIL]
            + cc.test + ct_test_charged + ct_ladder_charged + cc.base;
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
    gq_setup = cm_const(CM_SQSETUP);
    gq_prime = cm_const(CM_CPRIMESQ) - cm_const(CM_CPRIME);
    gq_apply = cm_const(CM_CAPPLY);
    gr_setupinv = cm_const(CM_LINSETUPINV);
    gq_setupres = cm_const(CM_SQSETUPRES);
    ja_w1s = cm_const(CM_W1SITER);
    ja_w1c = cm_const(CM_W1SCHECK);
    ja_w1call = cm_const(CM_W1SCALL);
}

/* The clock for learning costs: the counted cost given a cost table,
 * else thread CPU time, with the mocks' own time replaced by what they
 * model.
 */
double gr_clock(void) {
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

/* The roots a walk at the node lv is expected to visit, with one square
 * fixed: those of its residue classes mod qq = aq / q up to the root of
 * zmax / q, where q is what is allocated at the square (as the gain
 * gate's r_walk, less what lies below zmin).
 */
static double gq_roots(t_node *lv) {
    uint sql = cur_vlevel[sq0];
    double g = sqg[sql - 1];
    double q = mpz_get_d(value[sq0].alloc[sql - 1].q);
    double hi = pow(mpz_get_d(zmax) / q, 1 / g);
    double lo = pow(mpz_get_d(zmin) / q, 1 / g);
    return (hi - lo) * q * res_array(lv->level)->count / mpz_get_d(lv->aq);
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

/* The walks seen, for sampling them. A walk resumed on recovery is not
 * seen again: it was counted when it began, and what is left of it is
 * not a whole walk to learn from.
 */
static uint gr_ctr = 0;
void walk_v_gr(t_node *cur_node, mpz_t start) {
    uint L = cur_node->level;
    /* below a fixed square, only where the gate can use it */
    bool fsq = (cur_node->have_square == 1 && kern_batch());
    if (!auto_level || (cur_node->have_square && !fsq) || L >= GR_MAXL
            || mpz_sgn(start) != 0 || (++gr_ctr % GR_SAMPLE)) {
        walk_v_inner(cur_node, start);
        return;
    }
    if (fsq) {
        double za = gq_roots(cur_node);
        ulong w0 = cc.sq_walks, s0 = cc.sq_setres;
        double t0 = gr_clock();
        walk_v_inner(cur_node, start);
        /* with costs counted, the setup counted; else an estimate */
        double setup = cc.on ? (cc.sq_walks - w0) * gq_setup
                + (cc.sq_setres - s0) * gq_setupres : gq_setup;
        gq_t[L] += gr_less_setup('q', L, t0, gr_clock(), setup);
        gq_i[L] += za;
        ++gq_n[L];
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

/* likewise the cost per root of a walk at level L below a fixed square,
 * its walks expected to visit GR_MINI roots between them
 */
static double gq_cit(uint L) {
    for (uint d = 0; d < GR_MAXL; ++d) {
        uint l = L + d;
        if (l < GR_MAXL && gq_n[l] >= GR_SAMPLE && gq_i[l] >= GR_MINI)
            return gq_t[l] > 0 ? gq_t[l] / gq_i[l] : GQ_DEFIT;
        l = L - d;
        if (d <= L && gq_n[l] >= GR_SAMPLE && gq_i[l] >= GR_MINI)
            return gq_t[l] > 0 ? gq_t[l] / gq_i[l] : GQ_DEFIT;
    }
    return GQ_DEFIT;
}

/* The number of primes up to x: exact below GR_PIMAX, where the
 * asymptotic estimate is poor (and not even increasing).
 */
#define GR_PIMAX 10000
static uint *gr_pi = NULL;
static double gr_li(double x) {
    if (x < 2)
        return 0;
    if (x < GR_PIMAX) {
        if (!gr_pi) {
            gr_pi = calloc(GR_PIMAX, sizeof(uint));
            char *comp = calloc(GR_PIMAX, 1);
            uint c = 0;
            for (uint i = 2; i < GR_PIMAX; ++i) {
                if (!comp[i]) {
                    ++c;
                    for (uint j = i * i; j < GR_PIMAX; j += i)
                        comp[j] = 1;
                }
                gr_pi[i] = c;
            }
            free(comp);
        }
        return gr_pi[(uint)x];
    }
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
 * p^{x-1} for p in [p, cap]? Walking is estimated to cost w0; rw and
 * rr correct the estimates of walking and recursing.
 */
static bool gr_walk(
    t_node *prev_node, ulong p, ulong cap, uint x, double w0, double rw,
    double rr
) {
    if (cap < p)
        return 0;
    double W = w0 * rw;
    /* quick answer when the walk costs less than trying the primes */
    if (W < gr_own(prev_node, p, cap, x))
        return 1;
    return W < gr_recurse(prev_node, p, cap, x) * rr;
}

/* The same below one fixed square, for a loop at a position that -k
 * applies to (see gq_costable()).
 * A prime q has d roots of the fixed power with chance 1/d, so a child
 * expects the node's roots over q^{x-1}, and the walks of the children
 * sum as in gr_recurse(). Only primes that reach apply_single() have
 * their roots extended, and about half of those are then walked: all up
 * to the root of zl = zmax / aq, and above it only those giving a least
 * v_0 within zmax, each with chance zl / q^{x-1}.
 * For q^2 against a square, reject_square() lets through only the half
 * that can divide, each then walked, and once q^2 passes the greatest
 * root only those with a root in range, each with chance 2.endr / q^2,
 * at the cost of a root mod q for that half.
 */
static double gq_recurse(t_node *prev_node, ulong p, ulong cap, uint x) {
    uint L = prev_node->level;
    double za = gq_roots(prev_node);
    double zl = mpz_get_d(zmax) / mpz_get_d(prev_node->aq);
    double ci = gq_cit(L + 1);
    double s = x - 1, a = (p < 2) ? 2 : p, b = cap;
    double np = gr_li(b) - gr_li(a) + 1;
    double cs = gq_wsetup(prev_node);
    uint sql = cur_vlevel[sq0];
    if (x == 3 && sqg[sql - 1] == 2) {
        double endr = sqrt(mpz_get_d(zmax)
                / mpz_get_d(value[sq0].alloc[sql - 1].q));
        /* the scale that binds first, and where */
        double c = (zl < 2 * endr) ? zl : 2 * endr, qc = sqrt(c);
        double mA = (qc < b) ? qc : b, mB = (qc > a) ? qc : a;
        double ns = (((mA > a) ? gr_li(mA) - gr_li(a) : 0)
                + c * gr_psum(mB, b, s)) / 2;
        double se = sqrt(endr), mR = (se > a) ? se : a;
        double nr = (b > mR) ? (gr_li(b) - gr_li(mR)) / 2 : 0;
        return np * gr_apply + nr * GQ_ROOT
                + ns * (gq_prime + gq_apply + cs)
                + ci * za * gr_psum(a, b, s);
    }
    double ql = pow(zl, 1 / s);
    double mA = (ql < b) ? ql : b, mB = (ql > a) ? ql : a;
    double ns = ((mA > a) ? gr_li(mA) - gr_li(a) : 0)
            + zl * gr_psum(mB, b, s);
    return np * gr_apply + ns * (gq_prime + (gq_apply + cs) / 2)
            + ci * za * gr_psum(a, b, s);
}

/* the estimated cost of walking the node at lv now, likewise */
static inline double gq_wcost(t_node *lv) {
    return gq_wsetup(lv) + gq_cit(lv->level) * gq_roots(lv);
}

/* as gr_walk() below one fixed square */
static bool gq_walk(
    t_node *prev_node, ulong p, ulong cap, uint x, double w0, double rw,
    double rr
) {
    if (cap < p)
        return 0;
    double W = w0 * rw;
    if (W < (gr_li(cap) - gr_li(p) + 1) * gr_apply)
        return 1;
    return W < gq_recurse(prev_node, p, cap, x) * rr;
}

/* The estimated cost of the whole search of a batch that -k applies to,
 * for choices that must be made before it starts (see kern_state()). It
 * follows the search in the abstract: at each node the position the
 * default strategy would take; walk or recurse as the -ja1 gate would,
 * by the loop with every child walking; and the primes of each loop
 * summed, those below KE_SMALL one by one, each dividing or not, the
 * rest in bins. Costs are as for gq_recurse(), with a fixed cost per
 * root, and all is taken from zmax as given, so that a recovered run
 * chooses the same.
 */
#define KE_MAXPOS 8
#define KE_MAXSLOT 8
#define KE_SMALL 400
#define KE_BIN 1.5
#define KE_PELL 3e-6        /* the pass, per prime at each position */
#define KE_SWEEP 3e-6       /* a sweep without reject_square(), likewise */
#define KE_6X 10.7e-6       /* a STRATEGY_6X loop, per prime applied */
typedef struct {
    double Z;       /* zmax over what is allocated, and the bound of -k */
    long d;         /* offset of the square less that of this position */
    uint ns;        /* powers still to allocate, as exponents in order */
    uint e[KE_MAXSLOT];
    uint laste;     /* the last allocated, 0 if none */
    double lastp;
} t_kepos;
typedef struct {
    double roots, zl;
    uint np;
    t_kepos pos[KE_MAXPOS];
    uint nused;
    uint used[KE_MAXPOS * KE_MAXSLOT];
} t_kenode;
static double ke_root, ke_endr, ke_pmin;
static double ke_setup;     /* of a walk in the batch, see ke_root_node() */
static bool ke_high;

/* true if n is prime, for n < GR_PIMAX */
static inline bool gr_isprime(ulong n) {
    gr_li(3);
    return n >= 2 && n < GR_PIMAX && gr_pi[n] != gr_pi[n - 1];
}

/* The start for costing a loop over the primes after p below the node
 * at lp: one less than the first prime the loop will try. Primes known
 * at lp are skipped by the loop at no cost (see known_prime()), so they
 * are skipped here too, and two loops that try the same primes then
 * cost the same however their p was found.
 */
static ulong cost_start(t_node *lp, ulong p) {
    while (1) {
        ulong q = p + 1;
        while (q < GR_PIMAX && !gr_isprime(q))
            ++q;
        if (q >= GR_PIMAX)
            q = next_prime(p);
        if (!known_prime(lp, q))
            return q - 1;
        p = q;
    }
}

/* the range (lo, hi] and exponent of the next allocation at a position */
static uint ke_limit(t_kepos *kp, double *lo, double *hi) {
    uint e = kp->e[0], same = 1;
    double other = 1;
    for (uint i = 1; i < kp->ns; ++i)
        if (kp->e[i] == e)
            ++same;
        else
            other *= pow(ke_pmin, kp->e[i]);
    double L = pow(kp->Z / other, 1.0 / (e * same));
    if (maxp[e] && L > maxp[e])
        L = maxp[e];
    *hi = L;
    *lo = (kp->laste == e) ? kp->lastp : ke_pmin - 1;
    return e;
}

/* tau left at a position, and its highest prime */
static inline uint ke_tau(t_kepos *kp) {
    uint t = 2;
    for (uint i = 0; i < kp->ns; ++i)
        t *= kp->e[i] + 1;
    return t;
}

static double ke_cost(t_kenode *node, double budget);

/* the cost of walking a node */
static inline double ke_walk(t_kenode *node) {
    return GQ_SETUP + ke_root * node->roots;
}

/* The cost of the loop over the next allocation at position j, each child
 * walked, or with deep set costed in full; HUGE_VAL once past budget.
 */
static double ke_loop(t_kenode *node, uint j, bool deep, double budget) {
    t_kepos *kp = &node->pos[j];
    double lo, hi, cost = 0;
    uint e = ke_limit(kp, &lo, &hi);
    if (hi <= lo)
        return 0;
    ulong qm = 0;
    mpz_t *q = kern_q(sq0);
    bool sq = (e == 2 && ke_endr > 0);
    double a = lo;
    while (a < hi) {
        double p, c, f, b;
        if (a < KE_SMALL) {
            /* the next prime above a, on its own */
            ulong pi = (ulong)a + 1;
            while (!gr_isprime(pi))
                ++pi;
            b = pi;
            a = b;
            if (b > hi)
                break;
            bool skip = 0;
            for (uint i = 0; i < node->nused; ++i)
                if (node->used[i] == pi)
                    skip = 1;
            if (skip || mpz_fdiv_ui(nodes[cur_batch_level].aq, pi) == 0)
                continue;
            qm = mpz_fdiv_ui(*q, pi);
            ulong dm = (kp->d < 0) ? pi - (ulong)(-kp->d) % pi
                    : (ulong)kp->d % pi;
            p = pi;
            c = 1;
            f = (jacobi_u64(mulmod_u64(dm, qm, pi), pi) == 1) ? 1 : 0;
        } else {
            b = a * KE_BIN;
            if (b > hi)
                b = hi;
            c = gr_li(b) - gr_li(a);
            p = sqrt(a * b);
            f = 0.5;
            a = b;
            if (c <= 0)
                continue;
        }
        double pe = pow(p, e);
        /* those giving a least v_0 within the bound, see reject_single() */
        double s = (node->zl < pe) ? node->zl / pe : 1;
        /* those that divide with a root in range, see reject_square() */
        double r = 1;
        if (sq) {
            cost += c * gr_apply;
            if (f == 0)
                continue;
            if (pe > ke_endr) {
                cost += c * s * f * GQ_ROOT;
                if (2 * ke_endr < pe)
                    r = 2 * ke_endr / pe;
            }
            cost += c * s * f * r * gq_prime;
        } else {
            cost += c * (gr_apply + s * gq_prime);
            if (f == 0)
                continue;
        }
        t_kenode ch = *node;
        ch.roots = node->roots * 2 / pe / r;
        ch.zl = node->zl / pe;
        t_kepos *cp = &ch.pos[j];
        cp->Z /= pe;
        --cp->ns;
        memmove(cp->e, cp->e + 1, cp->ns * sizeof(cp->e[0]));
        cp->laste = e;
        cp->lastp = p;
        if (c == 1 && p < KE_SMALL)
            ch.used[ch.nused++] = (uint)p;
        double cc = deep ? ke_cost(&ch, (budget - cost) / (c * s * f * r))
                : ke_walk(&ch);
        cost += c * s * f * r * (gq_apply + cc);
        if (cost > budget)
            return HUGE_VAL;
    }
    return cost;
}

/* the position the default strategy would take at a node, KE_MAXPOS if none */
static uint ke_best(t_kenode *node) {
    uint best = KE_MAXPOS;
    for (uint j = 0; j < node->np; ++j) {
        t_kepos *kp = &node->pos[j];
        if (!kp->ns)
            continue;
        if (best == KE_MAXPOS) {
            best = j;
            continue;
        }
        t_kepos *bp = &node->pos[best];
        /* As the default strategy: by the highest prime of tau if so,
         * then the highest tau, then the most allocated.
         */
        if (ke_high && kp->e[0] != bp->e[0]) {
            if (kp->e[0] > bp->e[0])
                best = j;
            continue;
        }
        uint tj = ke_tau(kp), tb = ke_tau(bp);
        if (tj > tb || (tj == tb && kp->Z < bp->Z))
            best = j;
    }
    return best;
}

/* the cost of the subtree at a node; HUGE_VAL once past budget */
static double ke_cost(t_kenode *node, double budget) {
    double w = ke_walk(node);
    uint best = ke_best(node);
    if (best == KE_MAXPOS)
        return w;
    double lo, hi;
    ke_limit(&node->pos[best], &lo, &hi);
    if (hi <= lo || w < (gr_li(hi) - gr_li(lo)) * gr_apply)
        return w;
    if (w < ke_loop(node, best, 0, HUGE_VAL))
        return w;
    return ke_loop(node, best, 1, budget);
}

/* Set up the root of the estimate for the current batch: the node as
 * the batch leaves it, with the positions of at, each with the odd
 * power known to exceed b (1 if not known). Sets ke_endr, ke_root,
 * ke_pmin and ke_high to match.
 */
static void ke_root_node(t_kenode *root, ulong at, double b) {
    t_node *lv = &nodes[cur_batch_level];
    /* every walk of the batch expects its root residues */
    ke_setup = gq_wsetup(lv);
    double z = zmax_given;
    uint ts = kern_tau(sq0);
    ke_endr = (divisors[ts].gcddm == 2) ? sqrt(z / mpz_get_d(*kern_q(sq0)))
            : 0;
    ke_root = (divisors[ts].alldiv == 2) ? 0.7e-6 : 1.5e-6;
    for (ke_pmin = 3; mpz_fdiv_ui(lv->aq, (ulong)ke_pmin) == 0
            || !gr_isprime((ulong)ke_pmin); ++ke_pmin)
        ;
    ke_high = (nf.count > 2);
    root->roots = pow(z / mpz_get_d(*kern_q(sq0)), 1.0 / divisors[ts].gcddm)
            * mpz_get_d(*kern_q(sq0)) * res_array(lv->level)->count
            / mpz_get_d(lv->aq);
    root->zl = z / mpz_get_d(lv->aq);
    root->np = 0;
    root->nused = 0;
    for (uint vi = 0; vi < k && root->np < KE_MAXPOS; ++vi) {
        /* needs MAXK_KERN <= 64 */
        if (!((at >> vi) & 1))
            continue;
        t_kepos *kp = &root->pos[root->np++];
        kp->Z = z / mpz_get_d(*kern_q(vi)) / b;
        kp->d = (long)TYPE_OFFSET(sq0) - (long)TYPE_OFFSET(vi);
        kp->laste = 0;
        kp->lastp = 0;
        kp->ns = 0;
        /* the powers of the highest prime of tau come first */
        uint u = kern_tau(vi) / 2;
        while (u > 1 && kp->ns < KE_MAXSLOT) {
            uint h = divisors[u].high;
            kp->e[kp->ns++] = h - 1;
            u /= h;
        }
    }
}

/* The estimated cost of the current batch under -k with the positions of
 * at, including its pass and any sweep; HUGE_VAL once past budget.
 */
static double ke_batch(ulong at, double budget) {
    t_kenode root;
    ke_root_node(&root, at, kern_b);
    double cost = 0;
    for (uint j = 0; j < root.np; ++j) {
        t_kepos *kp = &root.pos[j];
        /* the pass, and the sweep of each power in turn */
        cost += KE_PELL * gr_li(kern_b);
        for (uint i = 0; need_midp && i < kp->ns; ++i) {
            uint e = kp->e[i];
            if ((i && kp->e[i - 1] == e) || !maxp[e])
                continue;
            double other = 1;
            for (uint l = 0; l < kp->ns; ++l)
                if (l != i)
                    other *= pow(ke_pmin, kp->e[l]);
            double L = pow(kp->Z / other, 1.0 / e), W = maxp[e];
            if (L <= W)
                continue;
            double np = gr_li(L) - gr_li(W);
            cost += ke_root * root.roots * pow(W, 1.0 - e) / (e - 1) / log(W);
            if (e == 2 && ke_endr > 0) {
                double re = sqrt(2 * ke_endr);
                if (re < W)
                    re = W;
                cost += np * (gr_apply + GQ_ROOT / 2)
                        + (gq_prime + ke_setup) * ((gr_li(re) - gr_li(W)) / 2
                            + ke_endr / re / log(re));
            } else
                cost += np * KE_SWEEP;
        }
    }
    if (cost > budget)
        return HUGE_VAL;
    return cost + ke_cost(&root, budget - cost);
}

/* The estimated cost of the current batch under STRATEGY_6X, given tau 6
 * left at v_i two places before the square; else 0. at gives the
 * positions -k would apply to.
 * Its loop of q^2 at v_i runs to about (zmax/8)^{1/4}, and reject_square()
 * lets through half of it up to the root of the greatest root. But as
 * best_6x() does, it gives way to the position the default strategy
 * would take if that has a lower limit: the search is then estimated as
 * for -k (see ke_batch()), over the same positions bar v_i, but with no
 * bound on their odd power, no pass and no sweep, and at most the cost
 * of walking the batch whole. The loops of q^2 at v_i that may follow
 * deeper in that search are not allowed for. As for -k, all is taken
 * from zmax as given, not from the current state of the search.
 */
static double ke_6x(ulong at) {
    uint vi = sq0 - 2;
    if (kern_tau(vi) != 6 || divisors[kern_tau(sq0)].gcddm != 2)
        return 0;
    double L = pow(zmax_given / 8, 0.25);
    double se = pow(zmax_given / mpz_get_d(*kern_q(sq0)), 0.25);
    if (se > L)
        se = L;
    double cost = gr_li(L) * (gr_apply + GQ_ROOT / 2) + gr_li(se) * KE_6X;

    t_kenode root;
    ke_root_node(&root, at & ~(1UL << vi), 1);
    uint j = ke_best(&root);
    if (j < KE_MAXPOS) {
        double lo, hi;
        ke_limit(&root.pos[j], &lo, &hi);
        if (hi < L) {
            double whole = ke_walk(&root);
            cost = ke_cost(&root, whole);
            if (cost > whole)
                cost = whole;
        }
    }
    return cost;
}

/* True if a batch that STRATEGY_6X can take should be left to it: that
 * is, unless -k at the positions in at is estimated to cost less.
 */
bool ke_prefer_6x(ulong at) {
    double c6 = (zmax_given > 0) ? ke_6x(at) : 0;
    double ck = (c6 > 0) ? ke_batch(at, c6) : HUGE_VAL;
    return !(ck < c6);
}

/* -ja2 learns the actual cost of what it chose against the estimate, in
 * nine parts: walking the node, walk_1_set(), recursing, recursing
 * where a square is left, where the children can flip, where t = 2 is
 * left, and where a higher power of 2 is left; and below one fixed
 * square, walking and recursing. A walk is timed
 * whole, and a position chosen one x at a time, each x being of a single
 * part. The estimates are then corrected by the ratios found.
 * Walking and walk_1_set() are off by small factors, learnt per level.
 * Recursing is estimated as if every child walks, which is about right
 * for the smallest nodes and far too high for the rest, by a factor
 * that depends on the size of the node and hardly on its level: on
 * D(96,4) -j4 -x1e16 actual/estimated was 0.6 for nodes that would cost
 * 0.1-1ms to walk, 0.06 at 0.1-1s and 0.004 at 1000s, and nodes of all
 * those sizes share a level. So the parts for recursing are learnt by
 * the node's estimated cost to walk, in bands of a factor of 8 from
 * 2^JA_BLOW seconds.
 * Each ratio starts from JA_PRIOR seconds of evidence at a prior ratio:
 * 1 per level; and by size, 1 up to band JA_BFULL, then JA_BDECAY of
 * the ratio in use for the band below, so that what is learnt of small
 * nodes carries up to the large ones. The first of those are chosen
 * with no evidence, yet cost the most; and recursing where walking was
 * cheaper costs little, since each child chooses again and may walk,
 * while walking where recursing was cheaper can cost far more (D(64,3)
 * -j4 -x1e15: 29s walking at level 1, 0.1s recursing).
 * Below one fixed square the trees are shallow, and the estimate of
 * recursing is close for all but the few largest nodes (D(18,5) -k1e6
 * -x1e22: actual/estimated 0.82-1.01 for nodes costing up to 1s to
 * walk, 0.03-0.3 at the root of a batch). There the prior does not
 * decay, since an optimistic one opens loops of a million primes to
 * save a walk of a fraction of a second.
 * A loop allocating p^{z-1} where t = 2z^2 is left (see can_flip()) is
 * estimated like any other: a flip below it costs little, and most of
 * its children go on elsewhere. But it is learnt apart, since its ratio
 * can differ by far from the others' (D(162,3) -x1e14: 10x theirs at
 * nodes costing 0.1-1s to walk). Its bands with no evidence start from
 * the ratio in use for recursing in the same band.
 * Likewise a loop that leaves t = 2 at its position, or a higher power
 * of 2: the estimate is furthest out where children can still recurse
 * at the position, and those can at most walk_1_set() or walk there.
 * Learnt apart, they took 5% less counted cost and CPU time over 28
 * runs (D(144,3) -x1e15 16%, D(100,4) -x1e18 10-21%, D(162,3) -x1e14
 * 12%); nothing was slower beyond noise.
 * The -ja1 gate learns nothing, and scales its estimate of recursing
 * by GR_RSCALE throughout (GQ_RSCALE below one fixed square).
 */
#define JA_PRIOR 1e-3
#define JA_WALK 0
#define JA_W1 1
#define JA_QWALK 2      /* walking below one fixed square */
#define JA_LPARTS 3     /* the parts learnt by level come first */
#define JA_RECURSE 3
#define JA_SQUARE 4
#define JA_QREC 5       /* recursing below one fixed square */
#define JA_PQSQ 6       /* recursing where the children can flip */
#define JA_TWO 7        /* recursing to leave t = 2 */
#define JA_POW2 8       /* recursing to leave a higher power of 2 */
#define JA_PARTS 9
static const char ja_tag[JA_PARTS - JA_LPARTS + 1] = "rsfpab";
#define JA_NB 24
#define JA_BLOW (-36)
#define JA_BFULL 7
#define JA_BDECAY 0.4
#define JA_QDECAY 1.0   /* likewise, for recursing below one fixed square */
static double ja_A[GR_MAXL][JA_LPARTS], ja_E[GR_MAXL][JA_LPARTS];
static double ja_SA[JA_NB][JA_PARTS - JA_LPARTS];
static double ja_SE[JA_NB][JA_PARTS - JA_LPARTS];
/* the ratios in use by size, and whether they need recalculating */
static double ja_SR[JA_NB][JA_PARTS - JA_LPARTS];
static bool ja_stale = 1;
/* the ratios in use at the node being costed, for walk_1_set() and by
 * part for recursing
 */
static double ja_r1 = 1, ja_rx[JA_PARTS - JA_LPARTS];
/* The raw estimate and part for each x, of the last position costed and
 * of the best so far.
 */
static uint ja_nd = 0;
static double *ja_cx, *ja_bx;
static unsigned char *ja_cp, *ja_bp;

/* the ratio for walking or walk_1_set() at level L */
static inline double ja_ratio(uint L, uint part) {
    if (L >= GR_MAXL)
        return 1;
    return (ja_A[L][part] + JA_PRIOR) / (ja_E[L][part] + JA_PRIOR);
}

/* the band of a node estimated to cost w to walk */
static inline uint ja_band(double w) {
    int b = (ilogb(w) - JA_BLOW) / 3;
    return (b < 0) ? 0 : (b >= JA_NB) ? JA_NB - 1 : b;
}

/* The ratio for recursing (a part from JA_RECURSE) from a node
 * estimated to cost w to walk.
 */
static double ja_rsize(uint part, double w) {
    if (ja_stale) {
        /* JA_RECURSE first, since the parts from JA_PQSQ start from it */
        for (uint s = 0; s < JA_PARTS - JA_LPARTS; ++s)
            for (uint b = 0; b < JA_NB; ++b) {
                double r0 = (s >= JA_PQSQ - JA_LPARTS)
                        ? ja_SR[b][JA_RECURSE - JA_LPARTS]
                        : (b <= JA_BFULL) ? 1 : ja_SR[b - 1][s]
                        * ((s == JA_QREC - JA_LPARTS) ? JA_QDECAY : JA_BDECAY);
                ja_SR[b][s] = (ja_SA[b][s] + JA_PRIOR * r0)
                        / (ja_SE[b][s] + JA_PRIOR);
            }
        ja_stale = 0;
    }
    return ja_SR[ja_band(w)][part - JA_LPARTS];
}

/* the part for recursing over p^{x-1} at a position with t left */
static inline uint ja_rpart(uint t, uint x) {
    if (t == 2 * x * x && can_flip(x))
        return JA_PQSQ;
    if (t / x == 2)
        return JA_TWO;
    if (ispow2_u64(t / x))
        return JA_POW2;
    return (((t / x) & 1) && !(t & 1)) ? JA_SQUARE : JA_RECURSE;
}

/* Learn from a choice at level L, at a node estimated to cost w to
 * walk, of a part estimated to cost est that cost dt.
 */
static inline void ja_learn(
    uint L, uint part, double w, double est, double dt
) {
    if (est <= 0)
        return;
    if (part >= JA_LPARTS) {
        uint b = ja_band(w);
        ja_SA[b][part - JA_LPARTS] += dt;
        ja_SE[b][part - JA_LPARTS] += est;
        ja_stale = 1;
    } else if (L < GR_MAXL) {
        ja_A[L][part] += dt;
        ja_E[L][part] += est;
    }
}

/* The 316 log line: what -ja has learnt, written before each 305 or 315
 * line, so that a run recovered from that line carries on from it
 * rather than learning afresh:
 *   316 <counted> <walks> [<level>:<t>,<i>,<n>,<A>,<E>,<A>,<E>,<A>,<E>]
 *       ... [q<level>:<t>,<i>,<n>] ... [r<e>:<A>,<E>] ... [s<e>:<A>,<E>]
 *       ... [f<e>:<A>,<E>] ...
 * with the cost counted so far (see cc_work()) and the walks seen by
 * the sampler; then for each level with anything learnt, the cost,
 * iterations and number of the walks sampled for the gate (gr_t[],
 * gr_i[], gr_n[]), and the actual and estimated cost of the walks, of
 * the walk_1_set() calls, and of the walks below one fixed square that
 * -ja2 chose (ja_A[], ja_E[]); then for each level the cost, roots and
 * number of the walks sampled below one fixed square (gq_t[], gq_i[],
 * gq_n[]); then for each band of node size with anything learnt, of
 * nodes costing from 2^e seconds to walk, the actual and estimated
 * cost of recursing (r), of recursing where a square is left (s), and
 * of recursing below one fixed square (f) (ja_SA[], ja_SE[]).
 * Costs are in seconds, with digits enough to restore each exactly.
 * What was being measured as the line was written is not recorded: the
 * recovered run learns nothing from the walk it resumes, nor from the
 * positions already chosen on the path to it.
 */
void ja_save(FILE *fp) {
    fprintf(fp, "316 %.17g %u", cc.on ? cc_work() : 0.0, gr_ctr);
    for (uint L = 0; L < GR_MAXL; ++L) {
        bool any = (gr_n[L] != 0);
        for (uint part = 0; part < JA_LPARTS; ++part)
            if (ja_A[L][part] != 0 || ja_E[L][part] != 0)
                any = 1;
        if (!any)
            continue;
        fprintf(fp, " %u:%.17g,%.17g,%u", L, gr_t[L], gr_i[L], gr_n[L]);
        for (uint part = 0; part < JA_LPARTS; ++part)
            fprintf(fp, ",%.17g,%.17g", ja_A[L][part], ja_E[L][part]);
    }
    for (uint L = 0; L < GR_MAXL; ++L)
        if (gq_n[L])
            fprintf(fp, " q%u:%.17g,%.17g,%u", L, gq_t[L], gq_i[L], gq_n[L]);
    for (uint s = 0; s < JA_PARTS - JA_LPARTS; ++s)
        for (uint b = 0; b < JA_NB; ++b)
            if (ja_SA[b][s] != 0 || ja_SE[b][s] != 0)
                fprintf(fp, " %c%d:%.17g,%.17g", ja_tag[s],
                        JA_BLOW + 3 * (int)b, ja_SA[b][s], ja_SE[b][s]);
    fprintf(fp, "\n");
}

/* restore what a 316 line records, given what follows its code */
void ja_restore(char *s) {
    char *line = s;
    double counted;
    int off = 0;
    if (sscanf(s, "%lf %u%n", &counted, &gr_ctr, &off) != 2 || off == 0)
        fail("518 could not parse learnt costs: '%s'", line);
    cc.base = counted;
    s += off;
    while (s[0] == ' ' && isdigit(s[1])) {
        uint L;
        off = 0;
        if (sscanf(s, " %u:%n", &L, &off) != 1 || off == 0 || L >= GR_MAXL)
            fail("518 could not parse learnt costs: '%s'", line);
        s += off;
        off = 0;
        if (sscanf(s, "%lf,%lf,%u%n", &gr_t[L], &gr_i[L], &gr_n[L], &off)
                != 3 || off == 0)
            fail("518 could not parse learnt costs: '%s'", line);
        s += off;
        /* a line written before JA_QWALK has fewer parts */
        for (uint part = 0; part < JA_LPARTS && s[0] == ','; ++part) {
            off = 0;
            if (sscanf(s, ",%lf,%lf%n", &ja_A[L][part], &ja_E[L][part], &off)
                    != 2 || off == 0)
                fail("518 could not parse learnt costs: '%s'", line);
            s += off;
        }
    }
    while (s[0] == ' ' && s[1] == 'q') {
        uint L;
        off = 0;
        if (sscanf(s + 2, "%u:%n", &L, &off) != 1 || off == 0 || L >= GR_MAXL)
            fail("518 could not parse learnt costs: '%s'", line);
        s += 2 + off;
        off = 0;
        if (sscanf(s, "%lf,%lf,%u%n", &gq_t[L], &gq_i[L], &gq_n[L], &off)
                != 3 || off == 0)
            fail("518 could not parse learnt costs: '%s'", line);
        s += off;
    }
    while (s[0] == ' ' && s[1] && strchr(ja_tag, s[1])) {
        uint part = strchr(ja_tag, s[1]) - ja_tag;
        int e, b;
        double A, E;
        off = 0;
        if (sscanf(s + 2, "%d:%lf,%lf%n", &e, &A, &E, &off) != 3 || off == 0)
            fail("518 could not parse learnt costs: '%s'", line);
        b = (e - JA_BLOW) / 3;
        if (e < JA_BLOW || (e - JA_BLOW) % 3 != 0 || b >= JA_NB)
            fail("518 could not parse learnt costs: '%s'", line);
        ja_SA[b][part] = A;
        ja_SE[b][part] = E;
        s += 2 + off;
    }
    ja_stale = 1;
    if (s[0] != 0 && s[0] != '\n' && s[0] != '\r')
        fail("518 could not parse learnt costs: '%s'", line);
}

/* the walk chosen at lp is done: learn from its cost */
void ja_learnt(t_act *lp) {
    ja_learn(lp->level - 1, lp->ja_wp, lp->ja_ew, lp->ja_ew,
            gr_clock() - lp->ja_t0);
    lp->ja_t0 = 0;
}

/* the current x of the position chosen at lp is done: learn from it */
void ja_learnx(t_act *lp) {
    uint di = lp->di;
    if (di < ja_nd)
        ja_learn(lp->level - 1, lp->ja_xp[di], lp->ja_w, lp->ja_ex[di],
                gr_clock() - lp->ja_xt0);
}

/* The act at lp is done, as unwinding passes it: learn from what was
 * chosen there by cost.
 */
void ja_unwind(t_act *lp) {
    if (lp->ja_t0 > 0)
        ja_learnt(lp);
    if (lp->ja_on) {
        ja_learnx(lp);
        lp->ja_on = 0;
    }
}

/* True if a loop of allocations at v_i can be costed below one fixed
 * square: only at a position that -k applies to. There the loop leaves
 * no second square, when each child would be a Pell equation, and its
 * children cannot flip; and in such a batch no strategy allocates at the
 * square, so that every child can indeed walk it. Elsewhere a child may
 * go on to walk_1_set() over every prime at the square, which the gate
 * never sees: D(6,4) -X -x1e13 ran for over 20s that way, not 0.1s.
 */
static inline bool gq_costable(uint vi) {
    return kern_at(vi);
}

/* -ja2: the corrected estimate c of recursing over every prime in
 * [p, cap] below lv, but never less than the cost of trying each of
 * them (see gr_own()). The ratio learnt for large nodes can be tiny
 * (below 1e-20 on D(1176,3)), and scaled by it alone the loop's own cost
 * vanished, so that the choice between positions rested on noise: a q^2
 * loop over 1e9 primes was costed at under 1us and chosen, taking over
 * 1000s.
 */
static inline double ja_floored(
    double c, t_node *lv, ulong p, ulong cap, uint x
) {
    double fl = gr_own(lv, p, cap, x);
    return (c < fl) ? fl : c;
}

#define JA_MIN_WALK 100e-6  /* least cost of walking, to choose by cost */
/* -ja2: the estimated cost of choosing position vi at the node at
 * prev_node, recursing over every x of t_i with every resulting case
 * walked, as for the -ja1 gate, corrected by the ratios learnt. Returns
 * HUGE_VAL if some x would walk the node (so walking it now is cheaper),
 * or stops early once past bound; sets *blind if some x is outside the
 * model (where the loop above may flip), when the result is meaningless.
 */
static double ja_cost(
    t_node *prev_node, t_act *cur_act, uint vi, double bound,
    bool *blind
) {
    t_allocation *ap = &value[vi].alloc[cur_vlevel[vi] - 1];
    uint ti = ap->t;
    t_divisors *dp = &divisors[ti];
    double total = 0;
    *blind = 0;
    /* all, since the level's x index can pass the last x of this t */
    memset(ja_cx, 0, ja_nd * sizeof(double));
    for (uint di = 0; di < dp->highdiv; ++di) {
        uint x = dp->div[di];
        uint nextt = ti / x;
        if (done_in_reverse(vi, x, nextt))
            continue;
        ulong p = start_p(vi, x);
        ulong limp = limit_p(cur_act, vi, x, nextt);
        e_xr xr = classify_x(prev_node, vi, x, p, limp);
        /* the range as the loop will try it */
        if (xr == XR_WALK1 || xr == XR_RANGE)
            p = cost_start(prev_node, p);
        switch (xr) {
          case XR_WALK:
            return HUGE_VAL;
          case XR_SKIP:
            continue;
          case XR_FLIP:
            *blind = 1;
            return 0;
          case XR_WALK1: {
            /* not at a position that -k applies to, so not costed */
            if (prev_node->have_square) {
                *blind = 1;
                return 0;
            }
            /* About 1 in m of the primes pass the check mod m = aq / q_i
             * to reach the tests.
             */
            double m = mpz_get_d(prev_node->aq) / mpz_get_d(ap->q);
            double c1 = ja_w1call + (gr_li(limp) - gr_li(p) + 1)
                    * (ja_w1s + (ja_w1c + JA_W1T) / (m < 1 ? 1 : m));
            ja_cx[di] = c1;
            ja_cp[di] = JA_W1;
            total += c1 * ja_r1;
            break;
          }
          case XR_RANGE: {
            ulong cap = (limp_cap && limp_cap < limp) ? limp_cap : limp;
            if (prev_node->have_square) {
                if (!gq_costable(vi)) {
                    *blind = 1;
                    return 0;
                }
                if (cap > p) {
                    double cr = gq_recurse(prev_node, p, cap, x);
                    ja_cx[di] = cr;
                    ja_cp[di] = JA_QREC;
                    total += cr * ja_rx[JA_QREC - JA_LPARTS];
                }
                break;
            }
            /* Leaving a square, the children are costed as if they did
             * not, which overestimates them, and likewise where they can
             * flip; learning corrects each by a ratio of its own, as it
             * does by what the loop leaves at the position (see
             * ja_rpart()).
             */
            uint part = ja_rpart(ti, x);
            if (cap > p) {
                double cr = gr_recurse(prev_node, p, cap, x);
                double r = ja_rx[part - JA_LPARTS];
                ja_cx[di] = cr;
                ja_cp[di] = part;
                total += ja_floored(cr * r, prev_node, p, cap, x);
            }
            break;
          }
        }
        if (total >= bound)
            return total;
    }
    return total;
}

/* keep the estimates by x of the last position costed as the best */
static inline void ja_swap(void) {
    double *x = ja_cx;
    ja_cx = ja_bx;
    ja_bx = x;
    unsigned char *p = ja_cp;
    ja_cp = ja_bp;
    ja_bp = p;
}

/* true if positions vi and vj are alike below lp, so cost the same */
static inline bool ja_alike(t_node *lp, uint vi, uint vj) {
    t_allocation *ai = &value[vi].alloc[cur_vlevel[vi] - 1];
    t_allocation *aj = &value[vj].alloc[cur_vlevel[vj] - 1];
    return ai->t == aj->t && ai->p == aj->p && ai->x == aj->x
            && mpz_cmp(ai->q, aj->q) == 0 && prev_x(vi) == prev_x(vj)
            && cost_start(lp, maxforce[vi]) == cost_start(lp, maxforce[vj]);
}

/* -ja2: given the strategy's choice sv of position at the node at
 * prev_node, return the position to choose by estimated cost, or
 * BV_WALK to walk the node now. Walking costs W whichever position is
 * chosen, and recursing over some x then walking is never cheaper, so
 * the choice is between walking and recursing over every x of some
 * position: W is a bound any position must beat. On equal cost, the
 * least position is chosen. Positions the model cannot cost stay
 * unchosen, unless the strategy chose one, when its choice stands.
 * Where walking would cost less than JA_MIN_WALK the strategy's choice
 * stands too, and nothing is learnt: weighing a position costs about
 * 1us (an integer root and a sum over primes for each x), and below
 * there the choice saves less than that.
 * With just -dv8 (and -ja1), it reports the choice without making it.
 */
uint ja_choose(t_node *prev_node, t_act *cur_act, uint sv) {
    uint L = prev_node->level;
    if (!ja_nd) {
        ja_nd = divisors[n].alldiv;
        ja_cx = malloc(ja_nd * sizeof(double));
        ja_bx = malloc(ja_nd * sizeof(double));
        ja_cp = malloc(ja_nd);
        ja_bp = malloc(ja_nd);
    }
    bool fsq = (prev_node->have_square != 0);
    double W0 = fsq ? gq_wcost(prev_node) : gr_wcost(prev_node);
    double W = W0 * ja_ratio(L, fsq ? JA_QWALK : JA_WALK);
    /* not worth choosing: leave it to the strategy and the gate */
    if (W < JA_MIN_WALK && auto_level >= 2)
        return sv;
    for (uint part = JA_LPARTS; part < JA_PARTS; ++part)
        ja_rx[part - JA_LPARTS] = ja_rsize(part, W0);
    ja_r1 = ja_ratio(L, JA_W1);
    bool blind, sblind;
    double sT = ja_cost(prev_node, cur_act, sv, HUGE_VAL, &sblind);
    uint best = sv, nblind = 0, neval = 1;
    double bT = sT;
    ja_swap();
    if (sblind)
        goto done;
    if (W <= bT) {
        best = BV_WALK;
        bT = W;
    }
    for (uint vi = 0; vi < k; ++vi) {
        if (vi == sv)
            continue;
        t_allocation *ap = &value[vi].alloc[cur_vlevel[vi] - 1];
        uint ti = ap->t;
        /* eligible as for the strategies */
        if (divisors[ti].high <= (kern_highpow() ? 1 : 2))
            continue;
        if ((ti & 1) && (kern_batch()
                || (prev_node->cap && divisors[ti].alldiv == 2)))
            continue;
        if (kern_passed(vi))
            continue;
        /* A position alike to one before it (or to the strategy's
         * choice) cannot improve on it.
         */
        bool seen = ja_alike(prev_node, vi, sv);
        for (uint vj = 0; !seen && vj < vi; ++vj)
            if (ja_alike(prev_node, vi, vj))
                seen = 1;
        if (seen)
            continue;
        ++neval;
        double T = ja_cost(prev_node, cur_act, vi, bT, &blind);
        if (blind) {
            ++nblind;
            continue;
        }
        if (T < bT || (T == bT && best < BV_SPECIAL && vi < best)) {
            best = vi;
            bT = T;
            ja_swap();
        }
    }
  done:
    /* time what was chosen by cost: a walk whole, a position by x */
    if (auto_level >= 2 && !sblind) {
        if (best == BV_WALK) {
            cur_act->ja_ew = W0;
            cur_act->ja_wp = fsq ? JA_QWALK : JA_WALK;
            cur_act->ja_t0 = gr_clock();
        } else {
            if (!cur_act->ja_ex) {
                cur_act->ja_ex = malloc(ja_nd * sizeof(double));
                cur_act->ja_xp = malloc(ja_nd);
            }
            memcpy(cur_act->ja_ex, ja_bx, ja_nd * sizeof(double));
            memcpy(cur_act->ja_xp, ja_bp, ja_nd);
            cur_act->ja_w = W0;
            cur_act->ja_on = 1;
        }
    }
#ifdef VERBOSE
    if (VB(VB_CHOICE))
        fprintf(gs_file(), "J %u %u %.4g %u %.4g %d %.4g %u %u %u\n",
                L, strategy, W * 1e6, sv, sblind ? -1.0
                : sT * 1e6, best < BV_SPECIAL ? (int)best : -1, bT * 1e6,
                neval, nblind, auto_level);
#endif
    return (auto_level >= 2) ? best : sv;
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
    uint vi = cur_act->vi;

    /* -ja1, except with a square fixed any but those at a position that
     * -k applies to, which keep the gain.
     */
    if (!prev_node->have_square) {
        uint L = prev_node->level;
        uint part = ja_rpart(ti, x);
        /* under -ja2, as corrected by what it has learnt */
        double w0 = gr_wcost(prev_node);
        double rw = (auto_level >= 2) ? ja_ratio(L, JA_WALK) : 1;
        double rr = (auto_level >= 2) ? ja_rsize(part, w0) : GR_RSCALE;
        do_walk = gr_walk(prev_node, cost_start(prev_node, p), cap, x,
                w0, rw, rr);
    } else if (prev_node->have_square == 1 && gq_costable(vi)) {
        /* likewise below one fixed square */
        uint L = prev_node->level;
        double w0 = gq_wcost(prev_node);
        double rw = (auto_level >= 2) ? ja_ratio(L, JA_QWALK) : 1;
        double rr = (auto_level >= 2) ? ja_rsize(JA_QREC, w0) : GQ_RSCALE;
        do_walk = gq_walk(prev_node, cost_start(prev_node, p), cap, x,
                w0, rw, rr);
    }
    return do_walk;
}
