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
 * level ahead. Walking now costs GR_SETUP plus its Z/aq iterations
 * (Z = zmax - zmin) at the cost per iteration learnt for its level;
 * recursing costs GR_APPLY per prime p tried, plus the walks of the
 * children as if every one walks: Z/(aq.p^{x-1}) iterations, or if that
 * is below 1, one iteration with that chance, the sums over primes in
 * closed form. At the leaf recursion that estimate is right
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
#define GQ_RSCALE 1.0
#define GQ_DEFIT 1e-6       /* per root, until a level has samples */
double gq_t[GR_MAXL], gq_i[GR_MAXL];
uint gq_n[GR_MAXL];

static inline double gr_now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_THREAD_CPUTIME_ID, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

/* The cost of what the run has done, counted rather than timed, so that
 * learning depends neither on the machine's load nor on luck, and two
 * identical runs make identical choices: walk iterations and inverse
 * filter entries tested, primes tried by walk_1_set() and the recursion
 * (those reaching apply_single() below a fixed square at cprimesq), each
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
    return cc.lin_walks * c[CM_LINSETUP]
            + (cc.lin_iter + cc.pell_iter) * c[CM_LOOP0]
            + cc.lin_inv * c[CM_LOOPTEST]
            + cc.sq_walks * c[CM_SQSETUP] + cc.sq_iter * c[CM_SQLOOP0]
            + cc.sq_inv * c[CM_SQTEST]
            + cc.w1s_prime * c[CM_W1SITER] + cc.w1s_check * c[CM_W1SCHECK]
            + cc.rec_prime * c[CM_CPRIME]
            + cc.rec_sq * (c[CM_CPRIMESQ] - c[CM_CPRIME])
            + cc.rec_applied * c[CM_CAPPLY]
            + cc.test + ct_test_charged + ct_ladder_charged + cc.base;
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
static inline double gr_iters(t_level *lv) {
    return (mpz_get_d(zmax) - mpz_get_d(zmin)) / mpz_get_d(lv->aq);
}

/* The roots a walk at the node lv is expected to visit, with one square
 * fixed: those of its residue classes mod qq = aq / q up to the root of
 * zmax / q, where q is what is allocated at the square (as the gain
 * gate's r_walk, less what lies below zmin).
 */
static double gq_roots(t_level *lv) {
    uint sql = cur_vlevel[sq0];
    double g = sqg[sql - 1];
    double q = mpz_get_d(value[sq0].alloc[sql - 1].q);
    double hi = pow(mpz_get_d(zmax) / q, 1 / g);
    double lo = pow(mpz_get_d(zmin) / q, 1 / g);
    return (hi - lo) * q * res_array(lv->level)->count / mpz_get_d(lv->aq);
}

/* The walks seen, for sampling them. A walk resumed on recovery is not
 * seen again: it was counted when it began, and what is left of it is
 * not a whole walk to learn from.
 */
static uint gr_ctr = 0;
void walk_v_gr(t_level *cur_level, mpz_t start) {
    uint L = cur_level->level;
    /* below a fixed square, only where the gate can use it */
    bool fsq = (cur_level->have_square == 1 && kern_batch());
    if (!auto_level || (cur_level->have_square && !fsq) || L >= GR_MAXL
            || mpz_sgn(start) != 0 || (++gr_ctr % GR_SAMPLE)) {
        walk_v_inner(cur_level, start);
        return;
    }
    if (fsq) {
        double za = gq_roots(cur_level);
        double t0 = gr_clock();
        walk_v_inner(cur_level, start);
        gq_t[L] += gr_clock() - t0 - GQ_SETUP;
        gq_i[L] += za;
        ++gq_n[L];
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

/* likewise the cost per root of a walk at level L below a fixed square */
static double gq_cit(uint L) {
    for (uint d = 0; d < GR_MAXL; ++d) {
        uint l = L + d;
        if (l < GR_MAXL && gq_n[l] >= GR_SAMPLE && gq_i[l] > 0)
            return gq_t[l] > 0 ? gq_t[l] / gq_i[l] : GQ_DEFIT;
        l = L - d;
        if (d <= L && gq_n[l] >= GR_SAMPLE && gq_i[l] > 0)
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
 * p^{x-1} for p in [p, cap]? Walking is estimated to cost w0; rw and
 * rr correct the estimates of walking and recursing.
 */
static bool gr_walk(
    t_level *prev_level, ulong p, ulong cap, uint x, double w0, double rw,
    double rr
) {
    if (cap < p)
        return 0;
    double W = w0 * rw;
    /* quick answer when the walk costs less than trying the primes */
    if (W < (gr_li(cap) - gr_li(p) + 1) * GR_APPLY)
        return 1;
    return W < gr_recurse(prev_level, p, cap, x) * rr;
}

/* The same below one fixed square, for a loop at a position that -k
 * applies to (see gq_costable()).
 * A prime q has d roots of the fixed power with chance 1/d, so a child
 * expects the node's roots over q^{x-1}, and the walks of the children
 * sum as in gr_recurse(). Only primes that reach apply_single() have
 * their roots extended, and about half of those are then walked: all up
 * to the root of zl = zmax / aq, and above it only those giving a least
 * v_0 within zmax, each with chance zl / q^{x-1}.
 */
static double gq_recurse(t_level *prev_level, ulong p, ulong cap, uint x) {
    uint L = prev_level->level;
    double za = gq_roots(prev_level);
    double zl = mpz_get_d(zmax) / mpz_get_d(prev_level->aq);
    double ci = gq_cit(L + 1);
    double s = x - 1, a = (p < 2) ? 2 : p, b = cap;
    double np = gr_li(b) - gr_li(a) + 1;
    double ql = pow(zl, 1 / s);
    double mA = (ql < b) ? ql : b, mB = (ql > a) ? ql : a;
    double ns = ((mA > a) ? gr_li(mA) - gr_li(a) : 0)
            + zl * gr_psum(mB, b, s);
    return np * GR_APPLY + ns * (GQ_PRIME + (GQ_APPLY + GQ_SETUP) / 2)
            + ci * za * gr_psum(a, b, s);
}

/* the estimated cost of walking the node at lv now, likewise */
static inline double gq_wcost(t_level *lv) {
    return GQ_SETUP + gq_cit(lv->level) * gq_roots(lv);
}

/* as gr_walk() below one fixed square */
static bool gq_walk(
    t_level *prev_level, ulong p, ulong cap, uint x, double w0, double rw,
    double rr
) {
    if (cap < p)
        return 0;
    double W = w0 * rw;
    if (W < (gr_li(cap) - gr_li(p) + 1) * GR_APPLY)
        return 1;
    return W < gq_recurse(prev_level, p, cap, x) * rr;
}

/* -ja2 learns the actual cost of what it chose against the estimate, in
 * six parts: walking the node, walk_1_set(), recursing, and recursing
 * where a square is left; and below one fixed square, walking and
 * recursing. A walk is timed whole, and a position chosen one x at a
 * time, each x being of a single part. The estimates are then corrected
 * by the ratios found.
 * Walking and walk_1_set() are off by small factors, learnt per level.
 * Recursing is estimated as if every child walks, which is about right
 * for the smallest nodes and far too high for the rest, by a factor
 * that depends on the size of the node and hardly on its level: on
 * D(96,4) -j4 -x1e16 actual/estimated was 0.6 for nodes that would cost
 * 0.1-1ms to walk, 0.06 at 0.1-1s and 0.004 at 1000s, and nodes of all
 * those sizes share a level. So those two parts are learnt by the
 * node's estimated cost to walk, in bands of a factor of 8 from
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
#define JA_PARTS 6
static const char ja_tag[JA_PARTS - JA_LPARTS + 1] = "rsf";
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
/* the ratios in use at the node being costed */
static double ja_rr = 1, ja_rs = 1, ja_r1 = 1, ja_rq = 1;
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

/* The ratio for recursing (part JA_RECURSE or JA_SQUARE) from a node
 * estimated to cost w to walk.
 */
static double ja_rsize(uint part, double w) {
    if (ja_stale) {
        for (uint s = 0; s < JA_PARTS - JA_LPARTS; ++s)
            for (uint b = 0; b < JA_NB; ++b) {
                double r0 = (b <= JA_BFULL) ? 1 : ja_SR[b - 1][s]
                        * ((s == JA_QREC - JA_LPARTS) ? JA_QDECAY : JA_BDECAY);
                ja_SR[b][s] = (ja_SA[b][s] + JA_PRIOR * r0)
                        / (ja_SE[b][s] + JA_PRIOR);
            }
        ja_stale = 0;
    }
    return ja_SR[ja_band(w)][part - JA_LPARTS];
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
void ja_learnt(t_level *lp) {
    ja_learn(lp->level - 1, lp->ja_wp, lp->ja_ew, lp->ja_ew,
            gr_clock() - lp->ja_t0);
    lp->ja_t0 = 0;
}

/* the current x of the position chosen at lp is done: learn from it */
void ja_learnx(t_level *lp) {
    uint di = lp->di;
    if (di < ja_nd)
        ja_learn(lp->level - 1, lp->ja_xp[di], lp->ja_w, lp->ja_ex[di],
                gr_clock() - lp->ja_xt0);
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
 * [p, cap], but never less than the cost of trying each of them. The
 * ratio learnt for large nodes can be tiny (below 1e-20 on D(1176,3)),
 * and scaled by it alone the loop's own cost vanished, so that the
 * choice between positions rested on noise: a q^2 loop over 1e9 primes
 * was costed at under 1us and chosen, taking over 1000s.
 */
static inline double ja_floored(double c, ulong p, ulong cap) {
    double fl = (gr_li(cap) - gr_li(p) + 1) * GR_APPLY;
    return (c < fl) ? fl : c;
}

#define JA_MIN_WALK 100e-6  /* least cost of walking, to choose by cost */
#define JA_W1S 0.1e-6       /* walk_1_set(), per prime iterated */
#define JA_W1T 2e-6         /* walk_1_set(), per prime reaching its tests */
/* -ja2: the estimated cost of choosing position vi at the node at
 * prev_level, recursing over every x of t_i with every resulting case
 * walked, as for the -ja1 gate, corrected by the ratios learnt. Returns
 * HUGE_VAL if some x would walk the node (so walking it now is cheaper),
 * or stops early once past bound; sets *blind if some x is outside the
 * model (where the loop above may flip), when the result is meaningless.
 */
static double ja_cost(
    t_level *prev_level, t_level *cur_level, uint vi, double bound,
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
        ulong limp = limit_p(cur_level, vi, x, nextt);
        switch (classify_x(prev_level, vi, x, p, limp)) {
          case XR_WALK:
            return HUGE_VAL;
          case XR_SKIP:
            continue;
          case XR_FLIP:
            *blind = 1;
            return 0;
          case XR_WALK1: {
            /* not at a position that -k applies to, so not costed */
            if (prev_level->have_square) {
                *blind = 1;
                return 0;
            }
            /* About 1 in m of the primes pass the check mod m = aq / q_i
             * to reach the tests.
             */
            double m = mpz_get_d(prev_level->aq) / mpz_get_d(ap->q);
            double c1 = (gr_li(limp) - gr_li(p) + 1)
                    * (JA_W1S + JA_W1T / (m < 1 ? 1 : m));
            ja_cx[di] = c1;
            ja_cp[di] = JA_W1;
            total += c1 * ja_r1;
            break;
          }
          case XR_RANGE: {
            ulong cap = (limp_cap && limp_cap < limp) ? limp_cap : limp;
            if (prev_level->have_square) {
                if (!gq_costable(vi)) {
                    *blind = 1;
                    return 0;
                }
                if (cap > p) {
                    double cr = gq_recurse(prev_level, p, cap, x);
                    ja_cx[di] = cr;
                    ja_cp[di] = JA_QREC;
                    total += cr * ja_rq;
                }
                break;
            }
            if (ti == 2 * x * x && can_flip(x)) {
                *blind = 1;
                return 0;
            }
            /* Leaving a square, the children are costed as if they did
             * not, which overestimates them, but learning corrects that
             * by a ratio of its own.
             */
            bool sq = ((ti / x) & 1) && !(ti & 1);
            if (cap > p) {
                double cr = gr_recurse(prev_level, p, cap, x);
                ja_cx[di] = cr;
                ja_cp[di] = sq ? JA_SQUARE : JA_RECURSE;
                total += ja_floored(cr * (sq ? ja_rs : ja_rr), p, cap);
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

/* true if positions vi and vj are alike, so cost the same */
static inline bool ja_alike(uint vi, uint vj) {
    t_allocation *ai = &value[vi].alloc[cur_vlevel[vi] - 1];
    t_allocation *aj = &value[vj].alloc[cur_vlevel[vj] - 1];
    return ai->t == aj->t && ai->p == aj->p && ai->x == aj->x
            && maxforce[vi] == maxforce[vj] && mpz_cmp(ai->q, aj->q) == 0;
}

/* -ja2: given the strategy's choice sv of position at the node at
 * prev_level, return the position to choose by estimated cost, or
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
uint ja_choose(t_level *prev_level, t_level *cur_level, uint sv) {
    uint L = prev_level->level;
    if (!ja_nd) {
        ja_nd = divisors[n].alldiv;
        ja_cx = malloc(ja_nd * sizeof(double));
        ja_bx = malloc(ja_nd * sizeof(double));
        ja_cp = malloc(ja_nd);
        ja_bp = malloc(ja_nd);
    }
    bool fsq = (prev_level->have_square != 0);
    double W0 = fsq ? gq_wcost(prev_level) : gr_wcost(prev_level);
    double W = W0 * ja_ratio(L, fsq ? JA_QWALK : JA_WALK);
    /* not worth choosing: leave it to the strategy and the gate */
    if (W < JA_MIN_WALK && auto_level >= 2)
        return sv;
    ja_rr = ja_rsize(JA_RECURSE, W0);
    ja_rs = ja_rsize(JA_SQUARE, W0);
    ja_rq = ja_rsize(JA_QREC, W0);
    ja_r1 = ja_ratio(L, JA_W1);
    bool blind, sblind;
    double sT = ja_cost(prev_level, cur_level, sv, HUGE_VAL, &sblind);
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
                || (need_maxp && divisors[ti].alldiv == 2)))
            continue;
        if (kern_passed(vi))
            continue;
        /* A position alike to one before it (or to the strategy's
         * choice) cannot improve on it.
         */
        bool seen = ja_alike(vi, sv);
        for (uint vj = 0; !seen && vj < vi; ++vj)
            if (ja_alike(vi, vj))
                seen = 1;
        if (seen)
            continue;
        ++neval;
        double T = ja_cost(prev_level, cur_level, vi, bT, &blind);
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
            cur_level->ja_ew = W0;
            cur_level->ja_wp = fsq ? JA_QWALK : JA_WALK;
            cur_level->ja_t0 = gr_clock();
        } else {
            if (!cur_level->ja_ex) {
                cur_level->ja_ex = malloc(ja_nd * sizeof(double));
                cur_level->ja_xp = malloc(ja_nd);
            }
            memcpy(cur_level->ja_ex, ja_bx, ja_nd * sizeof(double));
            memcpy(cur_level->ja_xp, ja_bp, ja_nd);
            cur_level->ja_w = W0;
            cur_level->ja_on = 1;
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

/* The gate under -ja: true if prev_level should be walked, rather than
 * recursed into by allocating p^{x-1} at cur_level's v_i for each prime
 * after p up to cap, given do_walk as the gain heuristics decided it.
 */
bool ja_gate(
    t_level *prev_level, t_level *cur_level, ulong p, ulong cap, bool do_walk
) {
    uint ti = cur_level->ti;
    uint x = divisors[ti].div[cur_level->di];
    uint vi = cur_level->vi;

    /* -ja1, except a loop whose children can flip (t = 2q^2 allocating
     * p^{q-1}), or with a square fixed any but those at a position that
     * -k applies to, which keep the gain.
     */
    if (!prev_level->have_square && !(ti == 2 * x * x && can_flip(x))) {
        uint L = prev_level->level;
        bool sq = ((ti / x) & 1) && !(ti & 1);
        /* under -ja2, as corrected by what it has learnt */
        double w0 = gr_wcost(prev_level);
        double rw = (auto_level >= 2) ? ja_ratio(L, JA_WALK) : 1;
        double rr = (auto_level >= 2)
                ? ja_rsize(sq ? JA_SQUARE : JA_RECURSE, w0) : GR_RSCALE;
        do_walk = gr_walk(prev_level, p, cap, x, w0, rw, rr);
    } else if (prev_level->have_square == 1 && gq_costable(vi)) {
        /* likewise below one fixed square */
        uint L = prev_level->level;
        double w0 = gq_wcost(prev_level);
        double rw = (auto_level >= 2) ? ja_ratio(L, JA_QWALK) : 1;
        double rr = (auto_level >= 2) ? ja_rsize(JA_QREC, w0) : GQ_RSCALE;
        do_walk = gq_walk(prev_level, p, cap, x, w0, rw, rr);
    }
    return do_walk;
}
