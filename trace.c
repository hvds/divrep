/* Instrumentation for VERBOSE builds: see trace.h. */

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <errno.h>
#include <time.h>

#include "coulint.h"
#include "rootmod.h"
#include "trace.h"

#ifdef VERBOSE
/* The records of -dv2 (VB_GATE), written to the file named by $GATE_STATS
 * (default gate_stats.log), one line per event:
 *   G lvl vi x ti p cap rw sq dec
 *       one per walk/recurse gate decision in prep_unforced_x(): rw is
 *       r_walk (gain applied), sq prev_level->have_square, dec W or R
 *   R lvl np dt t
 *       closes a gate R decision: primes tried at that level, wall
 *       time of the whole subtree (nested R and walks included), and
 *       the time since the first record
 *   C lvl thr t
 *       an open R decision's loop first tried a prime p > thr, at time
 *       t; with the matching R record this bounds the time a -W<thr>
 *       run would have moved to walk_midp()
 *   W lvl org ati nqc dt cause rm raq inv npc noc pbits obits
 *     ninv nprime nmulti tprime tmulti pinv_pred pprime_pred
 *       one per walk_v() call. org: G=gate, F=forced (limp==0), B=best_v
 *       walk_now, M=walk_midp(), O=other. cause: M/m no minimum yet (m: minp is 0),
 *       Z residue m > zmax, E range empty from the zmin side, N
 *       nonempty. rm/raq: bit-size of m and aq relative to zmax.
 *       The rest are for the nqc == 0 sweep only: inv[] count, number
 *       of need_prime / need_other positions and their mean residual
 *       bits; how many ati passed the inverse filter, test_primes() and
 *       test_multi(); time inside test_primes() and test_multi(); and
 *       model predictions of the inverse-filter pass rate (exact, from
 *       inv[]) and of the test_primes() pass rate (prod 4.8/(b ln 2)
 *       over need_prime residuals of b bits).
 *       Then, for nqc == 1 square walks (cause S): root iterations, how
 *       many passed the square position's own test (after the inverse
 *       filter) and time in that test, the residue count, root degree,
 *       whether the square's tau is a prime power (tau_prime_test()),
 *       and log2 of the root limit. For S walks ninv counts inverse
 *       passes, nprime/tprime cover test_zprimes() only.
 *       Last, for both, the expected number of inverse-filter entries
 *       tested per iteration.
 *   F lvl oldp outer ok inner dt
 *       one per run_flip_pqsq() call: the flip point, outer primes tried
 *       and accepted by apply_single(), primes iterated by its
 *       walk_1_set() calls, and wall time
 *   X lvl vlevel dt
 *       one per walk_6x() call (STRATEGY_6X): the allocation count at
 *       v_{sq0-2} and wall time
 *   V lvl vi x primes pass tprime tmulti dt
 *       one per walk_1_set() call: primes iterated, how many passed the
 *       modular and divisibility checks to reach the tests, time inside
 *       test_1primes() and test_1multi(), and wall time
 *   P lvl tried dt
 *       one per walk_midp() call (-W): (p, vi, x) combinations tried and
 *       wall time of the whole midp phase for the batch at lvl
 *   J lvl strategy W sv sT best bT neval nblind level
 *       (with -dv8 and -ja, to the same file) one per choice of position
 *       at a node without a fixed square (see ja_choose()): the cost W
 *       (us) of walking the node, the strategy's choice sv and its cost
 *       sT (-1 if outside the model, when the choice stands), the choice
 *       by cost best (-1 to walk) and its cost bT, the positions costed
 *       and those outside the model, and the -ja level: only at -ja2 is
 *       the choice made
 * The stage timing adds two clock_gettime() calls per inverse-filter
 * pass, inflating test_primes() time slightly; the log for a busy run
 * can reach GB, so use short runs or single -I/-b batches.
 */
static FILE *gs_fp;
char gs_origin = 'O';
double gs_ati;
int gs_nqc;
/* M/m: no minimum (m: minp 0), Z: m > zmax, E: range empty from the zmin
 * side, N: nonempty range, S: a walk of one fixed power
 */
char gs_cause;
double gs_rm, gs_raq;    /* log2(m / zmax), log2(aq / zmax) */
/* per-walk structure and stage pass counts (nqc == 0 sweep only) */
uint gs_inv, gs_npc, gs_noc;
ulong gs_mp_tried;           /* walk_midp(): (p, vi, x) tried */
ulong gs_w1s_primes;         /* walk_1_set(): primes iterated */
ulong gs_w1_pass;            /* walk_1_set(): primes reaching tests */
double gs_w1_tprime, gs_w1_tmulti;   /* walk_1_set(): test times */
double gs_pbits, gs_obits;   /* mean residual bits, prime/other */
ulong gs_n_inv, gs_n_prime, gs_n_multi;
double gs_t_prime, gs_t_multi;   /* time inside test_primes/test_multi */
double gs_pinv_pred, gs_pprime_pred; /* model predictions, see walk_v */
/* nqc == 1 square walks: root iterations, passes of the square position's
 * own test, time in it, residue count, root degree, log2 of the root limit
 */
ulong gs_sq_iter, gs_n_sq;
double gs_t_sq, gs_rbits;
double gs_sq_pinv_pred;      /* inverse pass rate over root residues */
double gs_tests_pred;        /* inverse entries tested per iteration */
uint gs_rc, gs_xi, gs_pp;
static double gs_rec_t0[GS_MAXLEVEL];
static ulong gs_rec_np[GS_MAXLEVEL];
static bool gs_rec_open[GS_MAXLEVEL];
/* p thresholds for C records: when a recurse loop's p first exceeds
 * gs_thr[i], log the time, so the cost of the part of the search that a
 * -W<gs_thr[i]> run would move to walk_midp() can be measured
 */
static const ulong gs_thr[] = {
    1000, 2000, 5000, 10000, 20000, 50000, 100000, 200000, 500000,
    1000000, 2000000, 5000000, 10000000
};
#define GS_NTHR (sizeof(gs_thr) / sizeof(gs_thr[0]))
static uint gs_thr_i[GS_MAXLEVEL];
double gs_now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}
static double gs_t_base = -1;
double gs_rel(void) {
    double t = gs_now();
    if (gs_t_base < 0)
        gs_t_base = t;
    return t - gs_t_base;
}
static void gs_close(void) {
    if (gs_fp)
        fclose(gs_fp);
    gs_fp = NULL;
}
FILE *gs_file(void) {
    if (!gs_fp) {
        const char *fn = getenv("GATE_STATS");
        gs_fp = fopen(fn ? fn : "gate_stats.log", "w");
        if (!gs_fp)
            fail("GATE_STATS: cannot open output: %s", strerror(errno));
        setvbuf(gs_fp, NULL, _IOFBF, 1 << 20);
        atexit(gs_close);
    }
    return gs_fp;
}
void gs_rec_end(uint lvl) {
    if (lvl < GS_MAXLEVEL && gs_rec_open[lvl]) {
        fprintf(gs_file(), "R %u %lu %.9f %.6f\n", lvl, gs_rec_np[lvl],
                gs_now() - gs_rec_t0[lvl], gs_rel());
        gs_rec_open[lvl] = 0;
    }
}
/* Predicted inverse-filter pass rate for a square (or higher power)
 * walk. The walk visits r = r0 + j.qq for each of the root residues r0,
 * and tests ati = (r^g - o) / qq against inv[]; for a modulus m the
 * outcome depends on j mod m, so the pass rate is exact from enumerating
 * j for each r0 and each small m (r^g takes few values mod small m, so
 * ati is far from uniform), with 1 - excluded/m for large m. Returns -1
 * unless the walk is expected to make at least 1000 iterations.
 */
double gs_square_pinv(
    t_mod *inv, uint inv_count, t_results *xr, mpz_t qq, mpz_t o, uint g,
    mpz_t endr
) {
    if (mpz_get_d(endr) / mpz_get_d(qq) * xr->count < 1000)
        return -1;
    ulong mods[256];
    uint nm = 0;
    for (uint i = 0; i < inv_count && nm < 256; ++i) {
        uint j;
        for (j = 0; j < nm; ++j)
            if (mods[j] == inv[i].m)
                break;
        if (j == nm)
            mods[nm++] = inv[i].m;
    }
    mpz_t M, t, u;
    mpz_init(M); mpz_init(t); mpz_init(u);
    uint nr = xr->count > 64 ? 64 : xr->count;
    double sum = 0;
    for (uint ri = 0; ri < nr; ++ri) {
        mpz_t *r0 = &xr->r[ri * xr->count / nr];
        double prod = 1;
        for (uint mi = 0; mi < nm; ++mi) {
            ulong m = mods[mi];
            uint nex = 0;
            for (uint i = 0; i < inv_count; ++i)
                if (inv[i].m == m)
                    ++nex;
            if (m > 2000) {
                prod *= 1.0 - (double)nex / m;
                continue;
            }
            mpz_mul_ui(M, qq, m);
            uint pass = 0;
            for (ulong j = 0; j < m; ++j) {
                mpz_mul_ui(t, qq, j);
                mpz_add(t, t, *r0);
                mpz_powm_ui(t, t, g, M);
                mpz_sub(t, t, o);
                mpz_mod(t, t, M);
                mpz_fdiv_q(t, t, qq);
                ulong a = mpz_get_ui(t);
                bool excl = 0;
                for (uint i = 0; i < inv_count; ++i)
                    if (inv[i].m == m && inv[i].v == a) {
                        excl = 1;
                        break;
                    }
                if (!excl)
                    ++pass;
            }
            prod *= (double)pass / m;
        }
        sum += prod;
    }
    mpz_clear(M); mpz_clear(t); mpz_clear(u);
    return sum / nr;
}

/* the walk's structure, and the model's predictions of its pass rates,
 * for the W record
 */
void gs_walk_setup(
    mpz_t **q, uint *need_prime, uint npc, uint *need_other, uint noc,
    t_mod *inv, uint inv_count, uint nqc
) {
    gs_nqc = nqc;
    gs_inv = inv_count;
    gs_npc = npc;
    gs_noc = noc;
    double zb = mpz_sizeinbase(zmax, 2), sp = 0, so = 0;
    for (uint i = 0; i < npc; ++i)
        sp += zb - mpz_sizeinbase(*q[need_prime[i]], 2);
    for (uint i = 0; i < noc; ++i)
        so += zb - mpz_sizeinbase(*q[need_other[i]], 2);
    gs_pbits = npc ? sp / npc : 0;
    gs_obits = noc ? so / noc : 0;
    /* predicted inverse-filter pass rate: per distinct modulus m, the
     * fraction of residues mod m not excluded (entries for the same m
     * from different positions may coincide)
     */
    gs_tests_pred = 0;
    double reach = 1.0;
    for (uint i = 0; i < inv_count; ++i) {
        gs_tests_pred += reach;
        reach *= 1.0 - 1.0 / inv[i].m;
    }
    gs_pinv_pred = 1.0;
    for (uint i = 0; i < inv_count; ++i) {
        bool seen = 0;
        for (uint j = 0; j < i; ++j)
            if (inv[j].m == inv[i].m) {
                seen = 1;
                break;
            }
        if (seen)
            continue;
        uint distinct = 0;
        for (uint j = i; j < inv_count; ++j) {
            if (inv[j].m != inv[i].m)
                continue;
            bool dup = 0;
            for (uint l = i; l < j; ++l)
                if (inv[l].m == inv[j].m && inv[l].v == inv[j].v) {
                    dup = 1;
                    break;
                }
            if (!dup)
                ++distinct;
        }
        gs_pinv_pred *= 1.0 - (double)distinct / inv[i].m;
    }
    /* predicted prime-stage pass rate: each need_prime residual of b
     * bits is prime with probability ~ K / (b ln 2), K ~ 4.8
     */
    gs_pprime_pred = 1.0;
    for (uint i = 0; i < npc; ++i) {
        double b = zb - mpz_sizeinbase(*q[need_prime[i]], 2) + 0.5;
        double pp = 4.8 / (b * 0.6931472);
        gs_pprime_pred *= (pp < 1) ? pp : 1;
    }
}

/* a gate decision at level lvl (G) */
void gs_gate(
    uint lvl, uint vi, uint x, uint ti, ulong p, ulong cap, double rw,
    uint sq, bool walk
) {
    fprintf(gs_file(), "G %u %u %u %u %lu %lu %.6g %u %c\n", lvl, vi, x, ti,
            p, cap, rw, sq, walk ? 'W' : 'R');
    if (walk)
        gs_origin = 'G';
}

/* a recurse loop starts at level lvl from p (closed by an R record) */
void gs_rec_start(uint lvl, ulong p) {
    if (lvl >= GS_MAXLEVEL)
        return;
    gs_rec_end(lvl);    /* improve_max recompute: restart timing */
    gs_rec_t0[lvl] = gs_now();
    gs_rec_np[lvl] = 0;
    gs_rec_open[lvl] = 1;
    uint ti = 0;
    while (ti < GS_NTHR && gs_thr[ti] < p)
        ++ti;
    gs_thr_i[lvl] = ti;
}

/* the recurse loop at level lvl tries p (C records at thresholds) */
void gs_rec_prime(uint lvl, ulong p) {
    if (lvl >= GS_MAXLEVEL || !gs_rec_open[lvl])
        return;
    ++gs_rec_np[lvl];
    while (gs_thr_i[lvl] < GS_NTHR && p > gs_thr[gs_thr_i[lvl]]) {
        fprintf(gs_file(), "C %u %lu %.6f\n", lvl, gs_thr[gs_thr_i[lvl]],
                gs_rel());
        ++gs_thr_i[lvl];
    }
}

/* walk_v() through inner, with its W record */
void trace_walk_v(
    t_level *cur_level, mpz_t start, void (*inner)(t_level *, mpz_t)
) {
    char org = gs_origin;
    gs_origin = 'O';
    gs_ati = -1;
    gs_nqc = -1;
    gs_cause = '?';
    gs_rm = gs_raq = 0;
    gs_inv = gs_npc = gs_noc = 0;
    gs_pbits = gs_obits = 0;
    gs_n_inv = gs_n_prime = gs_n_multi = 0;
    gs_t_prime = gs_t_multi = 0;
    gs_pinv_pred = gs_pprime_pred = 0;
    gs_sq_iter = gs_n_sq = 0;
    gs_t_sq = gs_rbits = 0;
    gs_rc = gs_xi = gs_pp = 0;
    gs_sq_pinv_pred = 0;
    gs_tests_pred = 0;
    double t0 = gs_now();
    (*inner)(cur_level, start);
    double dt = gs_now() - t0;
    /* ati == -1: returned before computing a range (empty, or no
     * minimum yet)
     */
    fprintf(gs_file(), "W %u %c %.0f %d %.9f %c %.0f %.0f"
            " %u %u %u %.1f %.1f %lu %lu %lu %.9f %.9f %.5g %.5g"
            " %lu %lu %.9f %u %u %u %.1f %.5g %.3f\n",
            cur_level->level, org, gs_ati, gs_nqc, dt, gs_cause, gs_rm,
            gs_raq, gs_inv, gs_npc, gs_noc, gs_pbits, gs_obits,
            gs_n_inv, gs_n_prime, gs_n_multi, gs_t_prime, gs_t_multi,
            gs_pinv_pred, gs_pprime_pred, gs_sq_iter, gs_n_sq, gs_t_sq,
            gs_rc, gs_xi, gs_pp, gs_rbits, gs_sq_pinv_pred, gs_tests_pred);
}

/* walk_1_set() through inner, with its V record */
void trace_walk_1_set(
    t_level *prev_level, t_level *cur_level, uint vi, ulong plow,
    ulong phigh, uint x,
    void (*inner)(t_level *, t_level *, uint, ulong, ulong, uint)
) {
    ulong primes = gs_w1s_primes;
    gs_w1_pass = 0;
    gs_w1_tprime = gs_w1_tmulti = 0;
    double t0 = gs_now();
    (*inner)(prev_level, cur_level, vi, plow, phigh, x);
    fprintf(gs_file(), "V %u %u %u %lu %lu %.9f %.9f %.9f\n",
            cur_level->level, vi, x, gs_w1s_primes - primes, gs_w1_pass,
            gs_w1_tprime, gs_w1_tmulti, gs_now() - t0);
}
#endif
