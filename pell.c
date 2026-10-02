#include <stdlib.h>
#include <string.h>

#include "pell.h"
#include "coul.h"
#include "coultau.h"
#include "rootmod.h"

typedef enum {
    p_limit, p_ra, p_sa, p_rd, p_sd, p_n, p_e, p_m, p_q0, p_ymax,
    p_sqrte, p_cfp, p_cfq, p_cfa, p_a0, p_a1, p_b0, p_b1, p_g,
    p_x, p_y, p_zt1, p_zt2,

    E_PELLSTASH_MAX
} e_pellstash;
mpz_t *pell_stash;
static inline mpz_t *ZP(e_pellstash e) { return &pell_stash[e]; }
#define Z(e) *ZP(e)

typedef struct s_zarray {
    mpz_t *za;
    uint alloc;
    uint size;
} t_zarray;

/* solutions (x, y) in pairs, sorted by x; and the roots being tried */
t_zarray sol, roots;
uint sol_iter;

void resize_zarray(t_zarray *zap, uint size) {
    if (size > zap->alloc) {
        if (size < zap->alloc + 16)
            size = zap->alloc + 16;
        zap->za = realloc(zap->za, size * sizeof(mpz_t));
        for (uint i = zap->alloc; i < size; ++i)
            mpz_init(zap->za[i]);
        zap->alloc = size;
    }
}

void free_zarray(t_zarray *zap) {
    if (zap->alloc) {
        for (uint i = 0; i < zap->alloc; ++i)
            mpz_clear(zap->za[i]);
        free(zap->za);
    }
}

void done_pell(void) {
    for (e_pellstash e = 0; e < E_PELLSTASH_MAX; ++e)
        mpz_clear(Z(e));
    free(pell_stash);
    free_zarray(&sol);
    free_zarray(&roots);
}

void init_pell(void) {
    pell_stash = malloc(E_PELLSTASH_MAX * sizeof(mpz_t));
    for (e_pellstash e = 0; e < E_PELLSTASH_MAX; ++e)
        mpz_init(Z(e));
}

int pell_comparator(const void *va, const void *vb) {
    mpz_t *a = (mpz_t *)va, *b = (mpz_t *)vb;
    int cmp = mpz_cmp(a[0], b[0]);
    return cmp ? cmp : mpz_cmp(a[1], b[1]);
}

/* Find square-free residue and root such that n = residue . root^2.
 * It is safe to call this with residue or root the same as n.
 */
void sqfree(mpz_t residue, mpz_t root, mpz_t n) {
    factor_state fs;
    fs_init(&fs);
    mpz_set(fs.n, n);
    mpz_set_ui(residue, 1);
    mpz_set_ui(root, 1);
    while (factor_one(&fs)) {
        if (fs.e & 1)
            mpz_mul(residue, residue, fs.f);
        if (fs.e >= 2) {
            mpz_pow_ui(fs.f, fs.f, fs.e / 2);
            mpz_mul(root, root, fs.f);
        }
    }
    fs_clear(&fs);
}

/* Given u = sa.x and w = sd.y, record (x, y) if they are positive
 * integers with x within the limit.
 */
static void add_solution(mpz_t u, mpz_t w) {
    if (mpz_sgn(u) <= 0 || mpz_sgn(w) <= 0)
        return;
    if (!mpz_divisible_p(u, Z(p_sa)) || !mpz_divisible_p(w, Z(p_sd)))
        return;
    resize_zarray(&sol, sol.size + 2);
    mpz_divexact(sol.za[sol.size], u, Z(p_sa));
    mpz_divexact(sol.za[sol.size + 1], w, Z(p_sd));
    if (mpz_cmp(sol.za[sol.size], Z(p_limit)) <= 0)
        sol.size += 2;
}

/* u^2 - w^2 = n: u - w and u + w are a pair of divisors of n */
static void solve_sqdiff(void) {
    long ln = mpz_get_si(Z(p_n));
    ulong an = (ln < 0) ? -ln : ln;
    for (ulong d = 1; d * d <= an; ++d) {
        if (an % d)
            continue;
        ulong f = an / d;
        if ((d ^ f) & 1)
            continue;
        /* the larger and smaller of u, w */
        mpz_set_ui(Z(p_zt1), (f + d) / 2);
        mpz_set_ui(Z(p_zt2), (f - d) / 2);
        if (ln > 0)
            add_solution(Z(p_zt1), Z(p_zt2));
        else
            add_solution(Z(p_zt2), Z(p_zt1));
    }
}

/* X^2 - EY^2 = M, E squarefree and not 1, for X and Y coprime and Y up
 * to ymax / f, by the method of Lagrange, Matthews and Mollin: for each
 * z with z^2 == E (mod |M|), every solution with X == -zY (mod |M|) is
 * (|M|A - zB, B) for some convergent A/B of (z + sqrt(E)) / |M|, namely
 * A_{i-1}/B_{i-1} where the complete quotient (P_i + sqrt(E)) / Q_i has
 * Q_i = (-1)^i sign(M). So we need only follow the convergents as far as
 * the limit, which takes a number of steps logarithmic in it.
 * Records f times each solution, mapped back to (x, y).
 */
static void solve_coprime(ulong f, bool by_a) {
    int sign = mpz_sgn(Z(p_m));
    mpz_abs(Z(p_q0), Z(p_m));
    roots.size = 0;
    if (mpz_cmp_ui(Z(p_q0), 1) == 0) {
        resize_zarray(&roots, 1);
        mpz_set_ui(roots.za[0], 0);
        roots.size = 1;
    } else {
        allzrootmod(0, Z(p_e), 2, Z(p_q0));
        t_results *rp = res_array(0);
        resize_zarray(&roots, rp->count);
        for (uint i = 0; i < rp->count; ++i)
            mpz_set(roots.za[i], rp->r[i]);
        roots.size = rp->count;
    }

    for (uint ri = 0; ri < roots.size; ++ri) {
        mpz_set(Z(p_cfp), roots.za[ri]);
        mpz_set(Z(p_cfq), Z(p_q0));
        /* (a0, b0) is the convergent before (a1, b1) */
        mpz_set_ui(Z(p_a0), 0);
        mpz_set_ui(Z(p_a1), 1);
        mpz_set_ui(Z(p_b0), 1);
        mpz_set_ui(Z(p_b1), 0);
        for (uint i = 0; ; ++i) {
            /* here (a1, b1) is convergent i - 1, and cfq is Q_i */
            mpz_mul_ui(Z(p_zt1), Z(p_b1), f);
            if (mpz_cmp(Z(p_zt1), Z(p_ymax)) > 0)
                break;
            if (i > 0 && mpz_cmpabs_ui(Z(p_cfq), 1) == 0
                && mpz_sgn(Z(p_cfq)) == ((i & 1) ? -sign : sign)
            ) {
                mpz_mul(Z(p_g), Z(p_q0), Z(p_a1));
                mpz_submul(Z(p_g), roots.za[ri], Z(p_b1));
                mpz_abs(Z(p_g), Z(p_g));
                mpz_mul_ui(Z(p_x), Z(p_g), f);
                mpz_mul_ui(Z(p_y), Z(p_b1), f);
                if (by_a) {
                    /* X = ra.u, Y = w */
                    if (mpz_divisible_p(Z(p_x), Z(p_ra))) {
                        mpz_divexact(Z(p_x), Z(p_x), Z(p_ra));
                        add_solution(Z(p_x), Z(p_y));
                    }
                } else {
                    /* X = rd.w, Y = u */
                    if (mpz_divisible_p(Z(p_x), Z(p_rd))) {
                        mpz_divexact(Z(p_x), Z(p_x), Z(p_rd));
                        add_solution(Z(p_y), Z(p_x));
                    }
                }
            }
            /* a_i = floor((P_i + sqrt(E)) / Q_i), sqrt(E) irrational */
            mpz_add(Z(p_zt1), Z(p_cfp), Z(p_sqrte));
            if (mpz_sgn(Z(p_cfq)) > 0)
                mpz_fdiv_q(Z(p_cfa), Z(p_zt1), Z(p_cfq));
            else {
                mpz_neg(Z(p_zt2), Z(p_cfq));
                mpz_fdiv_q(Z(p_cfa), Z(p_zt1), Z(p_zt2));
                mpz_add_ui(Z(p_cfa), Z(p_cfa), 1);
                mpz_neg(Z(p_cfa), Z(p_cfa));
            }
            /* next convergent */
            mpz_mul(Z(p_zt1), Z(p_cfa), Z(p_a1));
            mpz_add(Z(p_zt1), Z(p_zt1), Z(p_a0));
            mpz_set(Z(p_a0), Z(p_a1));
            mpz_set(Z(p_a1), Z(p_zt1));
            mpz_mul(Z(p_zt1), Z(p_cfa), Z(p_b1));
            mpz_add(Z(p_zt1), Z(p_zt1), Z(p_b0));
            mpz_set(Z(p_b0), Z(p_b1));
            mpz_set(Z(p_b1), Z(p_zt1));
            /* P_{i+1} = a_i Q_i - P_i, Q_{i+1} = (E - P_{i+1}^2) / Q_i */
            mpz_mul(Z(p_zt1), Z(p_cfa), Z(p_cfq));
            mpz_sub(Z(p_cfp), Z(p_zt1), Z(p_cfp));
            mpz_mul(Z(p_zt1), Z(p_cfp), Z(p_cfp));
            mpz_sub(Z(p_zt1), Z(p_e), Z(p_zt1));
            mpz_divexact(Z(p_cfq), Z(p_zt1), Z(p_cfq));
        }
    }
}

/* Ax^2 - Dy^2 = N, 0 < x <= limit, 0 < y
 * We assume A, D, limit > 0 and N non-zero.
 * All the solutions are found here, in a time that grows with the
 * logarithm of the limit; next_pell() then returns them in order of x.
 */
void new_pell(mpz_t iA, mpz_t iD, int iN, mpz_t ilimit) {
    sol.size = 0;
    sol_iter = 0;
    if (iN == 0)
        fail("not trying to solve Ax^2 = Dy^2\n");
    mpz_set(Z(p_limit), ilimit);
    mpz_set_si(Z(p_n), iN);

    /* ra.u^2 - rd.w^2 = n with u = sa.x, w = sd.y; ra, rd squarefree */
    sqfree(Z(p_ra), Z(p_sa), iA);
    sqfree(Z(p_rd), Z(p_sd), iD);
    mpz_gcd(Z(p_zt1), Z(p_ra), Z(p_rd));
    if (mpz_cmp_ui(Z(p_zt1), 1) != 0) {
        if (!mpz_divisible_p(Z(p_n), Z(p_zt1)))
            return;
        mpz_divexact(Z(p_n), Z(p_n), Z(p_zt1));
        mpz_divexact(Z(p_ra), Z(p_ra), Z(p_zt1));
        mpz_divexact(Z(p_rd), Z(p_rd), Z(p_zt1));
    }
    mpz_mul(Z(p_e), Z(p_ra), Z(p_rd));
    if (mpz_cmp_ui(Z(p_e), 1) == 0) {
        solve_sqdiff();
        goto solved;
    }
    mpz_sqrt(Z(p_sqrte), Z(p_e));

    /* Multiply through by whichever of ra, rd is the smaller, giving
     * (ra.u)^2 - E.w^2 = n.ra or (rd.w)^2 - E.u^2 = -n.rd, and find the
     * limit for the second of the two unknowns.
     */
    bool by_a = (mpz_cmp(Z(p_ra), Z(p_rd)) < 0);
    mpz_mul(Z(p_ymax), Z(p_sa), ilimit);
    if (by_a) {
        /* w^2 = (ra.u^2 - n) / rd */
        mpz_mul(Z(p_ymax), Z(p_ymax), Z(p_ymax));
        mpz_mul(Z(p_ymax), Z(p_ymax), Z(p_ra));
        mpz_sub(Z(p_ymax), Z(p_ymax), Z(p_n));
        mpz_fdiv_q(Z(p_ymax), Z(p_ymax), Z(p_rd));
        if (mpz_sgn(Z(p_ymax)) < 0)
            goto solved;
        mpz_sqrt(Z(p_ymax), Z(p_ymax));
    }

    /* X and Y may share a factor f where f^2 divides the right side,
     * and since ra and rd are squarefree any such f divides n
     */
    ulong an = mpz_get_ui(Z(p_n));    /* absolute value */
    for (ulong f = 1; f <= an; ++f) {
        if (an % f)
            continue;
        mpz_mul(Z(p_m), Z(p_n), by_a ? Z(p_ra) : Z(p_rd));
        if (!by_a)
            mpz_neg(Z(p_m), Z(p_m));
        mpz_set_ui(Z(p_zt1), f);
        mpz_mul_ui(Z(p_zt1), Z(p_zt1), f);
        if (!mpz_divisible_p(Z(p_m), Z(p_zt1)))
            continue;
        mpz_divexact(Z(p_m), Z(p_m), Z(p_zt1));
        solve_coprime(f, by_a);
    }

  solved:
    /* the same solution can arise from more than one root */
    if (sol.size > 2) {
        qsort(sol.za, sol.size / 2, 2 * sizeof(mpz_t), &pell_comparator);
        uint to = 2;
        for (uint from = 2; from < sol.size; from += 2) {
            if (mpz_cmp(sol.za[from], sol.za[to - 2]) == 0
                    && mpz_cmp(sol.za[from + 1], sol.za[to - 1]) == 0)
                continue;
            if (to != from) {
                mpz_swap(sol.za[to], sol.za[from]);
                mpz_swap(sol.za[to + 1], sol.za[from + 1]);
            }
            to += 2;
        }
        sol.size = to;
    }
}

bool next_pell(mpz_t ox, mpz_t oy) {
    if (sol_iter >= sol.size)
        return 0;
    mpz_set(ox, sol.za[sol_iter]);
    mpz_set(oy, sol.za[sol_iter + 1]);
    sol_iter += 2;
    return 1;
}

#undef Z
