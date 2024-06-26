#include <stdlib.h>
#include <string.h>

#include "pell.h"
#include "coul.h"
#include "coultau.h"
#include "rootmod.h"

typedef enum {
    failed,     /* no results */
    pell,       /* x^2 - Dy^2 = 1   D not square */
    neg_pell,   /* x^2 - Dy^2 = -1  D not square */
    gen_pell,   /* x^2 - Dy^2 = N   D not square */
    sqdiff_odd, /* x^2 - y^2 = N    N odd */
    sqdiff_even,/* x^2 - y^2 = N    N even, non-zero */
} e_pelltype;

typedef enum {
    A, D, N, limit,
    x, y, p, q, p0, q0,
    filter_x, filter_y,
    zt1, zt2,
    cf_a, cf_b, cf_c, cf_d,
    aN, mN, Pi, Qi, Ai, Bi, Gi, Pn, Qn, bestG, bestB,

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

typedef struct s_interleave {
    t_zarray zmatch;
    uint match_iter;
    mpz_t x, y, mul;
} t_interleave;

t_zarray pdiv, cf_initial, cf_recur, cft;
t_interleave *gp = NULL;
uint gpc = 0;
uint gpsize;        /* number of genpell solutions to interleave */
uint sqdiff_midh;   /* upper midpoint of divisors */
uint sqdiff_midl;   /* lower midpoint of divisors */
uint sqdiff_iter;   /* counter when iterating divisors */
uint conv_iter;     /* counter when iterating convergents */
bool filter_swap;
e_pelltype type;

void resize_zarray(t_zarray *zap, uint size) {
    if (size > zap->alloc) {
        if (size < zap->alloc + 16)
            size = zap->alloc + 16;
        zap->za = (mpz_t *)realloc(zap->za, size * sizeof(mpz_t));
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

void resize_interleave(uint size) {
    if (size > gpc) {
        if (size < gpc + 16)
            size = gpc + 16;
        gp = (t_interleave *)realloc(gp, size * sizeof(t_interleave));
        for (uint i = gpc; i < size; ++i) {
            t_interleave *gpi = &gp[i];
            memset(gpi, 0, sizeof(t_interleave));
            resize_zarray(&gpi->zmatch, 16);
            mpz_init(gpi->x);
            mpz_init(gpi->y);
            mpz_init(gpi->mul);
        }
        gpc = size;
    }
}

void free_interleave(void) {
    if (gpc) {
        for (uint i = 0; i < gpc; ++i) {
            t_interleave *gpi = &gp[i];
            free_zarray(&gpi->zmatch);
            mpz_clear(gpi->x);
            mpz_clear(gpi->y);
            mpz_clear(gpi->mul);
        }
        free(gp);
        gp = NULL;
        gpc = 0;
    }
}

void done_pell(void) {
    for (e_pellstash e = 0; e < E_PELLSTASH_MAX; ++e)
        mpz_clear(Z(e));
    free(pell_stash);
    free_zarray(&pdiv);
    free_zarray(&cf_initial);
    free_zarray(&cf_recur);
    free_zarray(&cft);
    free_interleave();
}

void init_pell(void) {
    pell_stash = (mpz_t *)malloc(E_PELLSTASH_MAX * sizeof(mpz_t));
    for (e_pellstash e = 0; e < E_PELLSTASH_MAX; ++e)
        mpz_init(Z(e));
    resize_interleave(16);
}

int pell_comparator(const void *va, const void *vb) {
    return mpz_cmp(*(mpz_t *)va, *(mpz_t *)vb);
}

/* Put sorted list of the divisors of n into pdiv array.
 */
void pdivisors(mpz_t n) {
    resize_zarray(&pdiv, 1);
    mpz_set_ui(pdiv.za[0], 1);
    pdiv.size = 1;

    factor_state fs;
    fs_init(&fs);
    mpz_set(fs.n, n);
    while (factor_one(&fs)) {
        uint oldsize = pdiv.size;
        resize_zarray(&pdiv, oldsize * (fs.e + 1));
        for (uint i = 0; i < oldsize; ++i) {
            mpz_t *src = &pdiv.za[i];
            uint targ = pdiv.size;
            for (uint j = 0; j < fs.e; ++j) {
                mpz_mul(pdiv.za[targ], *src, fs.f);
                src = &pdiv.za[targ];
                ++targ;
            }
            pdiv.size = targ;
        }
    }
    qsort(pdiv.za, pdiv.size, sizeof(mpz_t), &pell_comparator);
    fs_clear(&fs);
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

/* Set up cf_initial and cf_recur to represent the periodic continued
 * fraction for (cf_a + cf_b sqrt(cf_d)) / cf_c.
 */
void contfrac(void) {
    cf_initial.size = 0;
    cf_recur.size = 0;
    resize_zarray(&cft, 3);
    mpz_set(cft.za[0], Z(cf_a));
    mpz_set(cft.za[1], Z(cf_b));
    mpz_set(cft.za[2], Z(cf_c));
    cft.size = 3;
    uint split;
    bool qd = mpz_perfect_square_p(Z(cf_d));

    while (1) {
        uint cura = cft.size - 3;
        uint curb = cft.size - 2;
        uint curc = cft.size - 1;
        if (mpz_sgn(cft.za[curc]) == 0)
            fail("Division by zero\n");
        if (mpz_sgn(cft.za[cura]) == 0 && mpz_sgn(cft.za[curb]) == 0)
            return;
        if (mpz_sgn(cft.za[curc]) < 0) {
            mpz_mul_si(cft.za[cura], cft.za[cura], -1);
            mpz_mul_si(cft.za[curb], cft.za[curb], -1);
            mpz_mul_si(cft.za[curc], cft.za[curc], -1);
        }
        mpz_gcd(Z(zt1), cft.za[cura], cft.za[curb]);
        mpz_gcd(Z(zt1), Z(zt1), cft.za[curc]);
        if (mpz_cmp_ui(Z(zt1), 1) > 0) {
            mpz_divexact(cft.za[cura], cft.za[cura], Z(zt1));
            mpz_divexact(cft.za[curb], cft.za[curb], Z(zt1));
            mpz_divexact(cft.za[curc], cft.za[curc], Z(zt1));
        }

        /* CHECKME: do we need something faster than linear search? */
        for (uint i = 0; i < cft.size - 3; i += 3) {
            if (mpz_cmp(cft.za[i], cft.za[cura]) == 0
                && mpz_cmp(cft.za[i + 1], cft.za[curb]) == 0
                && mpz_cmp(cft.za[i + 2], cft.za[curc]) == 0
            ) {
                split = i / 3;
                goto cf_done;
            }
        }

        mpz_mul(Z(zt1), cft.za[curb], cft.za[curb]);
        mpz_mul(Z(zt1), Z(zt1), Z(cf_d));
        mpz_root(Z(zt1), Z(zt1), 2);
        if (mpz_sgn(cft.za[curb]) < 0) {
            mpz_mul_si(Z(zt1), Z(zt1), -1);
            if (!qd)
                mpz_sub_ui(Z(zt1), Z(zt1), 1);
        }
        mpz_add(Z(zt1), Z(zt1), cft.za[cura]);
        mpz_fdiv_q(Z(zt1), Z(zt1), cft.za[curc]);
        resize_zarray(&cf_initial, cf_initial.size + 1);
        mpz_set(cf_initial.za[cf_initial.size++], Z(zt1));

        /* now calculate 1 / (a/c + b/c sqrt(d) - x)
         * = (ac - c^2x - bc sqrt(d)) / ((a + cx)^2 - b^2d) */
        resize_zarray(&cft, cft.size + 3);
        cft.size += 3;
        uint nexta = cft.size - 3;
        uint nextb = cft.size - 2;
        uint nextc = cft.size - 1;

        mpz_mul(Z(zt1), Z(zt1), cft.za[curc]);
        mpz_sub(Z(zt2), cft.za[cura], Z(zt1));
        mpz_mul(cft.za[nexta], cft.za[curc], Z(zt2));
        mpz_mul(cft.za[nextb], cft.za[curb], cft.za[curc]);
        mpz_mul_si(cft.za[nextb], cft.za[nextb], -1);
        mpz_mul(Z(zt2), Z(zt2), Z(zt2));
        mpz_mul(Z(zt1), cft.za[curb], cft.za[curb]);
        mpz_mul(Z(zt1), Z(zt1), Z(cf_d));
        mpz_sub(cft.za[nextc], Z(zt2), Z(zt1));
    }
  cf_done:
    resize_zarray(&cf_recur, cf_initial.size - split);
    for (uint i = split; i < cf_initial.size; ++i)
        mpz_set(cf_recur.za[i - split], cf_initial.za[i]);
    cf_recur.size = cf_initial.size - split;
    cf_initial.size = split;
}

void init_convergents(void) {
    mpz_set_ui(Z(p0), 0);
    mpz_set_ui(Z(p), 1);
    mpz_set_ui(Z(q0), 1);
    mpz_set_ui(Z(q), 0);
    conv_iter = 0;
}

bool next_convergent(void) {
    mpz_t *next;
    if (conv_iter < cf_initial.size)
        next = &cf_initial.za[conv_iter];
    else if (cf_recur.size) {
        uint off = conv_iter - cf_initial.size;
        next = &cf_recur.za[off % cf_recur.size];
    } else
        return 0;
    ++conv_iter;
    mpz_set(Z(zt1), Z(p0));
    mpz_set(Z(p0), Z(p));
    mpz_mul(Z(p), Z(p), *next);
    mpz_add(Z(p), Z(p), Z(zt1));
    mpz_set(Z(zt1), Z(q0));
    mpz_set(Z(q0), Z(q));
    mpz_mul(Z(q), Z(q), *next);
    mpz_add(Z(q), Z(q), Z(zt1));
    return 1;
}

void pell_fund_sol(void) {
    mpz_set_ui(Z(cf_a), 0);
    mpz_set_ui(Z(cf_b), 1);
    mpz_set_ui(Z(cf_c), 1);
    mpz_set(Z(cf_d), Z(D));
    contfrac();
    init_convergents();
    /* Not sure how far we have to go in the worst case, but D=58 needs
     * this limit */
    uint lim = cf_initial.size + cf_recur.size * 2;
    for (uint i = 0; i < lim; ++i) {
        if (!next_convergent())
            fail("no next convergent\n");
        mpz_mul(Z(zt1), Z(p), Z(p));
        mpz_mul(Z(zt2), Z(q), Z(q));
        mpz_mul(Z(zt2), Z(zt2), Z(D));
        mpz_sub(Z(zt1), Z(zt1), Z(zt2));
        if (mpz_cmp_ui(Z(zt1), 1) == 0)
            return;
    }
    fail("No principle solution found for pell(%Zu)\n", Z(D));
}

void init_sqdiff(void) {
    /* Solve x^2 - y^2 = N */
    if (mpz_sgn(Z(N)) == 0)
        fail("not trying to solve x^2 = y^2\n");
    else if (mpz_sgn(Z(N)) < 0) {
        filter_swap = 1;
        mpz_swap(Z(filter_x), Z(filter_y));
        mpz_abs(Z(N), Z(N));
    }

    if (mpz_odd_p(Z(N)))
        type = sqdiff_odd;
    else if (mpz_tstbit(Z(N), 1)) {
        /* cannot have N == 2 (mod 4) */
        type = failed;
        return;
    } else {
        type = sqdiff_even;
        mpz_divexact_ui(Z(N), Z(N), 4);
    }
    pdivisors(Z(N));
    sqdiff_midh = pdiv.size >> 1;
    sqdiff_midl = sqdiff_midh - ((pdiv.size & 1) ? 0 : 1);
    sqdiff_iter = 0;
}

void init_basepell(void) {
    /* Solve x^2 - Dy^2 = 1 */
    type = pell;
    pell_fund_sol();
    mpz_set_ui(Z(x), 1);
    mpz_set_ui(Z(y), 0);
}

void init_negpell(void) {
    /* Solve x^2 - Dy^2 = -1 */
    mpz_set_ui(Z(cf_a), 0);
    mpz_set_ui(Z(cf_b), 1);
    mpz_set_ui(Z(cf_c), 1);
    mpz_set(Z(cf_d), Z(D));
    contfrac();
    if (cf_recur.size == 0)
        fail("can't handle neg_pell(%Zu) with square argument\n", Z(D));
    /* negative Pell's equation has no solutions if period is even */
    if ((cf_recur.size & 1) == 0) {
        type = failed;
        return;
    }
    init_convergents();
    uint lim = cf_initial.size + cf_recur.size;
    for (uint i = 0; i < lim; ++i) {
        next_convergent();
        mpz_mul(Z(zt1), Z(p), Z(p));
        mpz_mul(Z(zt2), Z(q), Z(q));
        mpz_mul(Z(zt2), Z(zt2), Z(D));
        mpz_add_ui(Z(zt1), Z(zt1), 1);
        if (mpz_cmp(Z(zt1), Z(zt2)) == 0)
            goto negpell_ok;
    }
    type = failed;
    return;
  negpell_ok:
    type = neg_pell;
    mpz_set(Z(x), Z(p));
    mpz_set(Z(y), Z(q));
}

/* x^2 - Dy^2 = N: x, y coprime */
void init_genpell_coprime(t_interleave *gpp) {
    mpz_divexact(Z(mN), Z(N), gpp->mul);
    mpz_divexact(Z(mN), Z(mN), gpp->mul);
    mpz_abs(Z(aN), Z(mN));
    /* if D is not a quadratic residue (mod mN), there is no solution */
    allrootmod(0, Z(D), 2, Z(aN));
    t_results *qrp = res_array(0);
    gpp->zmatch.size = 0;
    if (qrp->count == 0)
        return;

    for (uint qri = 0; qri < qrp->count; ++qri) {
        mpz_set(Z(cf_a), qrp->r[qri]);
        mpz_set_ui(Z(cf_b), 1);
        mpz_set(Z(cf_c), Z(aN));
        mpz_set(Z(cf_d), Z(D));
        contfrac();
        init_convergents();
        if (!next_convergent())
            continue;
        mpz_set(Z(Pi), qrp->r[qri]);
        mpz_set(Z(Qi), Z(aN));
        mpz_set(Z(Ai), Z(p));
        mpz_set(Z(Bi), Z(q));
        uint lim = cf_initial.size + cf_recur.size;
        bool have_best = 0;
        for (uint cfi = 0; cfi < lim; ++cfi) {
            mpz_t *cfz;
            if (cfi < cf_initial.size)
                cfz = &cf_initial.za[cfi];
            else
                cfz = &cf_recur.za[cfi - cf_initial.size];
            /* calculate 1 / ((P + sqrt(D)) / Q - x)
             *         = (Qx - P + sqrt(D)) / ((D - (P + Qx)^2 / Q) */
            mpz_mul(Z(zt1), Z(Pi), Z(Pi));
            mpz_sub(Z(zt1), Z(zt1), Z(D));
            mpz_fdiv_qr(Z(zt1), Z(zt2), Z(zt1), Z(Qi));
            if (mpz_sgn(Z(zt2)) != 0)
                fail("logic error: expect %Zi^2 == %Zi (mod %Zi)\n",
                    Z(Pi), Z(D), Z(Qi)
                );
            mpz_mul(Z(Pn), Z(Qi), *cfz);
            mpz_sub(Z(Pn), Z(Pn), Z(Pi));
            mpz_mul_ui(Z(Qn), Z(Pi), 2);
            mpz_mul(Z(zt2), Z(Qi), *cfz);
            mpz_sub(Z(Qn), Z(Qn), Z(zt2));
            mpz_mul(Z(Qn), Z(Qn), *cfz);
            mpz_sub(Z(Qn), Z(Qn), Z(zt1));
            next_convergent();
            if (mpz_cmp_ui(Z(Qn), 1) == 0) {
                mpz_mul(Z(Gi), Z(aN), Z(Ai));
                mpz_mul(Z(zt1), qrp->r[qri], Z(Bi));
                mpz_sub(Z(Gi), Z(Gi), Z(zt1));
                mpz_abs(Z(Gi), Z(Gi));
                mpz_mul(Z(zt1), Z(Gi), Z(Gi));
                mpz_mul(Z(zt2), Z(Bi), Z(Bi));
                mpz_mul(Z(zt2), Z(zt2), Z(D));
                mpz_sub(Z(zt1), Z(zt1), Z(zt2));
                if (mpz_cmp(Z(zt1), Z(mN)) == 0
                    && (!have_best || mpz_cmp(Z(Gi), Z(bestG)) < 0)
                ) {
                    mpz_set(Z(bestG), Z(Gi));
                    mpz_set(Z(bestB), Z(Bi));
                    have_best = 1;
                }
            }
            mpz_set(Z(Pi), Z(Pn));
            mpz_set(Z(Qi), Z(Qn));
            mpz_set(Z(Ai), Z(p));
            mpz_set(Z(Bi), Z(q));
        }
        if (have_best) {
            resize_zarray(&gpp->zmatch, gpp->zmatch.size + 2);
            mpz_set(gpp->zmatch.za[gpp->zmatch.size], Z(bestG));
            mpz_set(gpp->zmatch.za[gpp->zmatch.size + 1], Z(bestB));
            gpp->zmatch.size += 2;
        }
    }
    if (gpp->zmatch.size == 0)
        return;
    qsort(gpp->zmatch.za, gpp->zmatch.size / 2, 2 * sizeof(mpz_t),
            &pell_comparator);
    pell_fund_sol();
    gpp->match_iter = 0;
}

/* x^2 - Dy^2 = N
 * For each k: k^2 | N, we need to find solutions to (kx)^2 - D(ky)^2 = N
 * with (x, y) coprime, and interleave them.
 */
void init_genpell(void) {
    /* Find k: squared divisors of N */
    sqfree(Z(zt1), Z(zt2), Z(N));
    pdivisors(Z(zt2));
    resize_interleave(pdiv.size);
    gpsize = 0;
    /* Set up a solution for each k */
    for (uint i = 0; i < pdiv.size; ++i) {
        t_interleave *gpp = &gp[gpsize];
        mpz_set(gpp->mul, pdiv.za[i]);
        init_genpell_coprime(gpp);
        /* Skip if no solutions for this k */
        if (gpp->zmatch.size == 0)
            continue;
        /* Initialize first result, for interleaving */
        mpz_mul(gpp->x, gpp->zmatch.za[0], gpp->mul);
        mpz_mul(gpp->y, gpp->zmatch.za[1], gpp->mul);
        ++gpsize;
    }
    if (gpsize == 0) {
        type = failed;
        return;
    }
    type = gen_pell;
    pell_fund_sol();
}

/* Ax^2 - Dy^2 = N, 0 < x <= limit
 * We assume A, D, limit > 0.
 */
void new_pell(mpz_t iA, mpz_t iD, int iN, mpz_t ilimit) {
    mpz_set(Z(A), iA);
    mpz_set(Z(D), iD);
    mpz_set_si(Z(N), iN);
    mpz_set(Z(limit), ilimit);

    mpz_set_ui(Z(filter_x), 1);
    mpz_set_ui(Z(filter_y), 1);
    filter_swap = 0;

    sqfree(Z(zt1), Z(zt2), Z(A));
    mpz_mul(Z(filter_x), Z(zt1), Z(zt2));
    mpz_mul(Z(D), Z(D), Z(zt1));
    mpz_mul(Z(N), Z(N), Z(zt1));
    mpz_set_ui(Z(A), 1);

    sqfree(Z(D), Z(zt1), Z(D));
    mpz_mul(Z(filter_y), Z(filter_y), Z(zt1));

    /* now x^2 - Dy^2 = N */
    if (mpz_cmp_ui(Z(D), 1) == 0)
        return init_sqdiff();
    if (mpz_cmp_ui(Z(N), 1) == 0)
        return init_basepell();
    if (mpz_cmp_si(Z(N), -1) == 0)
        return init_negpell();
    return init_genpell();
}

bool next_pell(mpz_t ox, mpz_t oy) {
  pell_retry:
    switch (type) {
      case failed:
        return 0;
      case pell:
        mpz_set(ox, Z(x));
        mpz_set(oy, Z(y));

        /* x' = px + Dqy; y' = py + qx */
        mpz_mul(Z(zt1), ox, Z(p));
        mpz_mul(Z(zt2), oy, Z(q));
        mpz_mul(Z(zt2), Z(zt2), Z(D));
        mpz_add(Z(x), Z(zt1), Z(zt2));

        mpz_mul(Z(zt1), oy, Z(p));
        mpz_mul(Z(zt2), ox, Z(q));
        mpz_add(Z(y), Z(zt1), Z(zt2));
        break;
      case neg_pell:
        mpz_set(ox, Z(x));
        mpz_set(oy, Z(y));

        /* x' = p^2x + Dq^2x + 2Dpqy; y' = p^2y + Dq^2y + 2pqx */
        mpz_mul(Z(x), Z(p), Z(p));
        mpz_mul(Z(x), Z(x), ox);
        mpz_mul(Z(zt2), Z(q), Z(q));
        mpz_mul(Z(zt2), Z(zt2), Z(D));
        mpz_mul(Z(zt1), Z(zt2), ox);
        mpz_add(Z(x), Z(x), Z(zt1));
        mpz_mul(Z(zt1), Z(p), Z(q));
        mpz_mul(Z(zt1), Z(zt1), Z(D));
        mpz_mul(Z(zt1), Z(zt1), oy);
        mpz_mul_ui(Z(zt1), Z(zt1), 2);
        mpz_add(Z(x), Z(x), Z(zt1));

        mpz_mul(Z(y), Z(p), Z(p));
        mpz_mul(Z(y), Z(y), oy);
        mpz_mul(Z(zt1), Z(zt2), oy);
        mpz_add(Z(y), Z(y), Z(zt1));
        mpz_mul(Z(zt1), Z(p), Z(q));
        mpz_mul(Z(zt1), Z(zt1), ox);
        mpz_mul_ui(Z(zt1), Z(zt1), 2);
        mpz_add(Z(y), Z(y), Z(zt1));
        break;
      case gen_pell: {
        /* Find smallest next solution */
        uint i = 0;
        for (uint j = 1; j < gpsize; ++j) {
            uint cmp = mpz_cmp(gp[i].x, gp[j].x);
            if (cmp == 0)
                cmp = mpz_cmp(gp[i].y, gp[j].y);
            if (cmp > 0)
                i = j;
        }
        /* Return this solution, and initialize next one */
        t_interleave *gpp = &gp[i];
        mpz_t *match = &gpp->zmatch.za[gpp->match_iter];
        gpp->match_iter = (gpp->match_iter + 2) % gpp->zmatch.size;
        mpz_set(ox, match[0]);
        mpz_set(oy, match[1]);
        /* x' + y' sqrt(D) = (x + y sqrt(D))(p + q sqrt(D)) */
        mpz_mul(match[0], ox, Z(p));
        mpz_mul(Z(zt1), oy, Z(q));
        mpz_mul(Z(zt1), Z(zt1), Z(D));
        mpz_add(match[0], match[0], Z(zt1));
        mpz_mul(match[1], ox, Z(q));
        mpz_mul(Z(zt1), oy, Z(p));
        mpz_add(match[1], match[1], Z(zt1));

        mpz_set(ox, gpp->x);
        mpz_set(oy, gpp->y);
        mpz_mul(gpp->x, gpp->zmatch.za[gpp->match_iter], gpp->mul);
        mpz_mul(gpp->y, gpp->zmatch.za[gpp->match_iter + 1], gpp->mul);
        break;
      }
      case sqdiff_odd:
      case sqdiff_even: {
        if (sqdiff_midh + sqdiff_iter >= pdiv.size)
            return 0;
        mpz_t *pdl = &pdiv.za[sqdiff_midl - sqdiff_iter];
        mpz_t *pdh = &pdiv.za[sqdiff_midh + sqdiff_iter];
        ++sqdiff_iter;
        mpz_add(ox, *pdh, *pdl);
        mpz_sub(oy, *pdh, *pdl);
        if (type == sqdiff_odd) {
            mpz_divexact_ui(ox, ox, 2);
            mpz_divexact_ui(oy, oy, 2);
        }
        break;
      }
      default:
        fail("unexpected type %u\n", type);
    }

    if (filter_swap)
        mpz_swap(ox, oy);
    mpz_fdiv_qr(ox, Z(zt1), ox, Z(filter_x));
    if (mpz_cmp(ox, Z(limit)) > 0)
        return 0;
    if (mpz_sgn(Z(zt1)))
        goto pell_retry;
    mpz_fdiv_qr(oy, Z(zt1), oy, Z(filter_y));
    if (mpz_sgn(Z(zt1)))
        goto pell_retry;
    return 1;
}

#undef Z
