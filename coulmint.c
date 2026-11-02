#include <stdlib.h>
#include <stdio.h>
#include <assert.h>

#include "coul.h"
#include "coulmint.h"
#include "builtins.h"

/* from coul.c */
extern bool debugm;

/* copy of coul.c's target_lcm, set by prep_mintau() */
static uint target_lcm;

/* additional arrays of mpz_t initialized once at start */
mpz_t *mint_best, *mint_px; /* size mint_maxdepth */

/* If .valid, this mintau is .v as long as the index of the next available
 * prime is >= .from
 */
typedef struct s_mint_capped {
    mpz_t v;
    uint from;
    bool valid;
} t_mint_capped;
struct s_mint;
typedef struct s_mint {
    size_t capped_size;
    size_t branch_size;
    t_mint_capped *capped;
    struct s_mint **branch;
} t_mint;
typedef struct s_mint_state {
    uint *pfreev;       /* bit vector of available primes */
    /* the rest need MAX_NSPRIMES < 32768 */
    ushort *pfreei;     /* list of free prime indices */
    ushort pfreenext;   /* where to start looking for next free prime */
    ushort pfreedepth;  /* number of free primes found */
} t_mint_state;
uint mint_maxdepth;     /* size of pfreei[], mint_best[] and mint_px[] */
t_mint **mint_base;
uint *restricted;
uint restricted_count;
t_mint ***mint_base_restricted;
t_mint_state mint_state;

t_mint *new_mint(void) {
    t_mint *mp = calloc(1, sizeof(t_mint));
    return mp;
}

/* TODO: optimize resizing strategy */
static inline void resize_branch(t_mint *base, uint need) {
    size_t size = need + 1;
    base->branch = realloc(base->branch, size * sizeof(t_mint *));
    for (uint i = base->branch_size; i < size; ++i)
        base->branch[i] = NULL;
    base->branch_size = size;
}
static inline void resize_capped(t_mint *base, uint need) {
    size_t size = need + 1;
    base->capped = realloc(base->capped, size * sizeof(t_mint_capped));
    for (uint i = base->capped_size; i < size; ++i)
        base->capped[i].valid = 0;
    base->capped_size = size;
}

t_mint *mint_branch(t_mint *base, uint pdiff, bool create) {
    t_mint *branch;
    if (base->branch_size <= pdiff) {
        if (!create)
            return (t_mint *)NULL;
        resize_branch(base, pdiff);
    }
    branch = base->branch[pdiff];
    if (branch == NULL) {
        if (!create)
            return (t_mint *)NULL;
        branch = new_mint();
        base->branch[pdiff] = branch;
    }
    return branch;
}

t_mint_capped *mint_capped(t_mint *base, uint pdiff, bool create) {
    t_mint_capped *capped;
    if (base->capped_size <= pdiff) {
        if (!create)
            return (t_mint_capped *)NULL;
        resize_capped(base, pdiff);
    }
    return &base->capped[pdiff];
}

void mint_init_base(t_mint ***p) {
    t_divisors *dp = &divisors[target_lcm];
    *p = calloc(target_lcm + 1, sizeof(t_mint *));
    for (uint di = 0; di < dp->alldiv; ++di) {
        uint f = dp->div[di];
        if (f == 1)
            continue;
        (*p)[f] = new_mint();
    }
}

/* mintau() may be asked for t = t_i / x for any x > 1 dividing t_i, so
 * for any t | n/p with p the least prime dividing n: prep_midp() sweeps
 * powers that need not be a multiple of h(t_i). Under -k, mintau_at()
 * may halve such a t, which keeps to the same bound. Returns the depth
 * that needs, sumpm(n/p).
 */
static uint mint_depth(void) {
    uint p = 2;
    if (target_lcm == 1)
        return 0;
    while (target_lcm % p)
        ++p;
    return divisors[target_lcm / p].sumpm;
}

void prep_mintau(uint lcm) {
    target_lcm = lcm;
    mint_init_base(&mint_base);

    restricted_count = 0;
    restricted = NULL;
    t_divisors *dp = &divisors[target_lcm];
    for (uint di = 0; di < dp->alldiv; ++di) {
        uint d = dp->div[di];
        uint h = divisors[d].high;
        if (h <= 2)
            break;
        if ((target_lcm / d) % h)
            continue;
        restricted = realloc(restricted, (restricted_count + 1) * sizeof(uint));
        restricted[restricted_count++] = d;
    }
    if (restricted_count) {
        mint_base_restricted = malloc(restricted_count * sizeof(t_mint **));
        for (uint i = 0; i < restricted_count; ++i)
            mint_init_base(&mint_base_restricted[i]);
    }

    mint_maxdepth = mint_depth();
    t_mint_state *s = &mint_state;
    s->pfreei = calloc(mint_maxdepth, sizeof(ushort));

    mint_best = malloc(mint_maxdepth * sizeof(mpz_t));
    mint_px = malloc(mint_maxdepth * sizeof(mpz_t));
    for (uint i = 0; i < mint_maxdepth; ++i) {
        mpz_init(mint_best[i]);
        mpz_init(mint_px[i]);
    }
}

void free_mint(t_mint *mtp) {
    for (uint i = 0; i < mtp->capped_size; ++i) {
        t_mint_capped *capped = &mtp->capped[i];
        if (capped->valid)
            mpz_clear(capped->v);
    }
    free(mtp->capped);
    for (uint i = 0; i < mtp->branch_size; ++i) {
        t_mint *branch = mtp->branch[i];
        if (branch)
            free_mint(branch);
    }
    free(mtp->branch);
    free(mtp);
}

void mint_free_base(t_mint ***p) {
    t_divisors *dp = &divisors[target_lcm];
    for (uint di = 0; di < dp->alldiv; ++di) {
        uint f = dp->div[di];
        if (f == 1)
            continue;
        t_mint *mtp = (*p)[f];
        if (mtp)
            free_mint(mtp);
    }
    free(*p);
}

void done_mintau(void) {
    t_mint_state *s = &mint_state;
    free(s->pfreei);

    mint_free_base(&mint_base);
    if (restricted_count) {
        free(restricted);
        for (uint i = 0; i < restricted_count; ++i)
            mint_free_base(&mint_base_restricted[i]);
        free(mint_base_restricted);
    }

    for (uint i = 0; i < mint_maxdepth; ++i) {
        mpz_clear(mint_best[i]);
        mpz_clear(mint_px[i]);
    }
    free(mint_best);
    free(mint_px);
}

void track_mintau(mpz_t mint, uint t, uint depth0) {
    t_mint_state *s = &mint_state;
    gmp_fprintf(stderr, "mintau(%u) = %Zu [", t, mint);
    for (uint i = depth0; i < s->pfreedepth; ++i) {
        if (i > depth0)
            gmp_fprintf(stderr, " ");
        gmp_fprintf(stderr, "%u", sprimes[s->pfreei[i]]);
    }
    gmp_fprintf(stderr, "]\n");
}

static inline void mint_init_state(t_node *cur_node) {
    t_mint_state *s = &mint_state;
    s->pfreev = cur_node->pfreev;
    s->pfreenext = 0;
    s->pfreedepth = 0;
}

/* needs MAX_NSPRIMES < 32768 */
static inline void state_extend(signed short i) {
    t_mint_state *s = &mint_state;
    uint *pv = s->pfreev;
    uint next = s->pfreenext;
    uint nextoff = next >> 5;
    uint nextbit = next & 0x1f;
    uint depth = s->pfreedepth;
    while (depth <= i) {
        assert(nextoff < pfree_vecsize && nextbit < 8 * sizeof(uint));
        uint v = pv[nextoff] & ~((1U << nextbit) - 1);
        nextbit = ffs_u32(v);
        if (nextbit) {
            assert(depth < mint_maxdepth);
            s->pfreei[depth] = (nextoff << 5) + (nextbit - 1);
            ++depth;
        } else {
            ++nextoff;
            nextbit = 0;
        }
    }
    s->pfreenext = (nextoff << 5) + nextbit;
    s->pfreedepth = depth;
}
/* needs MAX_NSPRIMES < 32768 */
static inline signed short state_pfi(signed short i) {
    t_mint_state *s = &mint_state;
    assert(i >= 0);
    if (i >= s->pfreedepth)
        state_extend(i);
    return s->pfreei[i];
}

static inline bool mintau_check_known(
    t_mint *mtp, mpz_t mint, uint depth0, uint maxdepth
) {
    t_mint_state *s = &mint_state;
    for (uint depth = depth0; mtp && depth <= maxdepth; ++depth) {
        /* needs MAX_NSPRIMES < 32768 */
        ushort off = state_pfi(depth)
                - ((depth == depth0) ? 0 : s->pfreei[depth - 1]);
        t_mint_capped *capped = mint_capped(mtp, off, 0);
        if (capped && capped->valid && (
            depth == maxdepth || state_pfi(depth + 1) >= capped->from
        )) {
            mpz_set(mint, capped->v);
            return 1;
        }
        mtp = mint_branch(mtp, off, 0);
    }
    return 0;
}

static inline void mintau_cache_result(
    t_mint *mtp, mpz_t *mbest, uint depth0, uint maxdepth
) {
    t_mint_state *s = &mint_state;
    for (uint depth = depth0; mtp && depth <= maxdepth; ++depth) {
        /* needs MAX_NSPRIMES < 32768 */
        ushort off = state_pfi(depth)
                - ((depth == depth0) ? 0 : s->pfreei[depth - 1]);
        signed short next = (depth < maxdepth) ? state_pfi(depth + 1) : -1;
        if (next < 0
            || !mpz_divisible_ui_p(*mbest, (ulong)sprimes[next])
        ) {
            t_mint_capped *capped = mint_capped(mtp, off, 1);
            if (!capped->valid) {
                mpz_init_set(capped->v, *mbest);
                capped->valid = 1;
            }
            capped->from = (next < 0) ? 0 : next;
            break;
        }
        mtp = mint_branch(mtp, off, 1);
    }
}

/* Calculate the minimum contribution from unused primes satisfying
 * the given tau.
 *
 * This may be called for any t: t | n/p, p the least prime dividing n
 * (see mint_depth()).
 *
 * Sets mint to the result - there is always a valid value.
 */
void mintau_r(ushort depth0, mpz_t mint, uint t) {
    if (t == 1) {
        mpz_set_ui(mint, 1);
        return;
    }

    t_divisors *dp = &divisors[t];
    t_mint_state *s = &mint_state;
    uint maxdepth = depth0 - 1 + dp->sumpm;

    /* check if we already know this mintau */
    if (mintau_check_known(mint_base[t], mint, depth0, maxdepth))
        goto mintau_done;

    /* calculate this mintau */
    ulong p = (ulong)sprimes[state_pfi(depth0)];
    bool have_best = 0;
    mpz_t *mpx = &mint_px[depth0];  /* array protects against recursive calls */
    mpz_t *mbest = &mint_best[depth0];
    for (uint di = 0; di < dp->alldiv; ++di) {
        /* TODO: have a variant .div[] starting from .high in ascending order,
         * so that the 'd < dp->high' check is not needed, and the 'have_best
         * && best <= mpx' can lead to 'break' instead of 'continue'.
         */
        uint d = dp->div[di];
        if (d < dp->high)
            continue;
        mpz_ui_pow_ui(*mpx, p, (ulong)d - 1);
        if (have_best && mpz_cmp(*mbest, *mpx) <= 0)
            continue;
        mintau_r(depth0 + 1, mint, t / d);
        mpz_mul(mint, mint, *mpx);
        if (!have_best || mpz_cmp(*mbest, mint) > 0) {
            mpz_set(*mbest, mint);
            have_best = 1;
        }
    }
    if (debugm)
        track_mintau(*mbest, t, depth0);

    /* work out where to cache the result */
    mintau_cache_result(mint_base[t], mbest, depth0, maxdepth);
    mpz_set(mint, *mbest);
  mintau_done:
    ;
}

/* Calculate the minimum contribution from unused primes satisfying
 * the given tau.
 *
 * This may be called for any t: t | n/p, p the least prime dividing n
 * (see mint_depth()).
 *
 * Sets mint to the result - there is always a valid value.
 *
 * We only initialize the state structure once, any recursive calls
 * share it via the depth0 parameter.
 */
void mintau(t_node *cur_node, mpz_t mint, uint t) {
    if (t == 1) {
        mpz_set_ui(mint, 1);
        return;
    }
    mint_init_state(cur_node);
    mintau_r(0, mint, t);
}

/* Calculate the minimum contribution from unused primes satisfying
 * the given tau, while avoiding powers p^x: h(x) == h(r), x <= r.
 *
 * This may be called for any t: t | n/p, p the least prime dividing n
 * (see mint_depth()).
 *
 * Sets mint to the result, or to zero if no valid value.
 */
void mintau_restricted_r(ushort depth0, mpz_t mint, uint t, uint r, uint ri) {
    if (t == 1) {
        mpz_set_ui(mint, 1);
        return;
    }
    if (t % divisors[r].high)
        return mintau_r(depth0, mint, t);

    t_divisors *dp = &divisors[t];
    t_mint_state *s = &mint_state;
    uint maxdepth = depth0 - 1 + dp->sumpm;

    /* check if we already know this mintau */
    if (mintau_check_known(mint_base_restricted[ri][t], mint, depth0, maxdepth))
        goto mintau_done;

    /* calculate this mintau */
    ulong p = (ulong)sprimes[state_pfi(depth0)];
    bool have_best = 0;
    mpz_t *mpx = &mint_px[depth0];  /* array protects against recursive calls */
    mpz_t *mbest = &mint_best[depth0];
    for (uint di = 0; di < dp->alldiv; ++di) {
        /* see also TODO in mintau_r() */
        uint d = dp->div[di];
        if (d < dp->high)
            continue;
        if (d <= r && divisors[d].high == divisors[r].high)
            continue;
        mpz_ui_pow_ui(*mpx, p, (ulong)d - 1);
        if (have_best && mpz_cmp(*mbest, *mpx) <= 0)
            continue;
        mintau_restricted_r(depth0 + 1, mint, t / d, r, ri);
        if (mpz_sgn(mint) == 0)
            continue;
        mpz_mul(mint, mint, *mpx);
        if (!have_best || mpz_cmp(*mbest, mint) > 0) {
            mpz_set(*mbest, mint);
            have_best = 1;
        }
    }
    if (!have_best)
        mpz_set_ui(*mbest, 0);
    if (debugm)
        track_mintau(*mbest, t, depth0);

    /* work out where to cache the result */
    mintau_cache_result(mint_base_restricted[ri][t], mbest, depth0, maxdepth);
    mpz_set(mint, *mbest);
  mintau_done:
    ;
}

/* Calculate the minimum contribution from unused primes satisfying
 * the given tau, while avoiding powers p^x: h(x) == h(r), x <= r.
 *
 * This may be called for any t: t | n/p, p the least prime dividing n
 * (see mint_depth()).
 *
 * Sets mint to the result, or to zero if no valid value.
 *
 * We only initialize the state structure once, any recursive calls
 * share it via the depth0 parameter.
 */
void mintau_restricted(t_node *cur_node, mpz_t mint, uint t, uint r) {
    if (t == 1) {
        mpz_set_ui(mint, 1);
        return;
    }
    uint ri = restricted_count;
    for (uint i = 0; i < restricted_count; ++i) {
        if (restricted[i] != r)
            continue;
        ri = i;
        break;
    }
    assert(ri < restricted_count);
    mint_init_state(cur_node);
    mintau_restricted_r(0, mint, t, r, ri);
}

/* As mintau() for the given tau as left at v_i, as potentially modified
 * by the action of -k. Where -k has not acted, the answer is the same;
 * where it has acted (which happens only if t == 2 (mod 4)), we have
 * already tested every p^x with p <= B, x = 2 and for all other even x
 * across the full range. It is assumed B is chosen high enough that
 * B . mintau(t/2) is the correct minimal answer, but if not we only risk
 * giving too low an answer (which is safe).
 * This may be called when -k is enabled for any t | n/2.
 */
void mintau_at(t_node *cur_node, mpz_t mint, uint t, uint vi) {
    if ((t & 3) == 2 && kern_at(vi)) {
        mintau(cur_node, mint, t >> 1);
        mpz_mul_ui(mint, mint, kern_cur()->b);
    } else
        mintau(cur_node, mint, t);
}

/* as mintau_restricted() for the given tau as left at v_i, see mintau_at() */
void mintau_restricted_at(
    t_node *cur_node, mpz_t mint, uint t, uint r, uint vi
) {
    if ((t & 3) == 2 && kern_at(vi)) {
        mintau_restricted(cur_node, mint, t >> 1, r);
        mpz_mul_ui(mint, mint, kern_cur()->b);
    } else
        mintau_restricted(cur_node, mint, t, r);
}
