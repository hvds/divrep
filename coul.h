#ifndef COUL_H
#define COUL_H

#include <assert.h>
#include <gmp.h>
#include "types.h"
#include "prime_iterator.h"

double elapsed(void);
double seconds(double t1);
void fail(char *format, ...);
void fail_silent(void);
void report(char *format, ...);

/* 'divisors[i].div' is a list of divisors of 'i' in descending order of
 * highest prime factor, then ascending. 'high' is the highest prime
 * factor of 'i'; 'alldiv' is the number of factors; 'highdiv' is the
 * number of factors that are a multiple of 'high'; 'sumpm' is sum{p_j - 1}
 * of the primes dividing 'i', with multiplicity; 'gcddm' is gcd{d_j - 1}
 * of the divisors of i; 'sqrt' is sqrt(i) if integer, else 0.
 * Eg divisors[18] = {
 *   alldiv = 6, highdiv = 4, high = 3, sumpm = 5 = (3-1)+(3-1)+(2-1),
 *   gcddm = 1, sqrt = 0, div = = [3, 6, 9, 18, 2, 1]
 * }
 * whereas divisors[65].gcddm = gcd(1-1, 5-1, 13-1, 65-1) = 4.
 */
typedef struct s_divisors {
    uint alldiv;    /* number of divisors of i */
    uint highdiv;   /* number of divisors that are multiples of 'high' */
    uint high;      /* highest prime dividing i */
    uint sumpm;     /* sum{p_j - 1} of primes dividing i /*/
    uint gcddm;     /* gcd{d_j - 1} of divisors of i */
    uint sqrt;      /* square root of i, or 0 if i is not a square */
    uint *div;      /* array of divisors of i */
} t_divisors;
extern t_divisors *divisors;

/* Arrays with an entry for each x dividing target_lcm are packed: they
 * have xsize() entries, and the entry for x is at xi(x), the position of
 * x in divisors[target_lcm].div. See prep_fact().
 */
extern ushort *div_lookup;      /* xi(x) for x | target_lcm, else DIV_NONE */
extern uint div_lookup_size;    /* target_lcm + 1 */
extern uint div_count;          /* number of divisors of target_lcm */
#define DIV_NONE ((ushort)~0)
static inline uint xsize(void) {
    return div_count;
}
static inline uint xi(uint x) {
    assert(x < div_lookup_size && div_lookup[x] != DIV_NONE);
    return div_lookup[x];
}

/* the small primes available for allocation, see prep_primes() */
extern uint nsprimes;
extern uint *sprimes;
extern size_t pfree_vecsize;   /* uints in a bit vector of sprimes[] */

/* Each level of "recursion" allocates one prime power p^{x-1} with x | n
 * to one value v_i. It may be "forced", in which case it is part of a
 * group of simultaneous allocations of the same p to different i (and
 * in which case derecursion should unwind the whole group), or "unforced",
 * in which case no other v_j will be divisible by p.
 * Each level has a node, the state once the allocations up to and
 * including that level are made, and an act, the loop at that level
 * that makes them: nodes[l] is reached from nodes[l - 1] by acts[l].
 * An act's action says which kind of allocation it makes, or that it is
 * never iterated over: the dummy level at 0 and before any initial
 * squares (see prep_presquare()), and the levels an -I pattern fixes.
 * Those count as forced wherever unforced levels are told apart.
 * Some searches instead take over from a level while they run, and
 * progress lines show them by a suffix rather than by the allocation at
 * that level: any levels above it are part of the search.
 */
typedef enum {
    A_UNFORCED = 0,
    A_FORCED,
    A_BASE,         /* level 0, so there is always a prev_node */
    A_PRESQ,        /* the dummy level before initial squares */
    A_FIXED,        /* fixed by an -I pattern */
    A_MIDP,         /* -W's sweep, walk_midp() */
    A_6X,           /* the STRATEGY_6X walk, walk_6x() */
    A_FLIP,         /* run_flip_pqsq(), its allocation withdrawn */

    A_NONE          /* none of the above; also the number of actions */
} e_action;

/* The positions at which no allocation may be made below a node, as
 * bits by position (needs MAXK <= 64 * DIS_WORDS); gen changes whenever
 * v[] is rewritten. See dis_pos().
 */
#define DIS_WORDS 2
typedef struct s_dis {
    ulong gen;
    ulong v[DIS_WORDS];
} t_dis;

typedef struct s_node {
    uint level;     /* index of this entry */
    bool have_min;  /* we have passed any minp requirement */
    uint have_square;   /* number of v_i residues forced square so far */
    uint nextpi;    /* index of least prime not yet allocated */
    ulong maxp;     /* highest prime allocated so far, or never_unforced() */
    ulong *cap;     /* if set, caps p of p^{x-1} at v_i below here, cap_at() */
    ulong *capv;    /* storage for cap, once this node has set its own */
    ulong *wfloor;  /* the -W threshold this node was swept above, or NULL */
    t_dis *dis;     /* positions disallowed below here, or NULL before a batch */
    struct s_kern *kern;    /* the plan of -k for a batch complete here */
    uint vi_depth;  /* depth of this allocation */
    uint *pfreev;   /* bit vector of available primes */
    uint fp_need;   /* bitvector of forcedp still to apply */
    mpz_t aq;       /* running LCM of allocated p^x */
    mpz_t rq;       /* running CRT of (-i) % p^x */
} t_node;
extern t_node *nodes;
extern uint cur_batch_level;

/* What -k does in a batch, planned once the batch is complete and kept
 * with its node (see kern_state()): whether it applies at all, its bound,
 * and as bit vectors the positions it applies to and those passed over.
 * It applies to a batch that fixes exactly one square, unless that is
 * one STRATEGY_6X takes (2.z^2 at v_i, i >= 2), which has its own loop
 * at v_{i-2} and gains nothing from the pass.
 */
typedef struct s_kern {
    int id;             /* batch_alloc when it was planned */
    bool on;
    ulong b;            /* the bound of -k, 0 if it is not to apply */
    ulong at, passed;   /* needs MAXK_KERN <= 64 */
} t_kern;

/* the plan of -k for the current batch, if any */
static inline t_kern *kern_cur(void) {
    return nodes[cur_batch_level].kern;
}

/* true if -k applies to this batch */
static inline bool kern_batch(void) {
    t_kern *ks = kern_cur();
    return ks && ks->on && ks->b;
}

/* True if v_i is a position that -k applies to in this batch; needs
 * MAXK_KERN <= 64, as does kern_passed().
 */
static inline bool kern_at(uint vi) {
    return kern_batch() && ((kern_cur()->at >> vi) & 1);
}

typedef struct s_act {
    uint level;     /* index of this entry */
    e_action action;
    bool next_best; /* vi is known stable result of best_v() */
    bool unsorted;  /* this level is not where best_v() would put it */
    uint choice_strategy;   /* the strategy in force when vi was chosen */
    /* The positions disallowed below the node this act reaches, where it
     * holds them itself: for a batch complete there, or for v_i changed
     * from those at dis_from as they were at generation dis_from_gen
     * (see dis_apply()).
     */
    t_dis dis;
    t_dis *dis_from;
    ulong dis_from_gen;
    uint dis_vi;
    /* Loop of allocations at this level: whether, and above which
     * multiple of aq, an allocation can be rejected early (see
     * reject_single()), and whether aq is a single limb.
     */
    bool rj_ok, rj_limb;
    ulong rj_mult;
    /* Likewise for reject_square(), below a fixed value v_j = q.z^g:
     * rs_ok if it applies to this loop, rs_d the difference of offsets
     * j - i, and rs_endr for p^2 below a square the greatest z for which
     * v_j is within zmax, else 0.
     */
    bool rs_ok;
    long rs_d;
    ulong rs_endr;
    uint vi;        /* allocation of p^x into v_i */
    prime_iterator piter;
    ulong p;
    uint x;
    /* (optional) union */
        uint bi;    /* batch index, if forced */
    /* .. with */
        uint di;    /* divisor index, if unforced */
        uint ti;    /* target tau for v_i */
        ulong limp; /* limit for p */
        uint max_at;/* which max value used for limp calculation */
    /* end union */
} t_act;
extern t_act *acts;

/* Each value v_0 to v_{k-1} has had 'level' allocations of prime powers
 * p_i^{x_i-1}; q tracks the product of those prime powers, and t tracks
 * our target tau - starting at n, and divided by x_i on each allocation.
 */
typedef struct s_allocation {
    ulong p;
    uint x;
    uint t;
    uint level;     /* the level that made this allocation */
    mpz_t q;
    mpz_t lim;
} t_allocation;
typedef struct s_value {
    t_allocation *alloc;    /* size maxfact */
} t_value;
extern t_value *value;

#endif
