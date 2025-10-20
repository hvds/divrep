#ifndef COUL_H
#define COUL_H

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
 * of the divisors of i.
 * Eg divisors[18] = {
 *   alldiv = 6, highdiv = 4, high = 3, sumpm = 5 = (3-1)+(3-1)+(2-1),
 *   gcddm = 1, div = = [3, 6, 9, 18, 2, 1]
 * }
 * whereas divisors[65].gcddm = gcd(1-1, 5-1, 13-1, 65-1) = 4.
 */
typedef struct s_divisors {
    uint alldiv;    /* number of divisors of i */
    uint highdiv;   /* number of divisors that are multiples of 'high' */
    uint high;      /* highest prime dividing i */
    uint sumpm;     /* sum{p_j - 1} of primes dividing i /*/
    uint gcddm;     /* gcd{d_j - 1} of divisors of i */
    uint *div;      /* array of divisors of i */
} t_divisors;
extern t_divisors *divisors;

/* Each level of "recursion" allocates one prime power p^{x-1} with x | n
 * to one value v_i. It may be "forced", in which case it is part of a
 * batch of simultaneous allocations of the same p to different i (and
 * in which case derecursion should unwind the whole batch), or "unforced",
 * in which case no other v_j will be divisible by p.
 */
typedef struct s_level {
    uint level;     /* index of this entry */
    uint is_forced; /* this is a forced-prime entry if 1 */
                    /* this is a dummy entry for initial squares if 2 */
    bool have_min;  /* we have passed any minp requirement */
    bool next_best; /* vi is known stable result of best_v() */
    uint vi;        /* allocation of p^x into v_i */
    prime_iterator piter;
    ulong p;
    uint x;
    uint have_square;   /* number of v_i residues forced square so far */
    uint nextpi;    /* index of least prime not yet allocated */
    ulong maxp;     /* highest prime allocated so far */
    uint *vlevel;   /* number of elements allocated to each values[vi] */
    uint *pfreev;   /* bit vector of available primes */
    /* (optional) union */
        uint bi;    /* batch index, if forced */
    /* .. with */
        uint di;    /* divisor index, if unforced */
        uint ti;    /* target tau for v_i */
        ulong limp; /* limit for p */
        uint max_at;/* which max value used for limp calculation */
    /* end union */
    mpz_t aq;       /* running LCM of allocated p^x */
    mpz_t rq;       /* running CRT of (-i) % p^x */
} t_level;
extern t_level *levels;

/* Each value v_0 to v_{k-1} has had 'level' allocations of prime powers
 * p_i^{x_i-1}; q tracks the product of those prime powers, and t tracks
 * our target tau - starting at n, and divided by x_i on each allocation.
 */
typedef struct s_allocation {
    ulong p;
    uint x;
    uint t;
    mpz_t q;
    mpz_t lim;
} t_allocation;
typedef struct s_value {
    t_allocation *alloc;    /* size maxfact */
} t_value;
extern t_value *value;

#endif
