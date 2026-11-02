#ifndef COULMINT_H
#define COULMINT_H

#include <gmp.h>
#include "coul.h"

/* The minimum contribution from unused primes satisfying a given tau,
 * memoized: see mintau_r().
 */

extern uint restricted_count;

void prep_mintau(uint lcm);
void done_mintau(void);
void mintau(t_node *cur_node, mpz_t mint, uint t);
void mintau_restricted(t_node *cur_node, mpz_t mint, uint t, uint r);
void mintau_at(t_node *cur_node, mpz_t mint, uint t, uint vi);
void mintau_restricted_at(
    t_node *cur_node, mpz_t mint, uint t, uint r, uint vi
);

#endif
