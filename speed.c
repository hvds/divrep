#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <gmp.h>

#include "coul.h"

/* from MPUG */
#include "gmp_main.h"
#include "prime_iterator.h"

mpz_t np_p;
/* simplified access */
#define Z(x) x

void init(void) {
    _GMP_init();
    mpz_init(np_p);
}

/* copy from coul.c */
ulong next_prime(ulong cur) {
    mpz_set_ui(Z(np_p), cur);
    _GMP_next_prime(Z(np_p));
    if (mpz_fits_ulong_p(Z(np_p)))
        return mpz_get_ui(Z(np_p));
    fprintf(stderr, "002 next_prime overflow\n");
    exit(1);
}

void main(int argc, char **argv) {
    if (argc != 2)
        exit(1);
    ulong target = strtoul(argv[1], NULL, 10);
    ulong p = 2;
    ulong sum = 0;
    init();

#ifdef TEST_1
    while (p < target) {
        sum += p;
        p = next_prime(p);
    }
#else
    PRIME_ITERATOR(iter);
    while (p < target) {
        sum += p;
        p = prime_iterator_next(&iter);
    }
    prime_iterator_destroy(&iter);
#endif

    printf("%lu: %lu\n", target, sum);
    exit(0);
}
