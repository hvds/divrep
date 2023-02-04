#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "coul.h"

/* from MPUG */
#include "gmp_main.h"
#include "utility.h"

mpz_t np_p;
mpz_t uc_minusvi;
mpz_t uc_px;
mpz_t sum;
/* simplified access */
#define Z(x) (x)
#define ZP(x) &(x)

t_level l_old, l_new;

void init(void) {
    _GMP_init();
    mpz_init(np_p);
    mpz_init(uc_minusvi);
    mpz_init(uc_px);
    mpz_init(l_old.aq);
    mpz_init(l_old.rq);
    mpz_init(l_new.aq);
    mpz_init(l_new.rq);
    mpz_init(sum);
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

/* copy from coul.c */
static inline mpz_t *PARAM_TO_PTR(__mpz_struct *z) {
    return (mpz_t *)z;
}
void update_chinese(t_level *old, t_level *new, uint vi, mpz_t px) {
    mpz_t zarray[4];
    mpz_t *pxp = PARAM_TO_PTR(px);
    mpz_set_si(Z(uc_minusvi), -(long)vi);

    /* v_0 == -i (mod 2^e) can be upgraded to v_0 = 2^e - i (mod 2^{e + 1}) */
    if (mpz_even_p(px)) {
        mpz_add(Z(uc_minusvi), Z(uc_minusvi), px);
        mpz_mul_2exp(Z(uc_px), px, 1);
        pxp = ZP(uc_px);
    }

    /* TODO: write a custom chinese() */
    memcpy(&zarray[0], old->rq, sizeof(mpz_t));
    memcpy(&zarray[1], Z(uc_minusvi), sizeof(mpz_t));
    memcpy(&zarray[2], old->aq, sizeof(mpz_t));
    memcpy(&zarray[3], *pxp, sizeof(mpz_t));
    if (chinese(new->rq, new->aq, &zarray[0], &zarray[2], 2))
        return;
    fprintf(stderr, "chinese failed");
    exit(1);
}

void main(int argc, char **argv) {
    if (argc != 2)
        exit(1);
    ulong target = strtoul(argv[1], NULL, 10);
    ulong p = 2;
    init();

#if 0
    ulong sum = 0;
    while (p < target) {
        sum += p;
        p = next_prime(p);
    }
    printf("%lu: %lu\n", target, sum);
#elsif 0
    ulong sum = 0;
    PRIME_ITERATOR(iter);
    while (p < target) {
        sum += p;
        p = prime_iterator_next(&iter);
    }
    prime_iterator_destroy(&iter);
    printf("%lu: %lu\n", target, sum);
#else
    mpz_t px, zsum;
    mpz_init_set_ui(sum, 0);
    mpz_init(px);
    mpz_set_ui(l_old.aq, 1311710400);
    mpz_set_ui(l_old.rq, 1138387546);
    PRIME_ITERATOR(iter);
    p = 17;
    prime_iterator_setprime(&iter, p);
    while (p < target) {
        mpz_ui_pow_ui(px, p, 2);
        update_chinese(&l_old, &l_new, 7, px);
        mpz_add(sum, sum, l_new.rq);
        p = prime_iterator_next(&iter);
    }
    gmp_printf("%lu: %Zu\n", target, sum);
#endif

    exit(0);
}
