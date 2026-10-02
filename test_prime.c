/* Check u64_bpsw() against _GMP_BPSW(), which it must match exactly:
 * every n below 2^22 (or 2^<arg>), squares, cubes and near-squares,
 * random values of every size, semiprimes, the ends of the range, and
 * some known pseudoprimes.
 */
#include <stdlib.h>
#include <stdio.h>

#include "coulfact.h"
#include "gmp_main.h"
#include "primality.h"

static mpz_t z;
static ulong tried = 0, bad = 0;

static void check(ulong n) {
    mpz_set_ui(z, n);
    bool mine = u64_bpsw(n), theirs = _GMP_BPSW(z) != 0;
    ++tried;
    if (mine != theirs && ++bad <= 10)
        printf("not ok - %lu: u64_bpsw() %d, _GMP_BPSW() %d\n",
                n, mine, theirs);
}

int main(int argc, char **argv) {
    uint small = (argc > 1) ? strtoul(argv[1], NULL, 10) : 22;
    _GMP_init();
    mpz_init(z);
    gmp_randstate_t rs;
    gmp_randinit_default(rs);
    gmp_randseed_ui(rs, 777);

    for (ulong n = 0; n < (1UL << small); ++n)
        check(n);
    for (ulong p = 3; p < 200000; p += 2) {
        check(p * p);
        check(p * (p + 2));
        check(p * p * p);
    }
    for (uint bits = small + 1; bits <= 64; ++bits)
        for (uint i = 0; i < 100000; ++i) {
            mpz_urandomb(z, rs, bits);
            ulong n = mpz_get_ui(z) | 1;
            check((bits == 64) ? n | (1UL << 63) : n);
        }
    for (ulong i = 0; i < 100000; ++i) {
        check(~0UL - 2 * i);
        check((1UL << 63) + 2 * i + 1);
        check((1UL << 32) + 2 * i + 1);
        check((1UL << 32) - 2 * i - 1);
    }
    for (uint i = 0; i < 200000; ++i) {
        mpz_urandomb(z, rs, 20 + i % 12);
        mpz_nextprime(z, z);
        ulong p = mpz_get_ui(z);
        mpz_urandomb(z, rs, 20 + (i / 12) % 12);
        mpz_nextprime(z, z);
        ulong q = mpz_get_ui(z);
        check(p * q);
        check(p);
        mpz_urandomb(z, rs, 33 + i % 31);
        mpz_nextprime(z, z);
        if (mpz_fits_ulong_p(z))
            check(mpz_get_ui(z));
    }
    /* strong pseudoprimes to base 2, Carmichael numbers, and the
     * least composites passing the first 7, 9 and 12 prime bases
     */
    static const ulong known[] = {
        2047, 3277, 4033, 4681, 8321, 15841, 29341, 42799, 49141, 52633,
        65281, 74665, 80581, 85489, 88357, 90751, 1194649, 12327121,
        3215031751UL, 561, 1105, 1729, 2465, 2821, 6601, 8911, 10585,
        41041, 46657, 62745, 63973, 75361, 101101,
        341550071728321UL, 3825123056546413051UL, 318665857834031151UL,
        7999252175582851UL, 585226005592931977UL,
        18446744073709551557UL, 18446744073709551533UL
    };
    for (uint i = 0; i < sizeof(known) / sizeof(known[0]); ++i)
        check(known[i]);

    printf("%s - u64_bpsw() matches _GMP_BPSW() on %lu values",
            bad ? "not ok" : "ok", tried);
    if (bad)
        printf(" (%lu differ)", bad);
    printf("\n");
    return bad ? 1 : 0;
}
