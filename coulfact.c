#include <stdlib.h>
#include "coulfact.h"
#include "gmp_main.h"   /* prime_count */

/* for sorting */
int _mpz_comparator(const void *va, const void *vb) {
    return mpz_cmp(*(mpz_t *)va, *(mpz_t *)vb);
}

void init_fact(t_fact *f) {
    f->count = 0;
    f->size = 16;
    f->ppow = malloc(f->size * sizeof(t_ppow));
}
void free_fact(t_fact *f) {
    free(f->ppow);
}
void add_fact(t_fact *f, t_ppow pp) {
    uint count = f->count++;
    if (f->count > f->size) {
        uint size = f->size * 2;
        f->ppow = realloc(f->ppow, size * sizeof(t_ppow));
        f->size = size;
    }
    f->ppow[count] = pp;
}
void reverse_fact(t_fact *f) {
    t_ppow pp;
    uint c = f->count;
    for (uint i = 0; i + i + 1 < c; ++i) {
        uint j = c - i - 1;
        pp = f->ppow[i];
        f->ppow[i] = f->ppow[j];
        f->ppow[j] = pp;
    }
}

void init_zfact(t_zfact *f) {
    f->count = 0;
    f->size = 16;
    f->ppow = malloc(f->size * sizeof(t_zpow));
    for (int i = 0; i < f->size; ++i)
        mpz_init(f->ppow[i].p);
}
void free_zfact(t_zfact *f) {
    for (int i = 0; i < f->size; ++i)
        mpz_clear(f->ppow[i].p);
    free(f->ppow);
}
void add_zfact(t_zfact *f, t_zpow pp) {
    uint count = f->count++;
    if (f->count > f->size) {
        uint size = f->size * 2;
        f->ppow = realloc(f->ppow, size * sizeof(t_zpow));
        for (int i = f->count; i < size; ++i)
            mpz_init(f->ppow[i].p);
        f->size = size;
    }
    mpz_set(f->ppow[count].p, pp.p);
    f->ppow[count].e = pp.e;
}

uint try_simple_fact(uint n, uint d, t_fact *f) {
    uint e = 0;
    while ((n % d) == 0) {
        n /= d;
        ++e;
    }
    if (e) {
        t_ppow pp;
        pp.p = d;
        pp.e = e;
        add_fact(f, pp);
    }
    return n;
}

void simple_fact(uint n, t_fact *f) {
    uint d = 3;
    if (n > 1)
        n = try_simple_fact(n, 2, f);
    while (n > 1) {
        n = try_simple_fact(n, d, f);
        d += 2;
    }
    return;
}

uint simple_tau(t_fact *f) {
    uint t = 1;
    for (uint i = 0; i < f->count; ++i)
        t *= f->ppow[i].e + 1;
    return t;
}

uint simple_valuation(ulong n, ulong p) {
    uint v = 0;
    while ((n % p) == 0) {
        ++v;
        n /= p;
    }
    return v;
}

uint simple_prime_count(ulong n) {
    mpz_t zn, zc;
    mpz_init_set_ui(zn, n);
    mpz_init(zc);
    prime_count(zc, zn);
    uint c = mpz_get_ui(zc);
    mpz_clear(zn);
    mpz_clear(zc);
    return c;
}

uint tiny_gcd(uint a, uint b) {
    if (a > b)
        return tiny_gcd(b, a);
    if (a == 0)
        return b;
    return tiny_gcd(b % a, a);
}

ulong simple_gcd(ulong a, ulong b) {
    if (a > b)
        return simple_gcd(b, a);
    if (a == 0)
        return b;
    return simple_gcd(b % a, a);
}

/* 64x64->64 modular multiply. __uint128_t is a GCC/clang extension
 * (widely available on 64-bit targets); portable fallback avoids
 * overflow via repeated doubling for other compilers.
 */
#ifdef __GNUC__
static inline ulong mulmod_u64(ulong a, ulong b, ulong m) {
    return (ulong)(((__uint128_t)a * (__uint128_t)b) % m);
}
#else
static inline ulong mulmod_u64(ulong a, ulong b, ulong m) {
    ulong result = 0;
    a %= m;
    while (b) {
        if (b & 1)
            result = (result + a) % m;
        a = (a + a) % m;
        b >>= 1;
    }
    return result;
}
#endif

/* Returns the inverse of d mod m, or 0 if no inverse exists. We expect
 * to call this only with prime m, but do not enforce that.
 */
ulong simple_invert(ulong d, ulong m) {
    long t = 0;
    long newt = 1;
    long r = (long)m;
    long newr = (long)(d % m);
    while (newr != 0) {
        long q = r / newr;
        long tmp = t - q * newt;
        t = newt;
        newt = tmp;
        tmp = r - q * newr;
        r = newr;
        newr = tmp;
    }
    if (r > 1)
        return 0;
    if (t < 0)
        t += (long)m;
    return (ulong)t;
}

/* Returns (za / zb) mod p, or p if no inverse exists.
 */
ulong small_divmod(mpz_t za, mpz_t zb, ulong p) {
    ulong zb_r = mpz_fdiv_ui(zb, p);
    ulong inv = simple_invert(zb_r, p);
    if (inv == 0)
        return p;
    ulong za_r = mpz_fdiv_ui(za, p);
    return mulmod_u64(inv, za_r, p);
}
