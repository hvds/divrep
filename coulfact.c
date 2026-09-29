#include <stdlib.h>
#include "coulfact.h"
#include "gmp_main.h"   /* prime_count */

static mpz_t cp_z;  /* chinese_ppow_z */

/* init_coulfact/done_coulfact only needed if calling chinese_ppow_z */
void init_coulfact(void) {
    mpz_init(cp_z);
}
void done_coulfact(void) {
    mpz_clear(cp_z);
}

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

/* Returns the inverse of d mod m = p^e for prime p and m < 2^62, or 0
 * if p divides d.
 * Calculated as the inverse mod p, lifted by Newton steps i <- i(2 - d.i),
 * each doubling the power of p it is correct to.
 */
ulong ppow_invert(ulong d, ulong p, ulong m) {
    ulong i = simple_invert(d % p, p);
    ulong pm = p;
    while (pm < m) {
        pm = (pm > m / pm) ? m : pm * pm;
        ulong di = mulmod_u64(d, i, m);
        i = mulmod_u64(i, 2 + m - di, m);
    }
    return i;
}

/* CRT for a prime power: chinese_ppow() where it is known p | a.
 * If p^e divides a, v == s (mod m) is implied by v == r (mod a) or
 * contradicts it; else a = a'.p^f with 0 < f < e and p not dividing a',
 * so a solution needs p^f | s - r, * and then
 * t == ((s - r) / p^f) / a' (mod p^{e-f}).
 */
bool chinese_ppow_shared(
    mpz_t rp, mpz_t ap, mpz_t r, mpz_t a, ulong p, ulong m, ulong s, ulong am
) {
    ulong c = s + m - mpz_fdiv_ui(r, m);
    if (c >= m)
        c -= m;
    if (am == 0) {
        if (c)
            return 0;
        mpz_set(rp, r);
        mpz_set(ap, a);
        return 1;
    }
    ulong pf = 1;
    while (am % p == 0) {
        am /= p;
        pf *= p;
    }
    if (c % pf)
        return 0;
    m /= pf;
    ulong t = mulmod_u64(c / pf, ppow_invert(am, p, m), m);
    mpz_set(rp, r);
    mpz_addmul_ui(rp, a, t);
    mpz_mul_ui(ap, a, m);
    return 1;
}

/* As chinese_ppow_ai() for mpz_t m, s and ai = 1/a (mod m), except
 * that s may be any value == the residue (mod m). rp must not be any
 * of the inputs, and is the only mpz_t written.
 */
static void chinese_ppow_zai(
    mpz_t rp, mpz_t r, mpz_t a, mpz_t m, mpz_t s, mpz_t ai
) {
    mpz_sub(rp, s, r);
    mpz_mul(rp, rp, ai);
    mpz_mod(rp, rp, m);
    mpz_mul(rp, rp, a);
    mpz_add(rp, rp, r);
}

/* As chinese_ppow() for m = p^e too large for it, except that s may be
 * any value == the residue (mod m).
 */
bool chinese_ppow_z(
    mpz_t rp, mpz_t ap, mpz_t r, mpz_t a, ulong p, mpz_t m, mpz_t s
) {
    mpz_mod(ap, a, m);
    if (mpz_sgn(ap) == 0) {
        mpz_sub(rp, s, r);
        if (!mpz_divisible_p(rp, m))
            return 0;
        mpz_set(rp, r);
        mpz_set(ap, a);
        return 1;
    }
    uint f = 0;
    while (mpz_divisible_ui_p(ap, p)) {
        mpz_divexact_ui(ap, ap, p);
        ++f;
    }
    if (f == 0) {
        mpz_invert(ap, ap, m);
        chinese_ppow_zai(rp, r, a, m, s, ap);
        mpz_mul(ap, a, m);
        return 1;
    }
    mpz_sub(rp, s, r);
    mpz_ui_pow_ui(cp_z, p, f);
    if (!mpz_divisible_p(rp, cp_z))
        return 0;
    mpz_divexact(rp, rp, cp_z);
    mpz_divexact(cp_z, m, cp_z);
    mpz_invert(ap, ap, cp_z);
    mpz_mul(rp, rp, ap);
    mpz_mod(rp, rp, cp_z);
    mpz_mul(ap, a, cp_z);
    mpz_mul(rp, rp, a);
    mpz_add(rp, rp, r);
    return 1;
}
