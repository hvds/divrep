#include <stdlib.h>
#include <limits.h>
#include <math.h>
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

/* as invert_u64() for m < 2^32, where the divisions are faster */
uint invert_u32(uint d, uint m) {
    long t = 0;
    long newt = 1;
    uint r = m;
    uint newr = (d < m) ? d : d % m;
    while (newr != 0) {
        uint q = r / newr;
        long tmp = t - (long)q * newt;
        t = newt;
        newt = tmp;
        uint rtmp = r - q * newr;
        r = newr;
        newr = rtmp;
    }
    if (r > 1)
        return 0;
    if (t < 0)
        t += m;
    return (uint)t;
}

/* Returns the inverse of d mod m, or 0 if no inverse exists. We expect
 * to call this only with prime m, but do not enforce that.
 */
ulong invert_u64(ulong d, ulong m) {
    if (d >= m)
        d %= m;
    if (m <= UINT_MAX)
        return invert_u32((uint)d, (uint)m);
    long t = 0;
    long newt = 1;
    long r = (long)m;
    long newr = (long)d;
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
    ulong inv = invert_u64(zb_r, p);
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
    ulong i = invert_u64(d % p, p);
    ulong pm = p;
    while (pm < m) {
        pm = (pm > m / pm) ? m : pm * pm;
        ulong di = mulmod_u64(d, i, m);
        i = mulmod_u64(i, 2 + m - di, m);
    }
    return i;
}

/* Primality of n < 2^64 in single limbs, by the BPSW test just as
 * _GMP_BPSW() makes it: a strong probable prime test to base 2, then
 * the "almost extra strong" Lucas test with Baillie's parameters
 * (_GMP_is_almost_extra_strong_lucas_pseudoprime(n, 1)). Together they
 * are exact below 2^64.
 * This needs __uint128_t (see mulmod_u64()): without it u64_bpsw()
 * leaves the test to _GMP_BPSW().
 */
#ifdef __GNUC__

/* a.b/2^64 mod n, for odd n with ni = 1/n mod 2^64, and a, b < n */
static inline ulong mont_mul(ulong a, ulong b, ulong n, ulong ni) {
    __uint128_t t = (__uint128_t)a * b;
    ulong h = (ulong)(t >> 64);
    ulong mh = (ulong)(((__uint128_t)((ulong)t * ni) * n) >> 64);
    return (h >= mh) ? h - mh : h - mh + n;
}

/* 1/n mod 2^64 for odd n, by Newton's iteration */
static inline ulong mont_inv(ulong n) {
    ulong ni = n;
    for (uint i = 0; i < 5; ++i)
        ni *= 2 - n * ni;
    return ni;
}

static inline ulong mont_sub(ulong a, ulong b, ulong n) {
    return (a >= b) ? a - b : a - b + n;
}

/* strong probable prime to base 2, for odd n > 2: one is 2^64 mod n */
static inline bool u64_sprp2(ulong n, ulong ni, ulong one) {
    ulong mone = n - one, d = n - 1;
    uint s = __builtin_ctzl(d);
    d >>= s;
    /* 2^d, left to right, doubling for each bit set */
    ulong x = one;
    for (int b = 63 - __builtin_clzl(d); b >= 0; --b) {
        x = mont_mul(x, x, n, ni);
        if ((d >> b) & 1)
            x = (x >= n - x) ? x - (n - x) : x + x;
    }
    if (x == one || x == mone)
        return 1;
    while (--s) {
        x = mont_mul(x, x, n, ni);
        if (x == mone)
            return 1;
        if (x == one)
            return 0;
    }
    return 0;
}

/* the Jacobi symbol (a / n) for odd n */
static inline int u64_jacobi(ulong a, ulong n) {
    int t = 1;
    a %= n;
    while (a) {
        uint z = __builtin_ctzl(a);
        a >>= z;
        if ((z & 1) && ((n & 7) == 3 || (n & 7) == 5))
            t = -t;
        if ((a & 3) == 3 && (n & 3) == 3)
            t = -t;
        ulong r = n % a;
        n = a;
        a = r;
    }
    return (n == 1) ? t : 0;
}

static inline ulong u64_gcd(ulong a, ulong b) {
    while (b) {
        ulong r = a % b;
        a = b;
        b = r;
    }
    return a;
}

static inline bool u64_is_square(ulong n) {
    ulong r = (ulong)sqrtl((long double)n);
    while (r * r > n)
        --r;
    while ((r + 1) * (r + 1) <= n && r + 1 < (1UL << 32))
        ++r;
    return r * r == n;
}

/* the almost extra strong Lucas test, for odd n >= 13 */
static inline bool u64_aeslucas(ulong n, ulong ni, ulong one) {
    ulong P = 3;
    while (1) {
        ulong D = P * P - 4;
        ulong g = u64_gcd(n, D);
        if (g > 1 && g != n)
            return 0;
        if (u64_jacobi(D, n) == -1)
            break;
        if (P == 23 && u64_is_square(n))
            return 0;
        if (++P > 65535)
            return 0;   /* not reached: n is no square */
    }
    ulong d = n + 1;
    if (d == 0)
        return 0;       /* 2^64 - 1 = 3.5.17.257.641.65537.6700417 */
    uint s = __builtin_ctzl(d);
    d >>= s;
    /* in Montgomery form: 2, P, and V = V_k, W = V_{k+1} from k = 1 */
    ulong two = (one >= n - one) ? one - (n - one) : one + one;
    ulong Pm = (ulong)(((__uint128_t)one * P) % n);
    ulong V = Pm, W = mont_sub(mont_mul(Pm, Pm, n, ni), two, n);
    for (int b = 62 - __builtin_clzl(d); b >= 0; --b) {
        ulong T = mont_sub(mont_mul(V, W, n, ni), Pm, n);
        if ((d >> b) & 1) {
            V = T;
            W = mont_sub(mont_mul(W, W, n, ni), two, n);
        } else {
            W = T;
            V = mont_sub(mont_mul(V, V, n, ni), two, n);
        }
    }
    if (V == two || V == n - two)
        return 1;
    /* the extra strong test takes r < s - 1 */
    --s;
    while (s--) {
        if (V == 0)
            return 1;
        if (s)
            V = mont_sub(mont_mul(V, V, n, ni), two, n);
    }
    return 0;
}

bool u64_bpsw(ulong n) {
    if (n < 13)
        return n == 2 || n == 3 || n == 5 || n == 7 || n == 11;
    if (!(n & 1))
        return 0;
    ulong ni = mont_inv(n), one = -n % n;
    return u64_sprp2(n, ni, one) && u64_aeslucas(n, ni, one);
}

#else
#include "primality.h"

bool u64_bpsw(ulong n) {
    mpz_t z;
    mpz_init_set_ui(z, n);
    bool r = _GMP_BPSW(z) != 0;
    mpz_clear(z);
    return r;
}

#endif

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
void chinese_ppow_zai(
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
