#ifndef COULFACT_H
#define COULFACT_H 1
#include "types.h"
#include <gmp.h>

typedef struct s_ppow {
    ulong p;
    uint e;
} t_ppow;
typedef struct s_fact {
    uint count;
    uint size;
    t_ppow *ppow;
} t_fact;
typedef struct s_zpow {
    mpz_t p;
    uint e;
} t_zpow;
typedef struct s_zfact {
    uint count;
    uint size;
    t_zpow *ppow;
} t_zfact;

/* init_coulfact/done_coulfact only needed if calling chinese_ppow_z */
extern void init_coulfact(void);
extern void done_coulfact(void);

extern void init_fact(t_fact *f);
extern void free_fact(t_fact *f);
extern void add_fact(t_fact *f, t_ppow pp);
extern void reverse_fact(t_fact *f);
extern void init_zfact(t_zfact *f);
extern void free_zfact(t_zfact *f);
extern void add_zfact(t_zfact *f, t_zpow pp);
extern void simple_fact(uint n, t_fact *f);
extern uint simple_tau(t_fact *f);
extern uint simple_valuation(ulong n, ulong p);
extern uint simple_prime_count(ulong n);
extern uint tiny_gcd(uint a, uint b);
extern ulong simple_gcd(ulong a, ulong b);
extern ulong small_divmod(mpz_t za, mpz_t zb, ulong p);
extern ulong simple_invert(ulong d, ulong m);
extern ulong ppow_invert(ulong d, ulong p, ulong m);
extern bool u64_bpsw(ulong n);
extern bool chinese_ppow_shared(mpz_t rp, mpz_t ap, mpz_t r, mpz_t a,
        ulong p, ulong m, ulong s, ulong am);
extern void chinese_ppow_zai(mpz_t rp, mpz_t r, mpz_t a, mpz_t m, mpz_t s,
        mpz_t ai);
extern bool chinese_ppow_z(mpz_t rp, mpz_t ap, mpz_t r, mpz_t a,
        ulong p, mpz_t m, mpz_t s);
extern int _mpz_comparator(const void *va, const void *vb);

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

/* CRT for a prime power: as chinese_ppow() but with known inverse ai */
static inline void chinese_ppow_ai(
    mpz_t rp, mpz_t r, mpz_t a, ulong m, ulong s, ulong ai
) {
    ulong c = s + m - mpz_fdiv_ui(r, m);
    if (c >= m)
        c -= m;
    mpz_set(rp, r);
    mpz_addmul_ui(rp, a, mulmod_u64(c, ai, m));
}

/* CRT for a prime power: given v == r (mod a) with 0 <= r < a, and
 * v == s (mod m) with m = p^e < 2^62 and 0 <= s < m, sets rp to the least
 * such v, sets ap to lcm(a, m), and returns TRUE; returns FALSE if the two
 * are inconsistent.
 */
static inline bool chinese_ppow(
    mpz_t rp, mpz_t ap, mpz_t r, mpz_t a, ulong p, ulong m, ulong s
) {
    ulong am = mpz_fdiv_ui(a, m);
    if (am % p == 0)
        return chinese_ppow_shared(rp, ap, r, a, p, m, s, am);
    chinese_ppow_ai(rp, r, a, m, s, ppow_invert(am, p, m));
    mpz_mul_ui(ap, a, m);
    return 1;
}

#endif
