#ifndef BUILTINS_H
#define BUILTINS_H 1

/* Bit operations that gcc and clang provide as builtins, each with a
 * portable fallback for other compilers.
 */

#include "types.h"

#ifdef __GNUC__
    /* true if x is a power of 2; x must not be 0 */
    static inline bool ispow2_u64(ulong x) {
        return __builtin_popcountl(x) == 1;
    }
#else
    static inline bool ispow2_u64(ulong x) {
        return (x & (x - 1)) == 0;
    }
#endif

#ifdef __GNUC__
    /* the number of bits set in x */
    static inline uint popcount_u64(ulong x) {
        return __builtin_popcountl(x);
    }
#else
    static inline uint popcount_u64(ulong x) {
        x -= (x >> 1) & 0x5555555555555555UL;
        x = (x & 0x3333333333333333UL) + ((x >> 2) & 0x3333333333333333UL);
        x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fUL;
        return (x * 0x0101010101010101UL) >> 56;
    }
#endif

#ifdef __GNUC__
    /* the number of trailing zero bits of x; x must not be 0 */
    static inline uint trailing_zeroes_u64(ulong x) {
        return __builtin_ctzl(x);
    }
#else
    static inline uint trailing_zeroes_u64(ulong x) {
        uint n = 0;
        if ((x & 0xffffffff) == 0) n += 32;
        if (((x >> n) & 0xffff) == 0) n += 16;
        if (((x >> n) & 0xff) == 0) n += 8;
        if (((x >> n) & 0x0f) == 0) n += 4;
        if (((x >> n) & 0x03) == 0) n += 2;
        return ((x >> n) & 1) ? n : n + 1;
    }
#endif

#ifdef __GNUC__
    /* the number of leading zero bits of x; x must not be 0 */
    static inline uint leading_zeroes_u64(ulong x) {
        return __builtin_clzl(x);
    }
#else
    static inline uint leading_zeroes_u64(ulong x) {
        uint n = 0;
        if ((x & 0xffffffff00000000UL) == 0) n += 32;
        if (((x << n) & 0xffff000000000000UL) == 0) n += 16;
        if (((x << n) & 0xff00000000000000UL) == 0) n += 8;
        if (((x << n) & 0xf000000000000000UL) == 0) n += 4;
        if (((x << n) & 0xc000000000000000UL) == 0) n += 2;
        return ((x << n) & 0x8000000000000000UL) ? n : n + 1;
    }
#endif

#ifdef __GNUC__
    /* 1 + the index of the lowest set bit of x, or 0 if x is 0 */
    static inline uint ffs_u32(uint x) {
        return __builtin_ffs((int)x);
    }
#else
    static inline uint ffs_u32(uint x) {
        return x ? 1 + trailing_zeroes_u64((ulong)x) : 0;
    }
#endif

#endif
