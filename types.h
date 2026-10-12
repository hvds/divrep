#ifndef TYPES_H
#define TYPES_H 1
typedef unsigned char uchar;
typedef unsigned int uint;
typedef unsigned long ulong;
typedef long slong;
typedef unsigned char bool;

/* An unsigned 128-bit type, where the compiler has one: gcc and clang
 * define __SIZEOF_INT128__ on targets that support it. Code that needs
 * it should test HAVE_UINT128, and have a fallback.
 */
#ifdef __SIZEOF_INT128__
typedef unsigned __int128 uint128;
#   define HAVE_UINT128 1
#endif
#endif
