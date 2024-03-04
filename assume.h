#ifndef ASSUME_H
#define ASSUME_H 1

/* assume(cond) is intended to give a hint to the optimizer that the
 * stated condition is always true; currently only supported for gcc.
 */

#ifdef __GNUC__
#   define assume(p) do { if (!(p)) __builtin_unreachable(); } while (0)
#else
#   define assume(p) (void)0
#endif

#endif
