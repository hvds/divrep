#ifndef PRIME_ITERATOR_H
#define PRIME_ITERATOR_H

#include "ptypes.h"

typedef struct {
    UV p;
    UV segment_start;
    UV segment_bytes;
    unsigned char* segment_mem;
} prime_iterator;

#define PRIME_ITERATOR(i)  prime_iterator i = {2, 0, 0, 0}

extern void prime_iterator_global_startup(void);
extern void prime_iterator_global_shutdown(void);

extern void prime_iterator_destroy(prime_iterator *iter);
extern UV prime_iterator_next(prime_iterator *iter);
extern UV prime_iterator_prev(prime_iterator *iter);
extern void prime_iterator_setprime(prime_iterator *iter, UV n);
extern int prime_iterator_isprime(prime_iterator *iter, UV n);

extern UV* sieve_to_n(UV n, UV* count);

#endif
