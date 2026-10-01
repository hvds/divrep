#ifndef COULTAU_H
#define COULTAU_H

#include <gmp.h>
#include "types.h"
#include "ptypes.h"

typedef unsigned char bool;

typedef enum {
    FS_INIT = 0,
    FS_TRIAL,
    FS_POWER,
    FS_LARGE,
    FS_TERM,
} fs_state_t;

#define MAX_FACTORS 128

typedef struct factor_state_s {
    fs_state_t state;
    mpz_t n;    /* remaining number to be factored */
    mpz_t f;    /* new factor found */
    int e;      /* new exponent found */
    int ef;     /* exponent multiplier */
    UV tlim;    /* p^2 limit checked by trial division */

    /* used only for trial division phase */
    UV sp;      /* smallprime index */
    UV un;

    /* used only after trial division phase */
    int log;    /* verbose_level */
    int ntofac; /* number of additional factors in tofac_stack[] */
    mpz_t tofac_stack[MAX_FACTORS];
} factor_state;


typedef struct s_tm {
    mpz_t n;    /* remaining value to test */
    uint t;     /* look for tau(n^e) = t */
    uint vi;    /* index of value being tested */
    uint e;     /* power found */
    uint state; /* next factor test to try */
    ulong bits; /* bitset showing which factor tests to try */
    ulong B1;   /* for ECM tests */
    ulong tlim; /* checked to */
} t_tm;
extern t_tm *taum;

typedef uint (*tau_failure_handler)(uint count, t_tm *taum);

extern void init_tau(uint test_rough, uint flake);
extern void done_tau(void);
extern void fs_init(factor_state* fs);
extern void fs_clear(factor_state* fs);
extern int factor_one(factor_state* fs);
extern int is_taux(mpz_t n, uint32_t k, uint32_t x);
extern void alloc_taum(uint size);
extern bool tau_multi_prep(uint i);
extern uint tau_multi_run(uint i, tau_failure_handler tfh);
extern double (*ct_ladder_model)(uint count, t_tm *tm);
extern double ct_ladder_actual, ct_ladder_charged;
extern double (*ct_prep_price)(uint t, uint e, uint nbits, ulong p,
        bool full);
extern double (*ct_pprep_price)(uint nbits, int res);
extern double ct_test_charged;
extern bool tau_prime_prep(uint i);
extern uint tau_prime_run(uint first, uint count);
extern bool tau_prime_test(mpz_t n);
/* the ladder of factoring methods tau_multi_run() climbs: rungs
 * TM_INIT..tm_rungs()-1, the mask of rungs tried at a size, running
 * rung i on tm, and the factor a successful rung found
 */
#define TM_INIT 2
extern uint tm_rungs(void);
extern ulong tm_rungmask(uint bits);
extern bool tm_rung(uint i, t_tm *tm);
extern mpz_t *tm_factor(t_tm *tm);
/* the ladder's rung masks by size, as used by tau_multi_run() */
extern const ulong *get_tmfbl(uint *out_maxb, ulong *out_lim);

#endif
