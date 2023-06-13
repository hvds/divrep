#ifndef COULVEC_H

#include "coulfact.h"

typedef struct s_context t_context;

t_context *cvec_init(uint n, uint k, mpz_t *min, uint *target_t);
void context_done(t_context *cx);
void cvec_done(t_context *cx);

void apply_m(t_context *cx, uint m, t_fact *fm);
void suppress(t_context *cx, uint m, uint v, bool depend);
void apply_modfix(t_context *cx, mpz_t m, mpz_t v, bool negate, uint limit);
void cvec_pack(t_context *cx, uint chunksize, double minratio);
bool cvec_mult(t_context *cx, mpz_t *mod_mult, mpz_t *mult);
bool cvec_testv(t_context *cx, mpz_t value);
bool cvec_test(t_context *cx, mpz_t value, mpz_t *mod, mpz_t *mult);
bool cvec_test_ui(t_context *cx, ulong value, mpz_t *mod, mpz_t *mult);
void cvec_prep_test(t_context *cx, mpz_t *mod, mpz_t *mult);
bool cvec_test_prepped(t_context *cx, ulong value);

#endif
