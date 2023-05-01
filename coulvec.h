#ifndef COULVEC_H

#include "coulfact.h"

void cvec_init(uint n, uint k, mpz_t *min, uint *target_t);
void cvec_done(void);

void apply_m(uint m, t_fact *fm);
void suppress(uint m, uint v, bool depend);
void apply_modfix(mpz_t m, mpz_t v, bool negate, uint limit);
void cvec_pack(uint chunksize, double minratio);
bool cvec_mult(mpz_t *mod_mult, mpz_t *mult);
bool cvec_testv(mpz_t value);
bool cvec_test(mpz_t value, mpz_t *mod, mpz_t *mult);
bool cvec_test_ui(ulong value, mpz_t *mod, mpz_t *mult);
void cvec_prep_test(mpz_t *mod, mpz_t *mult);
bool cvec_test_prepped(ulong value);

#endif
