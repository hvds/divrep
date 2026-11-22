/* From 32fcf54782 on, MPUGMP carries a frozen serial copy of the SIQS
 * code from msiqs (github danaj/msiqs, its "embedded" edition), and its
 * factor.c and bls75.c call that copy's gmp_siqs(), as does coultau.c.
 * This builds the main msiqs SIQS code instead, and supplies the same
 * gmp_siqs() on top of it, so that all those callers use the main code.
 *
 * The main code has a gmp_siqs() of its own, with more arguments: we
 * build it under another name by including its siqs.c here (the Makefile
 * gives us its path), with gmp_siqs renamed for the duration.
 *
 * This file must not see MPUGMP's headers, since msiqs has its own
 * ptypes.h (included from msiqs's own directory) whose definitions,
 * croak() in particular, conflict with MPUGMP's. So the gmp_siqs() we
 * supply is declared here rather than taken from MPUGMP's siqs.h; it is
 * the one msiqs's embedded/README.md documents.
 */
#define gmp_siqs msiqs_main_siqs
#include MSIQS_SIQS_C
#undef gmp_siqs

extern mpz_t *gmp_siqs(const mpz_t n, uint32_t *nfactors,
        uint32_t trial_start, int verbose);

mpz_t *gmp_siqs(const mpz_t n, uint32_t *nfactors, uint32_t trial_start,
        int verbose) {
    /* serial, with default large-prime policies, as the embedded copy */
    return msiqs_main_siqs(n, nfactors, trial_start, verbose, 1, 0);
}
