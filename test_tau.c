#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>

#include "coul.h"
#include "coultau.h"
#include "gmp_main.h"

/* needed for coultau.c; but not used, since we init_tau(0, 0) */
t_divisors *divisors = NULL;

void fail(char *format, ...) {
    va_list ap;
    va_start(ap, format);
    gmp_vfprintf(stderr, format, ap);
    fprintf(stderr, "\n");
    va_end(ap);
    exit(1);
}

/* For each line "n t e" on stdin, write "n t e a b": a is true if
 * is_taux() finds tau(n^e) == t, b is true if the queue of tau_multi_prep()
 * and tau_multi_run() does.
 */
int main(int argc, char **argv) {
    char buf[4096], ns[4096];
    uint t, e;
    t_tm *tm;

    _GMP_init();
    init_tau(0, 0);
    alloc_taum(1);
    tm = &taum[0];

    while (fgets(buf, sizeof(buf), stdin)) {
        if (sscanf(buf, "%s %u %u", ns, &t, &e) != 3)
            fail("cannot parse '%s'", buf);
        if (mpz_set_str(tm->n, ns, 10) != 0)
            fail("not a number: '%s'", ns);
        int direct = is_taux(tm->n, t, e);
        tm->vi = 0;
        tm->t = t;
        tm->e = e;
        int queue = tau_multi_prep(0)
                && (tm->state == 0 || tau_multi_run(1, NULL) == 0);
        printf("%s %u %u %d %d\n", ns, t, e, direct ? 1 : 0, queue ? 1 : 0);
    }
    done_tau();
    _GMP_destroy();
    return 0;
}
