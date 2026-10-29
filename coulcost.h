#ifndef COULCOST_H
#define COULCOST_H

/* The cost table (see multibench-table), in every build. See
 * coulcost.c.
 */

#include "coul.h"

extern const char cm_default_table[];   /* timings.c, from timings */
extern const char *cm_table_sha(const char *section);
extern double cm_table_ghz(const char *section);
enum { CM_LOOP0, CM_LOOPTEST, CM_SQSETUP, CM_SQLOOP0, CM_SQTEST,
        CM_W1SITER, CM_W1SCHECK, CM_LINSETUP, CM_CAPPLY, CM_COUNT };

#endif
