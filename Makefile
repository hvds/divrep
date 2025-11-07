MPUGMP = /src/perl/Math-Prime-Util-GMP
# 2021-09-05
#MPUGMP_VER = db88b861fe
# 2023-05-15
#MPUGMP_VER = cbf87f5e18
# 2023-07-09
#MPUGMP_VER = 2389dcbc44
# 2025-07-11
MPUGMP_VER = a2907ae3b7
COUL = coulfact.c diag.c rootmod.c coultau.c pell.c prime_iterator.c coulvec.c
HOUL = coulfact.h diag.h rootmod.h coultau.h pell.h coul.h prime_iterator.h \
    coulvec.h

GCC_MAJOR := $(shell gcc -dumpversion)
ifeq "${GCC_MAJOR}" "7"
  CC_EXTRA_OPT = -ftree-loop-linear -ftree-loop-distribution -ftree-loop-im
endif
CC_OPT = -O6 -fgcse-sm -fgcse-las -fgcse-after-reload -fivopts -ftracer -funroll-loops -fvariable-expansion-in-unroller -freorder-blocks-and-partition -funswitch-loops ${CC_EXTRA_OPT}
dpcoul dpcaul dpcrul dsq12: CC_OPT = -O0

DEFINES := -DSTANDALONE

CFACTOR = ${MPUGMP}/factor.c ${MPUGMP}/ecm.c ${MPUGMP}/pbrent63.c ${MPUGMP}/isaac.c ${MPUGMP}/tinyqs.c ${MPUGMP}/squfof126.c ${MPUGMP}/simpqs.c ${MPUGMP}/primality.c ${MPUGMP}/utility.c ${MPUGMP}/gmp_main.c ${MPUGMP}/bls75.c ${MPUGMP}/real.c ${MPUGMP}/ecpp.c
HFACTOR = ${MPUGMP}/factor.h
ifeq ($(MPUGMP_VER), cbf87f5e18)
    CFACTOR += ${MPUGMP}/lucas_seq.c ${MPUGMP}/rootmod.c
endif
ifeq ($(MPUGMP_VER), 2389dcbc44)
    CFACTOR += ${MPUGMP}/lucas_seq.c ${MPUGMP}/rootmod.c ${MPUGMP}/random_prime.c
endif
ifeq ($(MPUGMP_VER), a2907ae3b7)
    DEFINES += -DHAVE_MISC_UI_H
    HFACTOR += ${MPUGMP}/misc_ui.h ${MPUGMP}/poly.h
    CFACTOR += ${MPUGMP}/lucas_seq.c ${MPUGMP}/rootmod.c ${MPUGMP}/random_prime.c ${MPUGMP}/misc_ui.c ${MPUGMP}/poly.c
endif

# temporary, avoid messing up
DEFINES += -DLARGE_MIN -DTRACK_STATS

pcoul dpcoul: DEFINES += -DTYPE_o
pcaul dpcaul: DEFINES += -DTYPE_a
pcrul dpcrul: DEFINES += -DTYPE_r

ifdef SQONLY
    DEFINES += -DSQONLY
endif
ifdef CHECK_OVERFLOW
    DEFINES += -DCHECK_OVERFLOW
endif
ifdef VERBOSE
    DEFINES += -DVERBOSE
endif
ifdef LARGE_MIN
    DEFINES += -DLARGE_MIN
endif
ifdef TRY_HARDER
    DEFINES += -DTRY_HARDER
endif
ifdef TRACK_STATS
    DEFINES += -DTRACK_STATS
endif
ifdef DEBUG_ALL
    DEFINES += -DDEBUG_ALL
endif
ifdef NATIVE
    CC_OPT += -march=native
endif

default: pcoul
all: pcoul dpcoul pcaul dpcaul pcrul dpcrul

pcoul dpcoul pcaul dpcaul pcrul dpcrul: Makefile coul.c ${COUL} ${HOUL} ${CFACTOR} ${HFACTOR}
	gcc -o $@ -g ${CC_OPT} ${DEFINES} coul.c ${COUL} ${CFACTOR} -I${MPUGMP} -lgmp -lm -lrt

test_pell: Makefile test_pell.c pell.c coultau.c rootmod.c coulfact.c prime_iterator.c ${HOUL} ${CFACTOR} ${HFACTOR}
	gcc -o test_pell -g ${CC_OPT} ${DEFINES} test_pell.c pell.c coultau.c rootmod.c coulfact.c prime_iterator.c ${CFACTOR} -I${MPUGMP} -lgmp -lm

ftest: Makefile ftest.c coultau.c prime_iterator.c ${HOUL} ${CFACTOR} ${HFACTOR}
	gcc -o ftest -g ${CC_OPT} ${DEFINES} ftest.c coultau.c prime_iterator.c ${CFACTOR} -I${MPUGMP} -lgmp -lm

speed: Makefile speed.c prime_iterator.c ${HFACTOR} ${MPUGMP}/gmp_main.c
	gcc -o speed -g ${CC_OPT} ${DEFINES} speed.c prime_iterator.c ${CFACTOR} -I${MPUGMP} -lgmp -lm

sq12 dsq12: Makefile sq12.c diag.c coultau.c prime_iterator.c diag.h coultau.h prime_iterator.h ${CFACTOR} ${HFACTOR}
	gcc -o $@ -g ${CC_OPT} ${DEFINES} sq12.c diag.c coultau.c prime_iterator.c ${CFACTOR} -I${MPUGMP} -lgmp -lm -lrt
