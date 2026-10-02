# Path to the Math-Prime-Util-GMP repository
MPUGMP ?= /src/perl/Math-Prime-Util-GMP

# Checkpoint SHA of the Math-Prime-Util-GMP repository, used to determine
# which files should exist. It needs to be one of the known values, or the
# Makefile needs updating:
#   2389dcbc44 (danaj master, branch point of hvds fork)
#       == b363d69b10 (hvds fork, simpqs-full branch)
#   db88b861fe (danaj master 2021-09-05)
#   cbf87f5e18 (danaj master 2023-05-15)
#   a2907ae3b7 (danaj master 2025-07-11)
#   39982f872b (danaj master v0.54 tag, CPAN release 2026-08-08)
MPUGMP_VER ?= 39982f872b
COUL = coulfact.c diag.c rootmod.c coultau.c pell.c prime_iterator.c \
    coulvec.c mock.c trace.c bench.c costtab.c
HOUL = coulfact.h diag.h rootmod.h coultau.h pell.h prime_iterator.h coul.h \
    coulvec.h mock.h trace.h bench.h coulint.h

GCC_MAJOR := $(shell gcc -dumpversion)
ifeq "${GCC_MAJOR}" "7"
  CC_EXTRA_OPT = -ftree-loop-linear -ftree-loop-distribution -ftree-loop-im
endif
CC_OPT = -O6 -fgcse-sm -fgcse-las -fgcse-after-reload -fivopts -ftracer -funroll-loops -fvariable-expansion-in-unroller -freorder-blocks-and-partition -funswitch-loops ${CC_EXTRA_OPT}
dpcoul dpcaul dpcrul dsq12: CC_OPT = -O0

# Tell MPUGMP code that we're not building the perl module.
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
ifeq ($(MPUGMP_VER), 39982f872b)
    DEFINES += -DHAVE_MISC_UI_H -DMPUG_054
    HFACTOR += ${MPUGMP}/misc_ui.h ${MPUGMP}/poly.h ${MPUGMP}/znlog.h
    CFACTOR += ${MPUGMP}/lucas_seq.c ${MPUGMP}/rootmod.c ${MPUGMP}/random_prime.c ${MPUGMP}/misc_ui.c ${MPUGMP}/poly.c ${MPUGMP}/znlog.c
endif

# TODO: decide individually whether to remove optionality on these
DEFINES += -DLARGE_MIN -DTRACK_STATS -DCHECK_OVERFLOW

pcoul dpcoul: DEFINES += -DTYPE_o
pcaul dpcaul: DEFINES += -DTYPE_a
pcrul dpcrul: DEFINES += -DTYPE_r

# Nonstandard binary, checks square cases only. Was used to rerun partial
# searches after finding bugs in the squares-handling code.
ifdef SQONLY
    DEFINES += -DSQONLY
endif
# Bail out early if CRT shows v_0 == r_q (mod a_q), with r_q > z_max.
ifdef CHECK_OVERFLOW
    DEFINES += -DCHECK_OVERFLOW
endif
# Makes instrumentation available, selected at runtime with -dv<bits>
# (see trace.h), and the benches (see bench.c).
ifdef VERBOSE
    DEFINES += -DVERBOSE
endif
ifdef STUB_SQUARE_BRANCH
    DEFINES += -DSTUB_SQUARE_BRANCH
endif
# experimental: children of a loop walk once one has (see coul.c)
ifdef WALK_FROM
    DEFINES += -DWALK_FROM
endif
ifdef WALK_FROM_CHECK
    DEFINES += -DWALK_FROM -DWALK_FROM_CHECK
endif
# Calibration-only stub of walk_v() (MOCK_WALK_TABLE env var), see mock.c
ifdef MOCK_WALK
    DEFINES += -DMOCK_WALK
endif
# with MOCK_WALK, also stub innermost recurse loops, see mock.c
ifdef MOCK_LEAF
    DEFINES += -DMOCK_LEAF
endif
# Optional optimization when lower bound for search is a significant
# proportion of the upper bound.
ifdef LARGE_MIN
    DEFINES += -DLARGE_MIN
endif
# Spend even longer trying to factorize large numbers (> 10^100) with ECM.
ifdef TRY_HARDER
    DEFINES += -DTRY_HARDER
endif
# Track how often we confirm at least m of the k values we're searching for.
ifdef TRACK_STATS
    DEFINES += -DTRACK_STATS
endif
# Write every v_0 being tested in walk_v() to the log file.
ifdef DEBUG_ALL
    DEFINES += -DDEBUG_ALL
endif
# Compile for native architecture unless portable build requested.
ifndef PORTABLE
    CC_OPT += -march=native
endif

default: pcoul
all: pcoul dpcoul pcaul dpcaul pcrul dpcrul

%: GIT_DEFINES_$* = $(shell ./git-data ${MPUGMP} $^)

pcoul dpcoul pcaul dpcaul pcrul dpcrul: Makefile coul.c ${COUL} ${HOUL} ${CFACTOR} ${HFACTOR}
	gcc -o $@ -g ${CC_OPT} ${DEFINES} ${GIT_DEFINES_$*} coul.c ${COUL} ${CFACTOR} -I${MPUGMP} -lgmp -lm -lrt

# the built-in cost table (see mock.c), from the file cost-table, which
# may have been checked out with CRLF line endings
costtab.c: cost-table
	perl -ne 'BEGIN { print "/* generated from cost-table: do not edit */\nconst char cm_default_table[] =\n" } s/\r?\n\z//; s/(["\\\\])/\\$$1/g; print qq{    "$$_\\n"\n}; END { print "    \"\";\n" }' cost-table > $@

test_pell: Makefile test_pell.c pell.c coultau.c rootmod.c coulfact.c prime_iterator.c ${HOUL} ${CFACTOR} ${HFACTOR} t/t05pell
	gcc -o test_pell -g ${CC_OPT} ${DEFINES} ${GIT_DEFINES_$*} test_pell.c pell.c coultau.c rootmod.c coulfact.c prime_iterator.c ${CFACTOR} -I${MPUGMP} -lgmp -lm
	t/t05pell

test_prime: Makefile test_prime.c coulfact.c prime_iterator.c ${HOUL} ${CFACTOR} ${HFACTOR}
	gcc -o test_prime -g ${CC_OPT} ${DEFINES} ${GIT_DEFINES_$*} test_prime.c coulfact.c prime_iterator.c ${CFACTOR} -I${MPUGMP} -lgmp -lm

rungbench: Makefile rungbench.c coultau.c prime_iterator.c ${HOUL} ${CFACTOR} ${HFACTOR}
	gcc -o rungbench -g ${CC_OPT} ${DEFINES} ${GIT_DEFINES_$*} rungbench.c coultau.c prime_iterator.c ${CFACTOR} -I${MPUGMP} -lgmp -lm

speed: Makefile speed.c prime_iterator.c ${HFACTOR} ${MPUGMP}/gmp_main.c
	gcc -o speed -g ${CC_OPT} ${DEFINES} ${GIT_DEFINES_$*} speed.c prime_iterator.c ${CFACTOR} -I${MPUGMP} -lgmp -lm

sq12 dsq12: Makefile sq12.c diag.c coultau.c prime_iterator.c diag.h coultau.h prime_iterator.h ${CFACTOR} ${HFACTOR}
	gcc -o $@ -g ${CC_OPT} ${DEFINES} ${GIT_DEFINES_$*} sq12.c diag.c coultau.c prime_iterator.c ${CFACTOR} -I${MPUGMP} -lgmp -lm -lrt

# coul.h may need a type
test_pell: DEFINES += -DTYPE_o
test: pcoul pcaul pcrul
	t/t10init
	t/t20log

dtest: dpcoul dpcaul dpcrul
	DEBUG=1 t/t10init
	DEBUG=1 t/t20log
