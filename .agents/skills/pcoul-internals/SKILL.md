---
name: pcoul-internals
description: Architecture, vocabulary, and design principles for the divrep/pcoul codebase
---
## pcoul / divrep internals

Orientation for anyone (human or AI) working on this codebase for the
first time. This is durable reference material - architecture,
vocabulary, build steps, and hard-won design rules.

### What this program does

The make target 'pcoul' searches for runs of k consecutive integers each
having exactly n divisors (a "D(n,k)" search). The core algorithm recursively
allocates prime powers to each of the k positions (v_0..v_{k-1}) so that each
position's divisor count multiplies out to the target n, subject to all
positions being linked via a shared CRT (aq, rq) state (since they are
consecutive integers, not independent).

Other targets such as 'pcaul' and 'pcrul' search for different but related
runs.

### Build

    git clone <this repo>
    git clone https://github.com/danaj/Math-Prime-Util-GMP mpu-gmp
    cd mpu-gmp && git checkout <pinned commit - see Makefile default>
    apt-get install libgmp-dev   # or platform equivalent
    make MPUGMP=/path/to/mpu-gmp MPUGMP_VER=<commit> pcoul

The MPUGMP dependency is pinned to a specific commit because there was
no official Math::Prime::Util / Math::Prime::Util::GMP release for several
years. There have been releases in 2026, so catching up to those is
a short-term target.  (see "Known sharp edges" below).

For the full test suite (`make test`, runs t/t10init): also build the
-O0 debug binaries (`make dpcoul dpcaul dpcrul`), and ensure
Math::GMP and Math::Prime::Util perl modules are installed (the test
harness is Perl, separate from the C search program). The test
script's shebang (`#!/opt/maths/bin/perl`) is host-specific; invoke
with `perl t/t10init` directly if that path doesn't exist locally.

### File map

- `coul.c` - the main search: CLI parsing, `main()`, the core
  recursion (`recurse()`), the walk-vs-recurse gate
  (`prep_unforced_x()`), the direct-walk implementation (`walk_v()`),
  and several special-case accelerators (`-W`/`walk_midp()` for large
  primes, `run_flip_pqsq()` for a specific tau-factorization pattern).
- `coultau.c` - "does n^e have exactly tau=t divisors?" testing,
  including a batched, early-abort-capable multi-value version
  (`tau_multi_prep`/`tau_multi_run`) used on the hot path, and a
  single-value version (`is_taux`/`factor_one`) used elsewhere. Wraps
  Math-Prime-Util-GMP's factoring primitives (ECM, p-1, QS, etc).
- `rootmod.c` - modular root-finding (`allrootmod`) and the residue-
  tracking arena (`res_array`) used to track valid values for
  positions forced to be exact g'th powers ("squares").
- `pell.c` - general Pell/generalized-Pell equation solver, used when
  two or more positions simultaneously need to be exact powers (the
  "have_square>=2" case in `walk_v()`).
- `coulfact.c` - trivial small-integer factoring/gcd helpers, used
  only for divisor/exponent bookkeeping (values always small).
- `coulvec.c` - modular-constraint bitvector handling for the `-m`/
  `-c*` options.
- `diag.c` - terminal progress-line display, unrelated to the search
  algorithm itself.
- `prime_iterator.c` - adapted from Math::Prime::Util's C sources;
  `prime_iterator_prev()`/`prev_prime_in_segment()` are this project's
  own addition on top of the imported forward-iteration code.

### Key vocabulary / concepts

- **aq / rq**: the shared CRT modulus and residue across ALL k
  positions (they're consecutive integers, not independent, so a
  prime allocated at any position constrains all of them).
- **have_square (g'th-power tracking)**: a position is forced to be an
  exact g'th power when every possible way of completing its target
  divisor count uses exponents that share a common factor g > 1
  (`divisors[t].gcddm`). `have_square==1` (one such position) is
  handled via `rootmod.c`'s residue tracking; `have_square>=2` (two or
  more simultaneously) requires solving a Pell equation (`pell.c`) to
  find candidates satisfying both positions' square constraints and
  their fixed positional offset at once.
- **walk vs recurse**: at each point with remaining primes to
  allocate, the search can either recurse (try allocating another
  prime, branching further) or "walk" (fix everything else and
  directly iterate candidate values). `prep_unforced_x()` estimates
  the cost of walking (`r_walk`) to decide which is cheaper; this
  decision is evaluated extremely frequently (order 10^12 times over
  the program's lifetime), so correctness AND per-call cost of this
  estimate both matter a lot.
- **-W / midp**: above a user-set prime threshold, allocations of a
  single large prime are handled via one flat descending sweep
  (`walk_midp()`) rather than normal recursion, since at most one
  such large prime can fit in the search bound per position anyway -
  recursion there would be pure combinatorial waste.
- **-I / recovery patterns**: a textual format (`parse_305`) for
  pre-specifying or resuming specific prime allocations per position,
  used both for `-I` (start from a specific point) and internal
  recovery/resume logic.
- **-h / roughness**: this can be manually set to specify a tau value
  (more precisely a `divisors[t].sumpm` value) that `coultau.c` should
  recognize as best resolved by trial factorization. In future this is
  expected to be replaced by something automatic and built-in.
- **Batches**: the outer recursion works through "batches" of forced-
  prime allocations (see `t_forcep`/`t_forcebatch`); `-a` and `-b`
  operate at this batch granularity, for sharding or inspecting specific
  parts of a search. Note: some batches are handled immedately and thus
  never listed, such as those that fully fix one value and those that
  `have_square>=2` (Pell). To reach one directly, construct an explicit
  `-I` pattern instead (see example below).

### Design principles (violate these only with a clear reason)

- **No malloc/free in hot paths.** Considerable effort goes into
  sizing and pre-allocating everything up front, and swapping mpz_t
  contents rather than assigning between them, specifically to avoid
  allocator overhead on paths executed astronomically often.
- **A clean, loud failure is correct behaviour, not a bug.** If a
  function's contract can't be met (e.g. a solver hits a hard-coded
  bound it wasn't proven to always satisfy), calling `fail()` with a
  clear message is the right thing to do - it's easily diagnosed and
  worked around (e.g. by raising a constant) if it's ever hit. A BUG,
  by contrast, is something that produces a false claim - e.g. wrongly
  reporting that every value below the best candidate has been
  checked when some were actually missed, or (equally seriously) an
  unbounded retry loop that never terminates and never reports
  failure. Any function whose interface has no way to signal "I
  couldn't do this" must hard-fail via `fail()` rather than silently
  looping or returning a wrong-but-plausible answer. Functions that DO
  need to report "couldn't resolve, caller should decide" have an
  explicit contract for that (see `tau_failure_handler` in
  `coultau.h`, used by the batched `tau_multi_run()` path) - if you
  need that behaviour, extend a function's interface to support it
  explicitly, don't retrofit a silent workaround.

### Known sharp edges (durable, still true as of the last check)

- **Math-Prime-Util-GMP pin is stale.** Catching up to a current
  release would pull in newer helpers for free (e.g. a fast native
  mulmod) and may let `pell.c`/`rootmod.c` be replaced or thinned
  against better-tested upstream equivalents.
- **`small_divmod()` (coul.c) and `simple_invert()` (rootmod.c)** both
  use full GMP bignum inversion (`mpz_invert`) for what is fundamentally
  a native 64-bit modular inverse, on paths called from every
  `walk_v()` setup. A native replacement (extended-Euclidean inverse +
  a `__int128`-based mulmod) would need writing from scratch or
  sourced from an updated MPUGMP.
- **`mpz_fits_uint_p` in `coultau.c`'s roughness-bound calculation is
  intentional** (guarding a value about to be squared into a `ulong`),
  but is a latent portability bug on any platform where
  `sizeof(uint) == sizeof(ulong)` - it should check that the value fits
  in HALF the bit-width of `ulong` (i.e. that its square won't
  overflow), not merely that it fits in `uint`. The accompanying
  `/* else what? */` is a genuine unimplemented TODO, not just a
  comment - currently `tlim` silently keeps its earlier default in
  that case, which has not been reasoned through.
- **Reproducing a `have_square>=2` (Pell) case for testing/
  instrumentation**: since these never appear in `-a` batch listings,
  use an explicit `-I` pattern with two positions forced to leave an
  ODD remaining divisor count each (so both need a square-completing
  factor), e.g. for a D(12,3) search:
  `./pcoul -I"7^3 2^3 ." -x1e100 12 3` (positions 0 and 1 each forced
  to leave remaining tau=3). Note `-I` patterns must satisfy the
  arithmetic-progression's implied parity/residue constraints between
  positions - the program will reject inconsistent patterns with a
  clear error (e.g. "Missing 2^1 at N in stack") rather than silently
  accepting them; this is correct, desired behaviour (see design
  principles above), not a bug to work around.
