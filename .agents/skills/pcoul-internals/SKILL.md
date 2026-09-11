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
    git clone https://github.com/hvds/Math-Prime-Util-GMP mpu-gmp
    cd mpu-gmp && git checkout simpqs-full   # commit b363d69b10
    apt-get install libgmp-dev   # or platform equivalent
    make MPUGMP=/path/to/mpu-gmp MPUGMP_VER=2389dcbc44 pcoul

Confirmed working end-to-end with exactly this recipe (built `dpcoul`,
ran a known test case from `t/t10init`, got the expected `f(6,3) =
242`). Two things that aren't obvious from the Makefile alone:
- **`danaj/Math-Prime-Util-GMP`'s current `master` does NOT contain the
  pinned commit** (`2389dcbc44` and friends) - that history only
  exists on **`hvds`'s own fork**, branch `simpqs-full`, whose tip
  (`b363d69b10`) is the Makefile-comment-documented equivalent of
  `2389dcbc44`. Cloning danaj's repo as the skill previously suggested
  will fail to find the commit at all.
- `MPUGMP_VER` must be passed explicitly (matching one of the
  Makefile's recognised strings, e.g. `2389dcbc44`) even when checking
  out the fork's hash directly - the Makefile keys its extra-source-file
  logic (`lucas_seq.c`/`rootmod.c`/`random_prime.c` etc.) off this
  string, not off what's actually checked out, so a mismatch produces
  confusing linker errors (`undefined reference to lucas_seq` etc.)
  even though compilation itself succeeds cleanly.

The MPUGMP dependency is pinned to a specific commit because there was
no official Math::Prime::Util / Math::Prime::Util::GMP release for several
years. There have been releases in 2026, so catching up to those is
a short-term target.  (see "Known sharp edges" below).

For the full test suite (`make test`, runs t/t10init): also build the
-O0 debug binaries (`make dpcoul dpcaul dpcrul`), and ensure
Math::GMP and Math::Prime::Util perl modules are installed (the test
harness is Perl, separate from the C search program).

For the Perl DB/harness layer (`ful`, `inject`, `report`, anything
under `lib/Seq/`), on a fresh Debian/Ubuntu host `apt-get install
libdbix-class-perl libmath-gmp-perl libmath-prime-util-perl
libdbd-mysql-perl mariadb-server` covers everything EXCEPT
`DBIx::Class::BitField` (used by `lib/Seq/Table.pm` for the `status`
bitfield columns), which has no OS package on Ubuntu 24.04 and isn't
reachable from a sandboxed/allowlisted network (it's on CPAN/metacpan,
not GitHub). It's a small, self-contained module (add_columns +
per-flag accessors, plus `DBIx::Class::ResultSet::BitField` for
`search_bitfield`); if you need to exercise this code without full
CPAN access, a minimal local reimplementation covering
`add_columns`/per-flag accessors/`search_bitfield` is enough to deploy
the schema and run `Seq::Run::finalize()` etc for testing.

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
  decision is evaluated extremely frequently (anticipated in the
  order of 10^12 times over the lifetime of the codebase),
  so correctness AND per-call cost of this
  estimate both matter a lot. Forced-prime batch dispatch and
  unforced/walk processing are cleanly separated: `limit_p()` (which
  `prep_unforced_x()` consults for this decision) has exactly one call
  site in the whole file, reached only *after* every forced prime's
  own batch choice has already been made; `test_forcep()`/the forced-
  batch construction never calls `limit_p()`/`mintau()` at all - which
  batches exist for a given prime, and which one gets chosen, is
  decided purely by static divisor/CRT structure. The "walk" family
  itself (`walk_v()`, `walk_1()`, `walk_1_set()`) all begin with an
  identical `#ifdef SQONLY` guard plus a `have_min` early-return (seed
  `level_setp()` to the min bound and return if `!have_min`) - despite
  being defined hundreds of lines apart, so any similar extension point
  needs adding to all three, not just `walk_v()`.
- **`mintau()`'s memoization is keyed purely by content, not tree
  position.** Its cache (`mint_base`, a lazily-grown `t_mint` trie
  indexed by `off` - the *gap* between consecutive available-prime
  indices) is populated relative to whichever `pfreev` bit-vector is
  active at call time; `mint_init_state()` resets its own scan state
  (`pfreenext`/`pfreedepth`) fresh on every call. It has no notion of
  "the real search tree" at all - it's safe to call with a
  temporarily/artificially modified `pfreev` (eg with a few extra bits
  cleared) and get back a fully valid, cacheable/cache-reusable answer
  for that modified view, not just for whatever the "live" state
  happens to be.
- **`is_forced` distinguishes forced-batch from unforced levels.**
  `cur_level->is_forced` is `1` only for a level populated via
  `apply_batch()` (a forced-prime batch, tail or not - it's set
  unconditionally near the top of that function) and `0` for one from
  `apply_single()` (a genuine unforced candidate) or a freshly-reset
  level. Useful for telling "still dispatching forced primes" from
  "already in unforced territory" when inspecting state.
- **`apply_level()` is the one shared level-transition function** that
  `apply_null()`, `apply_single()`, and `apply_primary()` all route
  through. `apply_secondary()` is the exception: it adds *further*
  constraints (for non-primary positions in the same forced batch) to
  a `cur_level` a preceding `apply_primary()` call already established
  in the same `apply_batch()` invocation, rather than creating a new
  level transition itself.
- **`prime_iterator_setprime(iter, n)`/`prime_iterator_next(iter)`**:
  seeding with `n` does NOT test `n` itself - `next()` always returns
  the first prime *strictly greater* than whatever was last seeded or
  returned. This drives the main per-prime enumeration (`continue_
  unforced:` label in the main loop): `level_setp()` seeds the
  iterator once per `(vi,x)` decision, then `prime_iterator_next()` is
  called repeatedly (via `goto`/`continue`, not a literal `for` loop)
  until the returned prime exceeds `cur_level->limp`.
- **-W / midp**: above a user-set prime threshold, allocations of a
  single large prime are handled via one flat descending sweep
  (`walk_midp()`) rather than normal recursion, since at most one
  such large prime can fit in the search bound per position anyway -
  recursion there would be pure combinatorial waste. `walk_midp()` is
  only ever invoked from `process_batch()`, which itself only runs once
  `fp_need` reaches 0 (see "forced levels have no gaps" below) - so any
  code path that can prove it reached `walk_midp()` can assume the
  forced-batch chain is already complete, with no partial-batch case to
  allow for.
- **Forced levels have no gaps: `level` runs 1..`forcedp` for the
  forced-prime chain, always, with no prime skipped.** `prep_forcep()`
  builds `forcep[0..forcedp)` in strictly increasing fpi order, one
  entry per forced prime, and *truncates* `forcedp` itself (`forcedp =
  fpi; break;`) rather than ever letting an entry have `count == 0`
  with more forced primes to follow - a higher prime that would have no
  real batches becomes genuinely unforced instead. So the forced chain
  always occupies exactly levels `1..forcedp` one level per prime; code
  that reaches a "forced batch just completed" point can rely on
  `level - 1 == forcedp` without checking it.
- **-I / recovery patterns**: a textual format (`parse_305`) for
  pre-specifying or resuming specific prime allocations per position,
  used both for `-I` (start from a specific point) and internal
  recovery/resume logic. Recovery replays a forced batch by calling
  `apply_batch()` directly from `insert_stack()`/`insert_forced()`,
  *not* through the normal `recurse()` loop - so it deliberately skips
  the loop's own call to `process_batch()`, and `recurse()`'s `e_is`
  jump value (`IS_DEEPER` vs `IS_MIDP`) is what tells it whether that
  call still needs to happen (`IS_DEEPER`: fresh, call `process_batch()`
  for the first time) or has already partly happened and only needs
  resuming (`IS_MIDP`: a `walk_midp()` sweep was mid-way through when
  checkpointed - `process_batch(cur_level, is_recover=1)` resumes it rather
  than re-running the batch's own bookkeeping, which was already logged
  before the interruption). Conflating these two - e.g. letting
  ordinary "just completed a batch" handling fire again after an
  `IS_MIDP` resume - double-runs `walk_midp()` and double-increments
  `batch_alloc`, desyncing `-a`/`-b` batch numbering for the rest of the
  run without necessarily crashing or producing an obviously wrong
  result, so it's easy to miss in testing (see `t/t10init`'s "recover
  midp does not retrigger process_batch" for the regression test, added
  after exactly this bug shipped).
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

### CLI flags (n/k are positional, and come AFTER all `-` options)

Traced directly from `main()`'s arg-parsing loop, since several are
easy to confuse by mnemonic alone:

- `-x<max>` / `-x<min>:<max>` (`set_minmax()`): the search bound - bare
  `-x<v>` means "search 0..v". This is the one to set to a specific
  claimed value when re-confirming a result.
- `-f<n>` (`force_all`): forces every prime `<= n` to be tracked as its
  own explorable batch (see "the tail" below) rather than allowing a
  synthetic catch-all tail batch for singleton cases.
- `-p<min>:<max>` (`set_cap()`, sets `sminp`/`smaxp`): restricts the
  *range of primes* considered - a genuinely partial search, not a
  full one, regardless of what range it's given.
- `-m<mod>=<val>` / `-m<mod>!<val>` (`set_modfix()`): restricts to
  (or excludes) a residue class - also a partial search.
- `-P<n>` (`limp_cap`, capital - unrelated to `-p` despite the similar
  letter): caps the internal `limit_p()` estimate, a performance knob.
- `-o` (`opt_print`): print candidates instead of fully testing them -
  also unrelated to `-p` despite the mnemonic overlap.
- `-a`/`-b`: batch selection (see "Batches" above).
- `-I`: recovery/injection pattern (see "recovery patterns" above).

`report_init()` echoes whichever of these were actually in effect back
onto the log's `001` line (e.g. `-p<min>:<max>`, each `-m` entry, `-f`
if nonzero) - that line is the ground-truth record of what a given run
actually used, more reliable than reconstructing it from other sources.

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

### Forced primes, batches, and the "tail" (forcep/forcebatch)

- **`t_forcep`/`t_forcebatch`** (built by the function around coul.c:1900,
  historically unnamed in comments - search for `forcep = malloc`): for
  each prime `p <= k`, the set of ways `p` could be allocated across
  positions is precomputed into a list of "batches" (`fp->batch[0..count)`).
  `-a`/`-b` index into this list (see "Batches" above).
- Each batch has a `primary` position and a `x[]` array of per-position
  exponents-plus-one. `test_forcep()` classifies each candidate
  (vi, fx) as `TFP_BAD` (impossible), `TFP_SINGLE` (only one valid
  allocation exists for this prime at this position - so it doesn't need
  its own explorable batch), or `TFP_GOOD` (kept as a real batch).
- **The tail**: when at least one `TFP_SINGLE` case is *not* being kept
  as its own batch (`keep_single` false) and at least one other batch
  for this prime already exists, a synthetic final batch is appended via
  `fpb_init(fbp, 1, 0)` - i.e. `primary=1`, all `x[]` zero. `is_tail()`
  tests exactly this (`bp->x[bp->primary] == 0`). Applying this batch
  (`apply_batch()` -> `apply_null()`) represents "this prime's
  allocation from here on is not itself forced/tracked as a batch";
  it does NOT mean the prime is unavailable.
- **`keep_single`** is true (suppressing the tail for that prime) when
  `p <= force_all` (the `-f` CLI option), or - specifically for
  `TYPE_o` - whenever `n & 3` is nonzero (i.e. `n` is *not* divisible
  by 4). So for `TYPE_o`, a tail can exist at all only when **n is
  divisible by 4**, and is suppressed entirely by passing `-f` with a
  value `>= k`.

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
