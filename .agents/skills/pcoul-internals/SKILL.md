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
    cd mpu-gmp && git checkout v0.54   # commit 39982f872b
    apt-get install libgmp-dev   # or platform equivalent
    make MPUGMP=/path/to/mpu-gmp pcoul

Confirmed working with exactly this recipe: `make MPUGMP=... dtest`
then passes. Two things that aren't obvious from the Makefile alone:
- The MPUGMP dependency is pinned to a specific commit, named by the
  Makefile's default `MPUGMP_VER`: at present the v0.54 release. For
  any other checkout `MPUGMP_VER` must be passed explicitly, matching
  one of the strings the Makefile lists - it keys its extra-source-file
  logic (`lucas_seq.c`/`rootmod.c`/`random_prime.c` etc.) off this
  string, not off what's actually checked out, so a mismatch produces
  confusing linker errors (`undefined reference to lucas_seq` etc.)
  even though compilation itself succeeds cleanly.
- To rebuild an older commit of this repo, check out the MPUGMP commit
  that its own Makefile names as the default. Those are all in danaj's
  repository, except `b363d69b10`, which is on hvds's fork (branch
  `simpqs-full`) and is equivalent to `2389dcbc44`.

For the test suite: `make test` uses the optimised binaries and
`make dtest` the -O0 debug ones (`dpcoul dpcaul dpcrul`). Both run
every file in `t/`, and need only core Perl modules. The soak tests
there skip themselves unless asked for (`TEST_PELL=1`, `TEST_TAU=1`).

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
  recursion (`recurse()`), the walk-vs-recurse gate (`gate_walk()`,
  asked from `prep_unforced_x()`), the direct-walk implementation
  (`walk_v()`),
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
  directly iterate candidate values). `prep_unforced_x()` sets up a
  fresh power x at a position: it finds the limit for p (`limit_p()`)
  and asks `gate_walk()` whether a walk (whose cost it estimates as
  `r_walk`) would be cheaper than recursing over those primes; this
  decision is evaluated extremely frequently (anticipated in the
  order of 10^12 times over the lifetime of the codebase),
  so correctness AND per-call cost of this
  estimate both matter a lot. **The decision is made once, at a fresh
  x, and the search stays committed to it** until unwinding removes
  the level: when a new candidate lowers the maximum, `recurse()` only
  recalculates the limit of each level it returns to, and recovery
  rebuilds a logged level without asking the gate. Both rely on what
  `limit_p()` guarantees: a lower maximum never gives a greater limit
  (0 stands for 2^64 or more). Forced-prime batch dispatch and
  unforced/walk processing are cleanly separated: `limit_p()` is
  reached only *after* every forced prime's
  own batch choice has already been made; `test_forcep()`/the forced-
  batch construction never calls `limit_p()`/`mintau()` at all - which
  batches exist for a given prime, and which one gets chosen, is
  decided purely by static divisor/CRT structure. The "walk" family
  itself (`walk_v()`, `walk_1()`, `walk_1_set()`) all begin with an
  identical `#ifdef SQONLY` guard plus a `have_min` early-return (seed
  `level_setp()` to the min bound and return if `!have_min`) - despite
  being defined hundreds of lines apart, so any similar extension point
  needs adding to all three, not just `walk_v()`.
- **Order of powers at one position**: the powers p^{x-1} that make up
  a position's tau are tried in a fixed order, so that each set of
  them is searched once. The next x is always a multiple of the
  highest prime dividing the tau still to place (`divisors[t].high`;
  the choices are `div[0..highdiv)`). Among x with the same highest
  prime they go in ascending order (`done_in_reverse()` skips the
  rest), and equal x go in increasing order of p (`start_p()`).
  **Powers of 2 are the exception**: recursion allocates them only
  under *highpow* (`-j4`, or a fixed order `-js`), and then in
  increasing order of p whatever the power. Anything that relies on
  the ascending order must leave powers of 2 out, as `can_flip()` does.
- **The flip (`run_flip_pqsq()`)**: once p^{z-1} has left tau 2z at a
  position, and no q > p fits as q^{z-1}, the order above leaves only
  [z, 2z] for this p and for every larger one. That is searched the
  other way round, as q^{2z-1} then r^{z-1} with r >= p, which is
  cheaper. z need not be prime, but not a power of 2. The flip ends
  only the x = z branch of its level: later x there go on as usual.
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
  invoked from `process_batch()`, which itself is run when a complete
  batch has been allocated (ie when `fp_need` reaches 0).
- **Forced levels have no gaps**: the forced-prime chain always occupies
  exactly `forcedp` consecutive levels, one per prime, starting
  at `final_level` (which is 1 `prep_presquare()` inserts an initial
  dummy level, else 0). `prep_forcep()` builds `forcep[0..forcedp)`
  in strictly increasing fpi order, one entry per forced prime, and
  *truncates* `forcedp` itself (`forcedp = fpi; break;`) rather than
  ever letting an entry have `count == 0` with more forced primes
  to follow - a higher prime that would have no real batches becomes
  genuinely unforced instead. `forcedp` can end up 0 (k = 1, or k = 2
  with 4 | n and no `-f`): the whole search is then one batch, `b0`,
  and it still goes through `process_batch()`, since `-W`, `-a` and
  the batch count all depend on that call. `prep_presquare()` (run
  once, before any of this) inserts that extra level - shifting where
  the chain starts by one - whenever some position needs an odd number
  of divisors (`target_t(vi) & 1`); for `TYPE_o` that's the same for
  every position (`target_t(vi)` is just `n`), so it only depends on
  whether `n` itself is odd, but `TYPE_r`'s per-position `target_tau[]`
  can make it position-specific. Either way, code that reaches a
  "forced batch just completed" point can rely on the chain having
  taken exactly `forcedp` levels, but should not assume `level - 1 ==
  forcedp` in absolute terms.
- **-I / recovery patterns**: a textual format (`parse_305`) for
  pre-specifying or resuming specific prime allocations per position,
  used both for `-I` (start from a specific point) and for recovery
  from a log (`-r`). Recovery replays a forced batch by calling
  `apply_batch()` directly from `insert_stack()`/`insert_forced()`,
  *not* through the normal `recurse()` loop - so it deliberately skips
  the loop's own call to `process_batch()`, and the `e_is` value that
  `insert_stack()` returns tells `recurse()` where to pick up:
  `IS_BATCH` when that call still has to be made (fresh, or to resume
  a partial `walk_midp()`); `IS_RWALK`, `IS_6X` or `IS_FLIP` to resume
  a walk, a 6X search or a flip; `IS_NEXT` or `IS_NEXTX` to move on
  from the last allocation shown.
- **Recovery and candidates**: the levels are rebuilt under the
  maximum that held when the last progress line was written, because
  under highpow the position chosen at a level can depend on the
  maximum (a 315 line marks only the levels that `best_v()` would not
  have reproduced at the time). So a candidate logged before that line
  is applied first, and one logged after it - such as one copied in
  from another shard - only once the stack is rebuilt; `prune_stale()`
  then unwinds the levels it has ruled out. A run that stays committed
  can also log an allocation which a candidate found beneath it has
  since ruled out, and recovery resumes after that allocation
  (`least_is_best()`, `limit_was_best()`). Recovery aims to honour
  every line a run could have written; one it could not have written
  may be refused with `fail()`. Do not lower `-x` by hand for a
  recovery: under `-j4` or `-js` the levels can then be rebuilt in a
  different order, and part of the search skipped without complaint.
  To force the maximum down, append a `202 Candidate <v>` line to the
  log instead.
- **-h / roughness**: this can be manually set to specify a tau value
  (more precisely a `divisors[t].sumpm` value) that `coultau.c` should
  recognize as best resolved by trial factorization. In future this is
  expected to be replaced by something automatic and built-in.
- **Batches**: the outer recursion works through "batches" of forced-
  prime allocations (see `t_forcep`/`t_forcebatch`); `-a` and `-b`
  operate at this batch granularity, for sharding or inspecting specific
  parts of a search. Note: some batches are handled immediately, and
  are then neither counted nor listed: those that fully fix one value,
  and those with `have_square>=2` (Pell). `-jp` (`defer_pell`) makes
  the Pell ones wait for the full batch, so that `-a` lists them
  (marked `[sq=2]` or more) and `-b` can run one; the batch ids are
  then not those of a run without `-jp`. `-a4` lists the ones that fix
  a value as well. A Pell case that needs an unforced allocation is
  not a batch at all: to reach one, construct an explicit `-I` pattern
  (see example below). A run that ends with no
  candidate reports `406` (no valid arrangement of powers) only if no
  batch was ever valid, in this process or in the log it recovered
  from (`seen_valid`); otherwise, under `-dl`, it reports
  `500 f(n, k) > max`. The harness records a 406 as the case being
  impossible, so the two must not be confused.

### CLI flags (n/k are positional, and come AFTER all `-` options)

Traced directly from `main()`'s arg-parsing loop, since several are
easy to confuse by mnemonic alone:

- `-x<max>` / `-x<min>:<max>` (`set_minmax()`): the search bound - bare
  `-x<v>` means "search 0..v". This is the one to set to a specific
  claimed value when re-confirming a result. The range is min < v_0 <=
  max; min >= max is refused, which includes giving no `-x` at all.
  Every walk starts at the first value above min, and `candidate()`
  checks again.
- `-X` (clears `improve_max`): do not lower the maximum when a
  candidate is found, so that every solution in the range is reported.
  The same value can then be reported more than once: that is
  accepted, since avoiding it would cost more time than it saves.
- `-j<n>` / `-js<v,v,...>` (`strategy`): how `best_v()` picks the
  position to allocate at next; `-js` gives a fixed order. `-j4` and
  `-js` set `highpow` (see "Order of powers" above). `-jp`
  (`defer_pell`) is a separate switch, not a strategy (see "Batches"
  above).
- `-g<n>` (`gain`): tunes the walk-vs-recurse gate; a higher gain
  means more recursion before walking. `-G<n>` sets it separately for
  walks with a fixed square.
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
- `-dw<n>` / `-dW<n>` / `-dL<n>` (debug): show every progress line
  (`-dw` leaves out the steps of a walk, `-dW` includes them), or
  write every one to the log (`-dL`), and stop after n of them if n
  is given. The tests are built on these.

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

- **`t_forcep`/`t_forcebatch`** (built by `prep_forcep()`): for
  each prime `p <= k`, the set of ways `p` could be allocated across
  positions is precomputed into a list of "batches" (`fp->batch[0..count)`).
  `-a`/`-b` index into this list (see "Batches" above). pcaul also
  forces every prime dividing n: each divides every v_i or none, the
  batches settle which, and it is never tried as an unforced prime.
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

- **Math-Prime-Util-GMP is pinned to its v0.54 release.** Its newer
  helpers (e.g. a fast native mulmod) may let code here be replaced,
  and `pell.c`/`rootmod.c` thinned against better-tested upstream
  equivalents.
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
  instrumentation**: where forced primes alone give the two squares,
  `-jp -a` lists the batch and `-jp -b<id>` runs it, e.g.
  `./pcoul -jp -b0 -x1e6 30 4`. Where it takes an unforced allocation,
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
