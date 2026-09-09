# walk_v() cost-model session deliverables

Unpack from the `divrep` repo root (`tar xzf walk-cost-model-deliverables.tar.gz`
from inside your repo checkout). This overlays:

    coul.c                          (modified)
    coultau.c                       (modified)
    coultau.h                       (modified)
    lib/Calibrate/WalkCost.pm       (new)
    lib/Calibrate/RootCount.pm      (new)
    recalibrate_walkcost.pl         (new)
    parse_verbose_cost.pl           (new)

`coul.c`/`coultau.c`/`coultau.h` are based on the `calibrate` branch at
`5a3c370`. Diff against your current tree before overwriting, in case
you've moved on since then - these are full files, not a patch, so a
straight overwrite will clobber anything else you've changed in them.
Recommended:

    git diff --no-index coul.c /path/to/repo/coul.c      # etc, before overwriting
    # or just extract into a scratch copy of the repo and `git diff` there

## What changed in coul.c/coultau.c/coultau.h, and why

All changes are `-DVERBOSE`-gated diagnostics (no behaviour change under
a normal, non-VERBOSE build), plus one function (`tau_prime_test`) that
routes the square/`prime_power` branch's primality check through a
named wrapper instead of calling `_GMP_is_prob_prime()` inline:

- `tau_prime_prep()`, `tau_multi_prep()`: added `vi=` to their VERBOSE
  header lines, so per-position attribution doesn't need positional
  inference when parsing a trace.
- `ct_pretest()`/`ct_bpsw()` (new, in `coultau.c`): thin VERBOSE-aware
  wrappers around `primality_pretest()`/`_GMP_BPSW()`, matching the
  existing `ct_*` convention.
- `tau_prime_test()` (new, in `coultau.c`, declared in `coultau.h`):
  makes the square-branch `prime_power` primality check visible to
  `-DVERBOSE` (it previously called `_GMP_is_prob_prime()` directly,
  bypassing every existing `ct_*` wrapper). **This is diagnostic only,
  not a performance change** - `_GMP_is_prob_prime()` already does
  exactly this pretest-then-BPSW logic internally (primality.c
  ~line 1227); an earlier version of this session claimed a ~3x
  speedup from this, which was wrong (VERBOSE-build measurement
  artifact) and has been corrected in the code comment.
- `alloc_square()`: added a VERBOSE print of `(g, qq, count)` at the
  point `allrootmod()` computes the residue count - used to validate
  `Calibrate::RootCount`'s closed-form root-count formula against real
  output (see below).
- `walk_1()`/`walk_1_set()`: added VERBOSE entry markers and
  early-return-reason markers, plus a marker distinguishing their
  `test_1primes()`/`test_1multi()` calls from the main loop's
  `test_primes()`/`test_multi()` calls (all named `walk_1_call`/
  `walk_1 ENTRY`/`walk_1 EARLY-RETURN ...`/`walk_1_set ENTRY`/
  `walk_1_set EXHAUSTED`) - used to confirm walk_1/walk_1_set reuse
  the same cost machinery as the main branch.

## The two new Perl modules

- **`lib/Calibrate/WalkCost.pm`**: parametric factorization-cost model
  for `walk_v()`, replacing `Calibrate::Recursion`'s `WALK_RATE`
  placeholder. Every calibrated number lives in `%DEFAULT_PARAMS`, not
  hardcoded in the cost functions, so it can be refreshed by
  `recalibrate_walkcost.pl` without touching the modelling logic. NOT
  yet wired into `Recursion.pm`'s `_node_cost()` - see the module's own
  header comment for what's needed to do that, and for the full set of
  validated findings, known gaps, and citations to the real data each
  number came from.
- **`lib/Calibrate/RootCount.pm`**: exact (not statistical) closed-form
  count of g'th roots modulo `qq`, for `walk_v()`'s `have_square`
  branch - fills the "not implemented" `r_walk` formula noted in
  `calibration-estimator-status.md`. Validated against real
  `alloc_square()`/`allrootmod()` output across `g=2` and `g=16`, many
  `qq` structures, all exact matches.

## The two new scripts

- **`parse_verbose_cost.pl`**: turns a `pcoul -DVERBOSE` trace into a
  per-candidate, per-stage cost TSV (one row per stage-attempt). Built
  for gathering training data, not just summary stats - see its own
  header comment for the attribution-quality caveats (exact vs
  approx), particularly around escalation-phase interleaving.
- **`recalibrate_walkcost.pl`**: the "interim/parallel goal" from
  `walk-cost-model-intro.md` - re-runs a small curated benchmark suite
  (documented in the script) plus the standalone `qs` binary, and
  regenerates a `WalkCost.pm` params file. Usage:

      ./recalibrate_walkcost.pl --pcoul ./pcoul.verbose \
          [--qs /path/to/standalone/qs] \
          [--out lib/Calibrate/walkcost_params.pl] [--timeout 20]

  `pcoul.verbose` must be built with `VERBOSE=1` first (see
  `.agents/skills/pcoul-internals/SKILL.md`). The standalone `qs`
  binary is optional (only needed to recalibrate `cpu_scale`) and is
  built from the `simpqs-post54` branch of
  `https://github.com/hvds/Math-Prime-Util-GMP` via:

      gcc -o qs -g -O3 -DTIMING -DSTANDALONE_SIMPQS -DSTANDALONE \
          simpqs.c utility.c rootmod.c isaac.c primality.c gmp_main.c \
          factor.c prime_iterator.c tinyqs.c lucas_seq.c real.c bls75.c \
          ecpp.c ecm.c squfof126.c pbrent63.c random_prime.c poly.c \
          misc_ui.c znlog.c -lgmp -lm

  Re-run this whenever the factorization backend changes materially
  (the flagged near-term case being an MPUGMP upgrade) or on new
  hardware. Load the result in code with
  `Calibrate::WalkCost::load_params($path)`.

## Known gaps / honest status, at a glance

See `WalkCost.pm`'s header comment for the full detail, but briefly:
`need_prime`/need_other's "cheap path" is well-calibrated; the
escalation-probability curve is a 2-point placeholder shape, not a
real regression; `cost_bpsw()` was never bit-bucketed; `have_square`'s
count is now exact but its cost isn't wired into `estimate_walk_seconds()`
yet; `walk_1()` is fully confirmed, `walk_1_set()`'s cost is
structurally understood but not empirically confirmed (a real,
if weak, negative search result - see the module header); `walk_midp()`
and `run_flip_pqsq()` (`FLIP_PQSQ`) are untouched, per your own
instruction to leave them for a later stage.
