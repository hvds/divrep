# Calibration & recursion-cost estimator - status, 2026-08

Handoff document. Companion to pcoul-batch-harness-design.md and the
original pcoul-calibration-design.md. Written to let work resume
without re-deriving what's already been established.

## What exists

- `lib/Calibrate.pm`, `lib/Calibrate/Search.pm`: the original
  empirical calibration tool (racing/successive-halving gain search,
  priority_batches shape-based prioritization, persistent cache,
  parallel worker pool). Search-phase cost blowup fixed (plateau/noise
  early-stop in the mediant refinement loop). est.total(s) column now
  extrapolates to the full batch set via a log(LCM)-vs-elapsed fit
  (`Calibrate::Search::estimate_full_total`) instead of reporting only
  the searched subset's raw sum. Gain display order fixed to match
  pcoul's actual -g<a>:<b> flag convention.
- `lib/Calibrate/Mintau.pm`: pure-Perl port of hvds' mintau prototype
  (branch with-mintau, script "mintau"), plus `divisors_ordered()`
  (coul.c's divisors[].div[] ordering: ascending, then stable sort by
  descending highest-prime-factor). Both validated:
  - mintau against the prototype's own worked examples (t=1..12,
    no exclusions) - all match.
  - mintau against real pcoul (-DCOUL_GATE_DEBUG instrumentation,
    added to a local build, not upstreamed) MINTAU trace output on
    D(12,7) - exact match once the exclusion-set rule below was
    corrected.
  - divisors_ordered against hvds' worked example (divisors_ordered(30)
    = [5,10,15,30,3,6,2,1]).
- `lib/Calibrate/Recursion.pm`: the new analytic/semi-analytic
  per-batch cost estimator. Two entry points:
  - `top_level_gate(%opt)`: the EXACT walk-vs-recurse decision at a
    batch's first (best_v-selected) decision point. No pcoul run
    needed. Validated to exact-match real GATE-instrumented traces on
    multiple D(12,7) batches (aq, r_walk, p_start, limp, cap, decision
    all match).
  - `estimate_batch_cost(%opt)`: Mertens-style estimate of the WHOLE
    recursion tree's cost, using top_level_gate's exact machinery at
    every node plus a density/power-law approximation for the
    branching sum over primes. See "known approximations" below.

## Validated findings (safe to build on)

- **aq formula**: `aq = PRODUCT over every distinct prime p appearing
  ANYWHERE in the batch's pattern of p^(maxexp(p) [+1 if p==2])`,
  where maxexp(p) is that prime's highest exponent anywhere in the
  pattern (apply_primary() fires once per prime, at its
  highest-exponent occurrence; apply_secondary() handles every other
  occurrence and does NOT touch aq). No unconditional bootstrap term
  (confirmed against D(12,2) -f0: aq=1, not 2, for a fully-unforced
  batch).
- **vi selection**: best_v(j) - NOT "the first '.' in the pattern"
  (an early wrong assumption of mine). -j0 picks the position with the
  HIGHEST remaining t_i (-j2: LOWEST), tied by highest q_i, tied by
  lowest position index, restricted to positions whose remaining t_i
  has an odd prime factor (pure powers of 2, or t_i==1, are
  ineligible - only -j4 allocates powers of 2, not modelled). Needs
  every position's evolving state, not just originally-'.' ones - a
  forced position whose own token doesn't reach full tau=n is still
  in play, just passed over while a bigger-t_i position exists.
  best_v4 not examined (depends on zmax, per hvds - not shape-only,
  so it doesn't fit this analytic approach the way j0/j2 do).
- **mintau() exclusion set**: exactly the primes that get a REAL (x>1)
  allocation somewhere in the batch (i.e. the same set aq's maxexp{}
  identifies) - NOT "the first f primes". An earlier version of this
  code used the "first f" rule after it matched a real pcoul trace,
  but only because of a since-fixed bug: apply_null() was marking a
  force-candidate prime as excluded even when a specific batch's
  combination assigned it nothing (a "null" application). hvds found
  and fixed this upstream (apply_pfreev only excludes when x>1 now) -
  re-validated against the fixed binary. Below the top level, the
  exact identity-based rule is path-dependent; approximated as a
  COUNT (exclude the smallest n_pattern_primes+depth primes) per
  hvds' guidance - not independently re-validated post-fix at depth>0.
- **maxforce[vi] / starting-prime seed**: both branches of
  prep_maxforce() implemented - n%4==0 (position-dependent
  k-vi-1-clamped-by-vi-then-f formula) and n%4!=0 (uniform
  maxforce[i]=k for all i, needed for D(18,*) - 18%4=2). Unaffected by
  the apply_null/pfreev bug (p_start was unchanged across old/new
  binaries in every re-checked trace).
- **have_square (mid-recursion trigger)**: an ODD remaining tau (>1)
  at the selected position means that position's completion must be a
  perfect square (tau(v) odd iff v is a perfect square) - pcoul
  switches to a different r_walk formula here (g'th-root walk size
  times res_array()->count) that is NOT implemented. Detected and
  short-circuited to a crude terminal (raw r_walk, no g'th-root
  adjustment) rather than silently run through the wrong formula.
- **[sq=N]-tagged batches (have_square from the start)**: a distinct
  case from the above - the forced pattern already contains a complete
  square position (remaining tau exactly 1, so the mid-recursion
  ODD-tau check never fires for it). Detected via the `[sq=N]` tag on
  the -a pattern string; same crude terminal-WALK fallback applied for
  the whole tree (have_square only ever increases through a
  recursion, never resets, so one detection at the top is sufficient).

## Known approximations / open accuracy questions

- **WALK_RATE**: a placeholder constant (1e7 candidates/sec),
  never properly calibrated against real elapsed times. Everything
  validated so far compares against `walkc` (items actually walked),
  not wall-clock seconds. This is the most mechanical remaining task
  if this work resumes - straightforward given the D(12,9) dataset
  already gathered (see below), just not yet done.
- **Tail handling in the power-law extrapolation**: at a RECURSE node,
  rather than testing only the smallest primes (an earlier version -
  see git history - extrapolated a fit from 3 clustered near-bottom
  points across the WHOLE range, which badly under-counted the tail
  and compounded multiplicatively with recursion depth), the current
  code tests 4 primes LOG-SPACED across the whole [p_start, cap]
  range, so the fit is directly informed by the tail's actual
  (flattening) shape. This is a real, validated improvement (spread
  across 33 real non-square D(12,9) batches went from >100000x down
  to 7.8x, ~2x after median calibration) but is still an
  approximation, not exact. An attempted "exact tail via one-level
  lookahead" refinement (find where the immediate child is forced to
  WALK, integrate that region exactly) was tried and reverted - it
  only catches cases where the very next level walks immediately, not
  cases where a branch keeps recursing 2-3 more levels before
  resolving cheaply, which is exactly the deep-recursion case that
  matters most. A real fix along those lines would need multi-level
  lookahead, not one - not attempted.
- **Gamma clamping**: the fitted power-law exponent is clamped to
  [-e, -e/2] (e = x-1) per hvds' hypothesis, checked directly against
  real D(12,9) decision points (|gamma| = 1.40 and 1.83 for e=2,
  both inside the predicted range) before being relied on. Guards
  against unstable few-point fits (confirmed necessary on real data:
  an unconstrained fit produced gamma=+5.05 on one node, extrapolating
  to an astronomical, physically-impossible result).
- **have_square accuracy is validated ONLY for the negligible-cost
  case.** Measured directly: on a real D(12,9) sample, square-affected
  batches are ~0.06% of total walkc and ~0.29% of total elapsed time,
  so the crude fallback's remaining error there (bounded to
  hundreds-to-thousands x, no longer catastrophic) doesn't matter
  much. **This does NOT generalize.** Spot-checked against real
  D(18,4) (n=18, k=4 - every single batch is [sq=1] there), the same
  fallback is wrong by roughly 49000x on one batch (predicted
  ~1,085,069 "items" vs real walkc=22, with real recurse-count in the
  hundreds - genuine, non-trivial recursion happening, not a single
  top-level walk at all). **Do not trust the current have_square
  handling for any case where squares are a significant fraction of
  total cost** - this needs the real g'th-root/res_array()->count
  formula, deferred to the pcoul code-review work (see synopsis doc).
- **Not modelled at all**: x a power of 2 (different limit_p branch,
  uses divisors[].highdiv); x==nextt with x itself prime (a third
  limit_p branch); external modular constraints (-m,
  restricted_count>0 branch); -W/p_mid (only learned of its existence
  2026-08 - changes which primes get tried at a position entirely,
  not yet examined at all); -j4 (depends on zmax mid-recursion for
  recovery logging, so best_v4 isn't shape-only the way j0/j2 are -
  would need a different approach, not just "read the formula").

## Real datasets gathered (reusable for future validation)

- D(12,7), -f3: batches b1, b6, b37, b43 individually
  GATE-instrumented and hand-verified (see chat for exact trace
  lines) - the primary source for validating top_level_gate.
- D(12,9), -f5, zmax=15724736976000 (just above the known v_0 =
  15724736975643): 43 batches (every 4th id, 0..169) with real
  (elapsed, walkc, pattern) triples in /tmp/d12k9_dataset.tsv (session
  scratch space - not committed; regenerate via the -Ld20-deadline
  loop in chat if needed). This is the dataset behind every "spread"
  and "ratio" number quoted above.
- D(18,4), -f2, zmax=1e10 (known v_0 = 66251139635486389922, real full
  runtime ~3h - the reduced zmax here is deliberately far short of
  that, per hvds' suggestion, just to get a first feel for the
  have_square gap): all 6 batches (every batch is [sq=1]) individually
  timed - real walkc 22 to 1165, real recurse counts up to ~1150. Not
  yet used for anything beyond the one comparison above.

## If this work resumes: suggested order

1. Calibrate WALK_RATE properly against the D(12,9) dataset's real
   elapsed times (not just walkc) - mechanical, not blocked on
   anything else.
2. Once the have_square formula is understood (pcoul code-review
   work, see synopsis doc), replace the crude fallback and re-run the
   D(18,4) comparison - that's the concrete test case to re-check
   against.
3. Reframe the calibration problem per the harness design doc: instead
   of searching a whole-run (j, f, g) grid, use the estimator (once
   have_square is fixed) to classify a batch's expected cost, and pick
   "good enough" settings for that batch specifically - a smaller,
   more tractable problem than what Calibrate::Search was originally
   built to solve.
4. Only after the above: revisit the not-modelled branches (x a power
   of 2, x==nextt prime, -m, -W/p_mid, -j4) if they turn out to matter
   for real target (n, k) cases - not worth pre-emptively modelling
   without a concrete case that needs them, per the same
   proportionality principle applied to have_square.
