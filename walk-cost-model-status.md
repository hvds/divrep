# walk_v() escalation-cost model - status, 2026-09-24 (updated late 2026-09-24)

Handoff document. Companion to `calibration-estimator-status.md`
(the separate, still-open recursion/gate-decision estimator -
`Calibrate::Recursion`, `top_level_gate`, `aq`/`mintau` - not touched
by this topic) and `pcoul-batch-harness-design.md` (forward-looking
harness design, not yet built). Written to let work resume without
re-deriving what's already been established.

## What this topic is

`walk_v()`'s escalation ladder (`tau_multi_run()` -> a sequence of
ECM/P-1/QS/fixed-method attempts, `tmf_2..tmf_42` in `coultau.c`) is
the genuinely nondeterministic, factorization-library-dependent half
of pcoul's cost (the recursion/allocation structure that
`Calibrate::Recursion` models is the deterministic half). Original
motivation: build a cost model accurate enough to substitute for real
escalation work during calibration, and to survive a
Math::Prime::Util::GMP library upgrade without needing to be
re-derived from scratch each time.

Two git-am patch series carry the code:
`calibrate-clean-history.patches.tar.gz` (10 patches, the original
session: `Calibrate::Recursion` harness scaffolding through
`Dickman.pm`/`Ladder.pm`) and `calibrate-clean-history-part2.patches.tar.gz`
(5 patches, this session: `63ed7ae..ffe6664`, `coulmock.c`'s full
MOCK_LADDER implementation and everything that fed it). Both apply
cleanly in sequence on top of `29903ec`; verified via a fresh clone +
build this session.

## What exists and is validated

- **`lib/Calibrate/Dickman.pm`**: Dickman's rho (RK4 on a fixed grid),
  validated against published values to 4+ sig figs. Used for ECM/P-1
  success probability given a known factor size.
- **`lib/Calibrate/Ladder.pm`**: per-rung cost/success model on top of
  Dickman rho. `FAMILY_BOOST` constants fitted from `rungbench`'s `pq`
  mode (constructed semiprimes with a known factor size) and
  validated against a genuinely held-out test gathered AFTER the fit
  was fixed (errors mostly <0.05).
- **`rungbench.c`** (replaces `ftest.c`): multi-trial in-process
  benchmark, two modes:
  - `pq` (default): `n = p*q`, distinct independent primes - good for
    success-rate/cost calibration, but the found factor's multiplicity
    is ALWAYS exactly 1 by construction. Cannot measure repeated-factor
    rates.
  - `rand` (added this session): genuine random integer, filtered for
    roughness and compositeness, tested directly against a named rung
    (bypassing `tau_single_try()`, which overwrites `tm->n` with the
    found factor on success - a saved copy of the original `n` is
    needed to compute real multiplicity). Reports `mult=` and
    `factor_bits=` per trial, plus a `MULT_HIST` summary.
- **Exact multiplicity theory for `nqc==0`** (hvds, this session): `ati`
  sweeps uniformly and `qq[vi]` is coprime to any prime `p` not already
  in the allocation list (anything that WAS allocated is stripped by
  the `inv[]` checks before this point), so multiplication by `qq[vi]`
  is a bijection mod `p^k` for every `k` - `v_i` is EXACTLY uniform mod
  `p^k`, giving `P(mult=j) = (1/p)^(j-1)*(1-1/p)` exactly, not
  heuristically. Spot-validated empirically via `rungbench rand` mode:
  at a found-factor size of 9 bits, observed rate 1/491 vs theoretical
  1/512 - close, though one event is not a real sample size. **Not
  verified for `nqc>0`** (the have_square/Pell branch) - flagged by
  hvds as open, revisit once that branch is looked at properly.
- **`coulmock.c`** (new file, this session): MOCK_LADDER build mode,
  replacing the WHOLE `tau_multi_run()` call with a deterministic
  expected-cost calculation (never a sampled real outcome - an earlier
  version sampled and fell through to the real call, which corrupts
  search results by letting a coin flip decide whether to discover a
  real answer; fixed to always return "rejected", so a mocked run's
  *results* are meaningless but its *timing* is meant to be
  trustworthy). Validated structurally at every development stage:
  exact `recurse`/`walk` match and near-exact `walkc`/breakdown against
  the real build (`STUB_SQUARE_BRANCH`/plain builds), including after
  this session's full rewrite.
  - Buchstab's omega function (own RK4 solve - NOTE the DDE
    `(u*omega(u))'=omega(u-1)` has `omega(u)` itself on the RHS, unlike
    rho's equation, so needs real RK4 stage estimates, not grid lookups
    mid-step; got this wrong on the first attempt, caught by validating
    against the known asymptotic `omega(u)->e^-gamma` before trusting
    it) drives the smallest-factor-size sampling: a residual reaching
    escalation is tlim-rough by construction, not uniform over
    `[8,bits/2]` as the first version assumed. Sampled ONCE per
    candidate (not resampled per rung - the true smallest factor is one
    fixed, if unknown, quantity for the whole candidate).
  - Compatibility split (`compatibility_split()`): given a rung finds a
    prime of size `p`, splits into `P(incompatible - whole-batch abort)`
    and, for each divisor `j>=2` of the current tau target `t`,
    `P(compatible via multiplicity j-1)`, using the exact geometric law
    above. For most rungs (large characteristic `p`), this collapses to
    "is `t` even"; for small-`p` rungs the tail terms matter, and WHICH
    `j` values matter depends on `t`'s own divisor structure (the
    "shape" hvds asked about).
  - Recursive per-candidate cost (`candidate_outcome()`): a
    compatible-but-not-fully-resolved success (`t` reduces to something
    other than 1 or 2) restarts the whole ladder from the cheapest rung
    with the new, smaller shape - exactly matching `tau_multi_run()`'s
    own `goto tmr_retry`. Bracket lookup uses `coultau.c`'s real
    `get_tmfbl()` accessor (exported this session, replacing an
    initial hand-copied table that both risked drifting out of sync
    and, as built, already missed the `flake` masking `init_tmfbl()`
    applies).
  - Cross-candidate joint survival: `tau_multi_run()` processes every
    candidate in a batch rung-major, and the moment ANY of them hits an
    incompatible success, the WHOLE batch aborts - hvds: "we should not
    reach [an expensive rung] unless all the numbers have either failed
    all previous rungs or have been found to match the required tau."
    Modelled as the product, across all candidates in a call, of each
    one's own "never causes an abort" probability - an approximation
    (ignores exact rung-major interleaving order) but a real
    improvement over treating candidates independently, which applied
    no such filter at all.
- **Windowed real-vs-mock comparison methodology** (hvds, this
  session): a single run can't validate an *expected-cost* model,
  since the real outcome for a given number is deterministic, not
  random - there's no way to get statistical power by repeating an
  identical test. hvds' fix: compare real vs mock across several
  consecutive, same-width windows at a large magnitude (e.g.
  `x=Ze21:(Z+1)e21` for `Z=0..7`) rather than one run - this
  successfully distinguished "real, reproducible bias" (confirmed: an
  aggregate ~11x mock/real overestimate, consistent in direction
  across all 8 windows, PRE-dating this session's compatibility-split
  rewrite) from single-run noise. **This is the tool to use for
  re-validating aggregate cost accuracy** - see next steps.
- **`g_mock_family_s[]`** (diagnostic, `atexit`-printed as
  `MOCK_FAMILY_BREAKDOWN`): per-family (ecm/p1/qs/fixed) cost
  accumulator, used to isolate the pre-rewrite ~11x overestimate to
  the P-1 family specifically, dominated by the single most expensive
  rung (`tmf_31`, P-1 5M/100M rung). Not gated behind any flag -
  harmless overhead, always printed when `MOCK_LADDER` is built.

## Resolved late 2026-09-24: batch_survival collapse, and much more

Commits `db7341c..5348b94`. See the `5348b94` commit message for the
full list; in brief:

- **Diagnosis**: the collapse was genuine *probability* (almost every
  batch is meant to abort) combined with a wrong *cost* formula:
  `total * P(no abort)` charged aborted batches nothing. Replaced by a
  rung-major walk over per-entry events, each weighted by P(no other
  entry has aborted yet). An aborted batch costs what was spent before
  the abort.
- **Ground truth**: `make LADDER_STATS=1` builds a real pcoul that
  prints per-rung (and per-8-bit-bucket) tries/hits/seconds, in the
  same shape as the mock's `MOCK_LADDER_STATS`/`MOCK_LADDER_BUCKET`.
  **This is now the primary validation tool** - far more diagnostic
  than whole-run timing, since it shows which rung is wrong and at
  what size.
- **Real-code bug found** (`db7341c`, needs hvds review): after
  splicing out the last live entry, `tau_multi_run()` redid rung i on
  the dead entry - e.g. 400000 brent63 rounds on a known prime.
  Results unchanged; real ladder time -54% at 1e27, -15% at 1e30.
- **Model bugs fixed**: missing 1/b^2 in the smallest-factor density
  (the dominant error once the structure was fixed); P-1 rungs with B2
  in the curves slot; ECM cost not scaling with B1; roughness bound
  ignoring the build; brent63/tinyqs bits-independent; prep-resolved
  entries charged a full ladder; odd-t / t==2 follow-ups modelled as
  full ladders or free successes; `tm->e` ignored; factor size
  resampled per rung.
- **Current accuracy** (`pcoul -X 88 5`, real build includes the
  splice fix): 1e27 real 0.038s / mock 0.030s; 1e30 0.278 / 0.325;
  1e33 2.27 / 2.45, with per-rung tries/hits/cost within ~15%. Windows
  `Ze31:(Z+1)e31`, Z=1..8: mock/real 0.89-1.28, mean ~1.11.

## Open gaps (see coulmock.c comments for detail)

- **Coverage**: D(88,5) up to 1e33 only exercises rungs 2-4 (brent63,
  P-1 5000, tinyqs) plus a trickle of 11-13. Everything from rung 5 up
  - the deep ECM/P-1 rungs, QS, and the B1 chain - is modelled but
  essentially unvalidated. Needs a workload with larger residuals.
- Mild residual overestimate (~1.1x over 8 windows), mostly rung 3
  P-1 cost at 88-103 bits (mock ~75us/try, real ~56us).
- Squfof (rungs 5, 10) still bits-independent with 0% success; never
  reached in the runs so far (tinyqs precedes it).
- Placeholder check costs (`CT_PRIME_S`, `IS_TAUX_S`); real non-rung
  overhead is `LADDER_TOTAL total_s - rung_s`, ~1.5% of ladder time so
  far, and the mock's check costs land in roughly the same place.
- `p_cofactor_prime()` is a Mertens-style estimate, not checked.
- Only the smallest factor is modelled; P-1/ECM can find any factor.
  Seems not to matter at these sizes (hit rates match), may matter
  for larger residuals with several mid-sized factors.
- tm->B1 not carried into a retried chain; relative-B1 rungs with no
  B1-setting rung earlier in the pass are treated as no-ops.
- `nqc>0` (have_square/Pell branch) multiplicity theory unverified.
- QS chart still rough; `WalkCost.pm`'s `mean_prep_cost_ns()` still
  lacks bits-scaling.
- Factor size is still one *sample* per residual, so mock totals have
  sampling noise; see simplifications below.

## Simplification directions (for "close enough and fast")

- Rung-model fits are now per-rung empirical curves in bits, and
  rungbench can refit them after a library upgrade in minutes. A
  cruder but faster mock could replace the per-residual chain
  expansion with a per-(rung, 8-bit bucket) table of *conditional*
  hit rate and cost measured directly by LADDER_STATS - that captures
  ladder-order conditioning for free, at the price of needing a real
  run per library version and per rough workload shape.
- The cross-candidate walk costs O(events * count); with count <= k
  this is small, but it could drop to O(events) by keeping a running
  product and dividing out the current entry's own term.
- Most mass sits in rungs 2-4 at these sizes; a short-circuit that
  stops expanding a chain once its remaining weight is below, say,
  1e-4 would cut work substantially without visible effect.

## If this work resumes: suggested order

1. hvds: review `db7341c` (real-code splice fix) independently of the
   mock work.
2. Find a workload that reaches rungs 5+ at real volume (larger
   residuals - a bigger target size or different n/k) and repeat the
   LADDER_STATS vs MOCK_LADDER_STATS comparison there; fit/verify the
   deeper rungs with rungbench as done for rungs 2-4 and P-1.
3. Replace the placeholder check costs and `p_cofactor_prime()` with
   measured values if they show up as material there.
4. Then decide which simplification (above) is close enough for the
   calibration goal, measured against the same windowed comparison.
5. Deferred: nqc>0 theory, B1 chaining, QS chart fidelity.
