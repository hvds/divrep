# walk_v() escalation-cost model - status, 2026-09-24

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

## Immediate next step - unresolved from this session

A quick post-compatibility-split-rewrite check
(`./pcoul.mock7 -X -x1e21 88 5`) showed `g_mock_spent_s` coming out
near ZERO relative to the raw per-family sums (e.g. `p1=13.7` but
`total=0.000000` in the `MOCK_FAMILY_BREAKDOWN` line) - i.e.
`batch_survival` (the cross-candidate joint-survival product) is
collapsing close to 0. **Not yet diagnosed**: this could be a genuine
correct consequence of aggressive incompatible-triggering (many
candidates really do have a near-certain eventual incompatible
success somewhere across their full recursive chain), or a bug in how
`p_causes_abort` compounds across rungs/recursion levels. Needs
investigation BEFORE trusting any new aggregate timing numbers from
the rewritten model, and before re-running the windowed comparison to
see whether the ~11x bias improved.

## Other known open gaps (see also `coulmock.c`'s own file-header and
inline comments, which are the authoritative, most detailed version)

- Aggregate cost-prediction accuracy has NOT been re-validated via the
  windowed methodology since the compatibility-split/recursive
  rewrite (blocked on the item above).
- `tm->B1` chaining is not preserved across a `candidate_outcome()`
  recursive re-entry (starts fresh rather than inheriting the calling
  pass's B1 state).
- `t==1` (need remaining `n==1` exactly) and `t==2` (need remaining
  `n` prime) resolution are treated as free/certain, not costed - the
  real `ct_prime()` check has some real, probably small, cost this
  doesn't charge for.
- `nqc>0` (have_square/Pell branch) multiplicity/compatibility theory
  is unverified - flagged by hvds, not investigated this session.
- QS (index 24 in `coulmock.c`) uses a rough hardcoded chart, not
  precisely copied from `WalkCost.pm`'s `cost_simpqs_seconds()`.
- `WalkCost.pm`'s `mean_prep_cost_ns()` still has no bits-scaling term
  (pre-existing gap, not addressed this session) - proper isolation
  needs total-attempted-`ati` count (from `walk_v_call` `nqc==0`
  traces), not survivor count.

## If this work resumes: suggested order

1. Diagnose the `batch_survival`-near-zero anomaly above - this blocks
   trusting anything else.
2. Re-run the windowed real-vs-mock comparison (same methodology: 8
   consecutive same-width windows at a large magnitude, D(88,5) or
   similar) to see whether the compatibility-split/recursive rewrite
   actually improved the aggregate accuracy versus the pre-rewrite
   ~11x bias, once (1) is resolved.
3. If still biased, use `g_mock_family_s[]`'s per-family breakdown
   again to re-isolate which component dominates, same approach as
   before.
4. Gather more `rungbench rand`-mode multiplicity data (one event at
   one factor size isn't a real validation of the `1/p` law, just a
   promising first check) if the compatibility-split theory itself
   becomes the suspect.
5. Only once aggregate accuracy is trusted: revisit the deferred gaps
   above (`nqc>0`, B1 chaining, t==1/2 costing, QS chart fidelity) in
   whatever order the windowed comparison suggests matters most.
