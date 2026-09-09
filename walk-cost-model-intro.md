# Next topic: model walk_v()'s factorization cost separately from
# recursion structure
 
## What we're talking about
 
The repository `https://github.com/hvds/divrep` has a build target
`pcoul` designed to find upper bounds, and to prove minimal values,
of D(n, k), the least positive integer v such that [ v, v+1 .. v+k-1 ]
all have exactly n factors. That program has many options, and it is hard
to determine what the optimal settings are for any given target, so I
want a calibration tool to help discover optimal settings.
 
The repository has skills files under `.agents/skills` with some of
the details previously discovered.
 
## Why this topic exists
 
The calibration work done previously (branch `calibrate`, see
`calibration-estimator-status.md` and `pcoul-batch-harness-design.md`)
built `Calibrate::Recursion::estimate_batch_cost()`, an analytic
Mertens-style model of an ENTIRE recursion tree - both the
deterministic recurse/walk decision structure and the walk cost at
leaves - collapsed into a single number via a placeholder constant,
`WALK_RATE` (1e7 candidates/sec, never calibrated against anything
real). That conflates two very different things:
 
- **the recursion/allocation structure** (which positions get
  allocated, which primes, when a WALK decision fires, and critically
  how many candidates that walk would examine - this is the `r_walk`/
  `aq` quantity, and it IS deterministic and already well validated),
- **the cost of actually walking those candidates** (dominated by
  factorization/tau-checking each one - genuinely nondeterministic,
  and dependent on the specific factorization library/algorithm in
  use, which is expected to change soon - a Math::Prime::Util::GMP
  upgrade is planned).
 
Trying to model both at once is why the previous approach kept hitting
walls (see "what went before" below) - the model had no way to
distinguish "this batch has many candidates but each is cheap to
reject" from "this batch has few candidates but each is expensive",
and no way to stay valid across a library upgrade even if it had.
 
Hugo's proposed plan (this session) is to separate them:
 
1. Gather real test cases exercising walk_v()'s main (non-square)
   branch.
2. Instrument to learn: how many candidates are rejected WITHOUT
   factorizing (some cheap pre-filter presumably runs first), and for
   the rest, how factorization time depends on required tau and the
   magnitude of the value. The main calls here are test_primes() and
   test_multi(), which should probably be characterized separately.
3. Build a model predicting mean factorization time from primary signals
   (k, the magnitude and required tau of the reduced values, maybe the set
   of allocated primes) - explicitly flagged as the hard part.
4. Rebuild calibration on top of that: replace the actual
   factorization step with "assume the modelled mean time", so the
   nondeterministic part is isolated and the rest of calibration
   becomes a deterministic-cost problem.
 
Interim/parallel goal: a tool to refresh the model's parameters
whenever the factorization behaviour changes materially (the
upcoming MPU upgrade being the concrete near-term case) - i.e. this
should NOT be a one-off calibration but a maintainable, re-runnable
process.
 
## What to carry forward from the previous topic
 
**Reusable and still valid** (this work is not being discarded, it's
the deterministic half of the eventual combined model):
 
- `Calibrate::Recursion::top_level_gate()` - the EXACT walk-vs-recurse
  decision at a batch's first decision point, validated against real
  pcoul traces. Gives `aq`, `r_walk` (the candidate-count for the walk,
  gain-scaled), `p_start`, `limp`, `cap`, `decision` with no pcoul run
  needed.
- The `aq` formula (product over distinct primes in the pattern of
  p^(maxexp(p) [+1 if p==2])), `Calibrate::Mintau`'s mintau()/
  divisors_ordered() ports, both `prep_maxforce()` branches, best_v(j)
  selection rules for j=0/2 - all validated against real
  -DCOUL_GATE_DEBUG-instrumented traces, not just static reading.
- The general principle that `r_walk` (or the underlying zmax/aq
  quantity) already IS the deterministic candidate count for a walk -
  this is exactly the "how many candidates" half of the new plan's
  step 3/4, already solved. The new work is purely "how long per
  candidate", which multiplies against this existing count.
- Working methodology: read source, form a specific hypothesis, then
  verify against a real instrumented build before trusting it. Every
  "obvious" conclusion from pure reading this session that turned out
  wrong (aq's scope, the mintau exclusion rule, a p_start/q_vi
  conflation, tail-extrapolation instability, the have_square trigger
  mechanics) was only caught this way. Given walk_v()'s actual
  behaviour (cheap-rejection mechanism, factorization routine used,
  early-exit behaviour) is completely unknown right now, expect the
  same pattern to apply here.
- A working local build recipe exists (not persisted between
  sessions, but fast to redo): clone `hvds/divrep` and a compatible
  `danaj/Math-Prime-Util-GMP` commit (the Makefile names a known-good
  SHA), `apt install libgmp-dev`, `make pcoul`. A prior instrumentation
  patch (`coul-gate-debug-instrumentation.patch`, delivered separately)
  adds `getenv("COUL_GATE_DEBUG")`-gated debug prints in
  `apply_allocv()`, `mintau()`, and `prep_unforced_x()` - useful
  precedent for the NEW instrumentation needed inside `walk_v()`
  itself, though that function hasn't been touched yet.
 
**Known gaps, still open, related but not blocking this topic**:
 
- `have_square` (both the mid-recursion-discovered case and the
  `[sq=N]`-tagged-from-the-start case) has no real cost model, only a
  crude fallback that is fine when squares are a negligible fraction
  of total cost (measured: ~0.3% on a real D(12,9) sample) and
  wildly wrong (~49000x on one batch) when they dominate (D(18,4),
  where every batch is `[sq=1]`). `walk_v()` itself very likely has an
  analogous split (a much smaller g'th-power-only candidate set for
  the square case) - explicitly out of scope for this topic's first
  pass (hvds: "the main (no square) branch of walk_v()"), but worth
  remembering it's a second, structurally similar modeling problem
  for later, once the non-square case is solved.
- `-W`/`-Wx` (p_mid), `-m`/`-p`/`-c`, `FLIP_PQSQ`'s actual mechanics,
  and several source files (`pell.c`, `coultau.c`, `rootmod.c`,
  `coulvec.c`) remain unexamined - see `next-topic-synopsis.md` for
  the fuller list, prepared for a separate general code-review topic
  that hvds is running independently of this one.
 
## Suggested first steps for this topic
 
1. **Read `walk_v()` itself** (location in `coul.c` not yet
   identified this session) to understand its actual structure before
   instrumenting anything: what does the cheap pre-filter (if one
   exists) check, what factorization/tau-checking routine gets called
   for candidates that pass it, and does that routine have early-exit
   behaviour (e.g. abandoning partial factorization as soon as the
   partial factor count already rules out the target tau)? This last
   point matters a lot for the cost model's shape - "mean factorization
   time" is likely NOT one number per (tau, magnitude) but a mix of
   fast rejects and full factorizations, and the MIX ratio itself may
   depend on tau/magnitude too.
2. **Instrument accordingly** (same `getenv("COUL_GATE_DEBUG")`-style
   pattern as before, or a new dedicated env var if that's cleaner
   given a different function) to record, per candidate examined:
   whether it was rejected cheaply or fully factorized, and if the
   latter, how long that took and what tau/magnitude it had.
3. **Gather real data** across a range of (required tau, magnitude)
   combinations - probably reusing the same D(12,7)/D(12,9)/D(18,4)
   test cases already characterised, plus others as needed to get
   good coverage of the (tau, magnitude) space the model needs to
   cover.
4. **Build the model** (the hard part, per hvds) - functional form
   TBD, informed by whatever the instrumentation data actually shows
   about how factorization time scales.
5. **Design the "recalibration tool"** - what inputs does it need
   (presumably a benchmark suite of representative (tau, magnitude)
   timings, re-run against a new library version to refresh model
   parameters), and how should it be packaged so it's easy to re-run
   later without re-deriving the whole approach. Worth settling this
   design early, even before the model itself is finished, since it
   constrains how the model should be structured (e.g. as a small
   number of named, independently-fittable parameters rather than an
   opaque fit) to be recalibration-friendly.
6. Once the model exists: restart calibration proper, replacing the
   walk_v() factorization step with the model's predicted mean time,
   and combining it with the ALREADY-VALIDATED recursion-structure
   machinery (`top_level_gate`, `aq`, `r_walk` as candidate count) from
   the previous topic.
 
