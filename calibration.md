# Calibration and cost models for pcoul

Status as of 2026-09-30. This replaces pcoul-batch-harness-design.md,
walk-cost-model-status.md, gate-cost-model-status.md and
calibration-estimator-status.md.

## Aims

Most of pcoul's CPU time goes on runs that prove an upper bound is
minimal: zmax is fixed (as if with -X), and no candidate is expected to
lower it mid-run. Everything here is costed at the requested zmax.

- End goal: a runtime optimiser. At each node pcoul chooses walk or
  recurse, which position to allocate next (best_v()) and whether and
  how far to pre-walk large primes (-W), by estimated cost, instead of
  by fixed options (-g, -j, -W) tuned by hand.
- Interim: `calibrate` chooses options for a whole run by timing a
  sample of its batches with the mock pcoul.
- Further off: a batch harness that runs batches separately with
  per-batch settings. Requirements, kept from the earlier design: a
  persistent per-batch ledger (batch, bound confirmed, settings, time,
  status); one authoritative current bound, propagated to every new
  dispatch (a batch confirmed against a larger bound stays confirmed);
  an independent audit tool that proves an aggregated run complete,
  distinguishing not-attempted from timed-out batches; dispatch order
  by cost, or by an externally supplied likelihood when given.

## What exists

### The mock pcoul (mock.c, MOCK_WALK=1 MOCK_LEAF=1)

Runs the search with the costly parts replaced by their modelled cost,
from the machine's cost table ($MOCK_WALK_TABLE). The 367 line reports
real time outside the mocks plus modelled time; the 368 line is the
modelled part alone, with what was stubbed.

- walk_v(): linear walks and walks of one fixed power (nqc < 2) are
  costed, not run: per iteration the loop, plus the inverse-filter
  pass rate (exact from inv[]; over root residues for fixed powers)
  times the tests. Tests model trial division from the exact or
  modelled valuations of each position's value (honouring the inverse
  filter's exclusions), primality tests stage by stage as
  test_primes() runs them, and the factoring ladder rung by rung as
  tau_multi_run() interleaves its pending values. Pell walks (nqc >= 2)
  run for real.
- walk_1_set(): the first 10000 primes run for real with modelled
  tests (every 8th exactly), the rest charged at their rates.
- MOCK_LEAF: an innermost loop whose first child walks is charged in
  closed form (cprime plus walks scaling as (p0/p)^(x-1)); loops of
  fixed-power walks, and loops above the leaves, are sampled (above
  65536: 8 children of every 128 run and timed, the rest charged their
  mean); the tail of a loop where nearly every prime fails on
  rq > zmax is charged ctail per prime.
- Always real: primes below 65536, apply_single() up to the tail,
  prep_unforced_x(), flips' outer loops, walk_6x(), walk_midp(), and
  each walk's setup.

Validation, mock/real (367 totals, tables of 2026-09-29):

| batch | ratio |
|---|---|
| D(162,3) b9 subtree 397^2 / 97^2 | 1.09 / 1.15 |
| D(48,10) b0 | 1.16-1.21 |
| D(96,8) batches (heavy / small) | 0.93-1.01 / 1.06-1.22 |
| D(18,4) -x1e18 | 0.97 |
| D(90,4) -x1e24 / -x1e22 | 0.88 / 0.94 |

With leaf loops real (MOCK_LEAF_OFF) the 397^2 subtree is 1.00-1.02:
the walk, test and ladder models are right there, and the rest is in
the leaf stubs (~5%) and striding (~3%). Mock runs vary ~4% run to run
(stride samples), as do real ones.

### The cost table (multibench-table)

One table per machine, MPUGMP build and n (`-f<flake>` for runs using
-o). Rows: C (per-operation constants fitted from -dv6 runs and
paired mock runs), S/L (trial division by size and prime), P/R (prime
tests), test_multi() rows by t, e and size, G (the ladder per rung:
reach, cost, hit rate, factor size, cofactor primality), Q (QS alone
by size). Sizes sit either side of the limb boundaries at 64 and 128
bits. G rows from 100 bits use inputs built from their factors, with
the smallest factor oversampled and weighted back (Buchstab). Without
-f, G rows reach 255 bits, and the rows above 230 bits take over an
hour to generate.

Coverage of the ladder: sound to about 191 bits; 207-255 bits from 60
inputs each; above that (with -f only) the single ECM rung is benched
from 12-30 inputs and is rough. Rungs after QS count as never reached.

### calibrate

Lists a range's batches (-a), groups them into strata by log10 of
X = (zmax - zmin)/aq and fixed power, times 3 per stratum under each
candidate setting with the mock, and predicts the full run; a
coordinate search over -j, -g and -W. Since every setting runs on the
same batches, differences between settings are far more precise than
the absolute predictions.

### -ja1 (runtime cost gate)

At a node with no fixed square (and not a flippable 2q^2 loop), walk
or recurse is decided by estimated cost instead of gain: walking costs
a setup plus Z/aq iterations at a cost per iteration learnt per level
during the run; recursing costs 0.2us per prime tried plus the
children's walks, as if every child walks. On every non-square batch
tried (8 D(96,8), 3 of them at 10x zmax, and 5 D(48,10)) it matched or
beat the best gain tried within a few %, with no tuning; the user's
-g24 on D(96,8) was 20-35% slower than both. Recovery honours the
recursion the recovery line shows, without asking the gate again, so
-ja1 can be turned on or off mid-run; tested by recovering D(12,4) and
D(24,5) from 100 random log points, and in t/t10init.

### Instrumentation

A VERBOSE=1 build has it all, chosen at runtime by -dv<bits>
(trace.h): 1 the trace, 2 the records, 4 stage timing.

- -dv2: one record per gate decision, recursion subtree, walk,
  walk_1_set(), flip and midp phase (trace.c). With -dv6 its clock
  reads inflate walks (~10% on D(48,10)); use it for structure and
  ratios, not absolute walk times.
- $MULTIBENCH: the benches behind the cost table (bench.c, see
  multibench-table).
- WALK_FROM / WALK_FROM_CHECK (experimental): once a child of a loop
  walks, later children walk without the gate; the check mode found
  the gate monotone within a loop apart from flips.

## To do

1. -ja2: best_v() by cost at the leaf recursion. Walking the node
   costs W whichever position is chosen, and recursing some x then
   walking is never better, so the choice is min(W, min_i T_i), T_i the
   cost of recursing over every x of position i: W is an incumbent any
   position must beat, and a lower bound on T_i (the primes tried, and
   the child walks of its dominant x) discards most. Positions alike in
   (t_i, q_i, first p) cost the same: take the least i. Positions with
   an x the model cannot cost (making a square) stay with the -j
   strategy. The -j strategies differ by up to 40% per batch under
   -ja1, none winning everywhere.
   Recovery then needs care: insert_stack() replays the recovered
   allocations in best_v() order, which a cost-based choice need not
   reproduce; it could instead take the position holding the last
   pending allocation as the one chosen (or rely on the expanded 315
   form, as for -j4).
2. With that, try "never walk a flippable loop".
3. Fixed squares under the cost gate: a child that completes a second
   square (Pell, nearly free) or flips must be costed as such; the
   per-iteration cost of square walks varies too much between levels
   to borrow.
4. Deeper lookahead (a further -ja level), and -W decided per node by cost.
5. In calibrate: Neyman allocation of samples across strata and a
   per-power (-Wx) search; with -ja1 the gain drops out of the search
   for non-square batches.
6. Mock accuracy: the leaf-stub shape in loops of mostly rejected
   primes; ctail varies by batch (0.187-0.229us per prime, no predictor
   yet); walks ~6% high on D(48,10); D(90,4) 0.88; fixed-power walks
   lack the inverse filter's exclusions; the loop0/looptest (and
   sqsetup/sqloop0) fits are nearly collinear.
7. The ladder above 299 bits: price the single ECM rung from timed
   failing attempts and hit rates by smallest-factor size measured at
   smaller n; end-to-end validation above 159 bits.
8. The batch harness.

## Why some of this is hard

- The upper levels are discrete: forced primes, the first unforced
  allocations, mintau exclusions and best_v()'s choices depend on the
  path. Density arguments fail there, so they have to be enumerated
  (the mock runs them for real).
- Walk or recurse is a threshold, so the tree's shape changes abruptly
  with the options. Estimates of whole subtrees compound their errors
  with depth.
- Walk costs depend on residues, not only sizes: inverse-filter pass
  rates, fixed-power root counts, and where a loop starts failing on
  rq > zmax. These are computed exactly per walk, not averaged.
- The per-iteration cost of a walk varies with level and shape (0.9us
  per root at level 2 against 1.8us at level 3 on D(90,4)), so it
  cannot be borrowed between levels.
- Factoring costs are heavy-tailed: rare inputs reach rungs costing
  seconds to hours, so sampling needs weighting, and means need many
  samples.
- Costs step with limb count (at 65 bits a t=15 prep costs 2.4x that
  at 64) and with QS parameters by decimal digits.

## Methodology lessons

- LARGE_MIN (on by default in the Makefile) makes the gate use
  zmax - zmin, so narrow -x windows walk where the full range would
  recurse. Build without it to make a narrow window just below zmax
  reproduce the full run's gate decisions and recursion, walking only
  the window (walk counts then scale by the window's fraction of the
  range, or 1 - (zmin/zmax)^(1/g) for fixed powers). Without
  LARGE_MIN, a walk's starting ati beyond 2^64 goes unchecked.
- Time with nothing else running: two vCPUs slow each other 10-15%.
  Real runs of the same batch vary ~4%.
- For fine timing inside pcoul use CLOCK_THREAD_CPUTIME_ID: once the
  diag and log timers are armed, the process CPU clock advances only
  at scheduler ticks.
- Read the mock's 367 line, not the 368 line.
- Build without PORTABLE (it is for distribution binaries).
- Per-node comparisons across runs need the node set to be the same:
  pair by order only at levels whose parents decide identically.

## Tried and dropped

- An analytic recursion estimator (lib/Calibrate, Mertens-style sums
  per level): exact at the top decision, but 2-8x spread per batch on
  D(12,9) and up to 49000x wrong on fixed-square batches.
- batch-estimate (idealised recursion from batch records): 1.1-1.8x,
  too slow for batches with huge X.
- MOCK_LADDER (coulmock.c): a per-residual chain model of the ladder
  from Dickman's rho; superseded by the measured G rows.
- For -ja1: fixed-square nodes with the same estimate (lost 12-40%), a
  per-level correction learnt from timed recursions (wrong shape: the
  big recursions set it, the marginal ones suffer), and a two-level
  estimate (no gain over one level).
- WALK_FROM as a speedup: the gate costs ~1us, so skipping it gains
  nothing measurable.
