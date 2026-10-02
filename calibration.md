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

The table is in sections (scan, prime, multi, ladder, qs, walk, w1s,
leaf, tail, situ), each stamped with the build that made it ("V section
sha"): `-s<sections>` rebuilds only some, and `-u<table>` takes the
rest from an existing table, so a new MPUGMP needs only scan, prime,
ladder and qs (and multi), a change to coul.c only walk, w1s, leaf,
tail and situ. pcoul builds in a default table from the file cost-table, used
unless $COST_TABLE names another (or, as before, $MOCK_WALK_TABLE);
`-dT` notes sections from a different build.

### Counted costs for -ja

-ja1 and -ja2 learn from costs counted from what the run did, not from
its timings, so that identical runs make identical choices: walk
setups, iterations and inverse entries tested, fixed-power walks, roots
and entries, walk_1_set() primes iterated and passing the check, and
recursion primes tried and applied, each at its table cost; each test's
preparation by the steps it took (trial primes by limbs, gcds by band,
bits tested for primality, power tests), at the K rows' costs fitted in
situ; prime tests' preparations by outcome and size, likewise; and the
ladder at its expected cost from the G rows on the values pending. A
`369` line reports the total, for comparison with the run's time.

Against CPU time over 22 runs the counted total first ranged 0.56-1.41
(coefficient of variation 0.25), pricing each preparation from the
bench rows by where it stopped: in situ preparation cost 0.8-2.6x that
price, varying by run, from caches and branch prediction in the full
program, the coarse S sizes, and skip_trial_bands(). Priced by its
steps from the K rows, each run's preparations come within 0.94-1.07
of their time (D(64,3) -j4 -x1e15, whose time is almost all
preparation, among them), and the whole run's counted total within
0.82-1.28 over 30 runs (mostly 0.95-1.13). What remains is in the walk
and recursion constants, fitted outside the full program or not at all
(capply); a -dv32 W record per run allows a regression of the run's
CPU time on all the counts, but over 30 runs it barely improves on
that (0.79-1.13) and the constants are poorly determined, so it is
left as a check. With counted costs D(64,3) -j4 -x1e15 took 7.9s,
then 29s as the pricing improved, then 5.2s: its choices at the root
are made before any learning, so they turned on small differences in
the estimates, until the learnt ratio for recursing was given a prior
of 1/4 (0.1s).

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

The estimate of recursing is too high near the root, where a wrong
choice to walk costs most: D(64,3) -j4 -x1e15 took 29s under -ja1,
walking at level 1, against 0.04s with no -ja. So the gate scales that
estimate by 1/4, as -ja2 does before it has learnt better: 0.05s there,
D(60,3) -j2 -x1e13 1.02s to 0.59s, D(48,4) -j2 -x1e12 0.68s to 0.28s,
and the other 26 runs of the benchmark set within 3% either way.
For n = 2^x.3 it is what lets -j4 pay as x grows (-ja1, seconds without
and with the factor, 90s allowed):

| run | -j0 | -j2 | -j4 |
|---|---|---|---|
| D(24,6) -x1e13 | 4.00, 4.08 | 3.47, 3.48 | 3.84, 3.80 |
| D(48,4) -x1e15 | 0.33, 0.31 | 0.67, 0.28 | 0.33, 0.34 |
| D(96,3) -x1e15 | 5.88, 5.97 | 13.44, 13.27 | 5.85, 0.73 |
| D(96,4) -x1e16 | 42.43, 40.30 | 45.09, 35.79 | 37.60, 12.48 |
| D(192,3) -x1e16 | >90, >90 | >90, >90 | >90, 27.66 |

### -ja2 (choosing positions by cost)

At a node with no fixed square, walking it costs W whichever position
is chosen, and recursing over some x then walking is never better, so
the choice is between walking and recursing over every x of some
position (ja_choose()): W and the strategy's choice are incumbents, and
other positions are costed (x_range() and the -ja1 estimate) until
they pass the incumbent; positions alike in (t, q, last p, x,
maxforce) cost the same. An x leaving a square is costed as if it did
not (an overestimate, corrected by learning, below); where a position
has an x the model cannot cost (a flip), the strategy's choice stands.
On
four D(96,8) batches at the usual zmax, -ja2 matched the best of
-j0..-j2 under -ja1 on each (whichever it falls back on), beat all of
them on one by 20%, and took 26-45% less time than -j4 -g24. There,
99% of its choices walk the node, and under 1% choose another
position. On D(48,10) batches 1-12 at -x22911293821947932 -j2 -f7
-g30 it took 25-60% less time than -ja1 on every batch that took
measurable time, and on runs with many squares 45-50% less (D(36,5)
-j2 -x1e12: 85s against 169s; D(60,4) -j0 -x1e15: 2.2s against 4.2s).

-ja2 learns from its choices: each choice made by cost is timed
(thread CPU time, as for -ja1), a walk whole and a position by each of
its x, and per level the actual cost against the estimate, in four
parts (walking, recursing, recursing into a square, walk_1_set()),
gives a ratio by which later estimates of each part are corrected
(starting from 1ms of evidence at ratio 1). Each x is of a single
part, so the attribution is exact: splitting a whole subtree's cost
between its parts in proportion to their estimates contaminated the
ratios (walk_1_set() at 40-65x), and once squares were costed, sent
D(60,4) -j4 -x1e15 from 2.1s to 190s. On
D(36,5) -j4 -x1e10 the ratios found were 0.00-0.01 for recursing at
level 2, 0.1 at 3, 0.4 at 4 and about 1 at 5 (the depth-1 estimate
assumes every child walks), about 2 for walk_1_set() (now charged 2us
per prime reaching its tests, as measured, not 1us), and 1.2-1.5 for
walking. Without that, -ja2 -j4 on D(36,5) chose vast walk_1_set()
ranges: -x3e10 took 87s against 14.5s under -ja1, -x1e11 over 300s
against 44s; learning, 5.5s and 15s. Elsewhere learning changed
nothing beyond noise. Costing positions that leave a square helps
where the strategy is poor: D(60,4) -j2 -x3e14 took 3.6s against 133s
(-j0 takes 1.6s), and on the other runs tried it changed nothing
beyond noise. The square ratios learnt are small (1e-5 at level 2,
0.01 at level 4, 0.6 at level 5).

The -ja1 gate, still deciding walk or recurse for each x of a position
-ja2 has chosen, applies the same learnt ratios. Without them, it used
the raw depth-1 estimate, so could walk a node that -ja2 had learnt to
recurse: choices then depending on timing noise, D(60,4) -j2 -x5e14
took 4.6s in most runs but 100s in about 1 in 7, from two walks at
level 3 of 27M and 103M iterations, and -x1e15 196s; D(60,4) -j0
-x1e15 once took 188s against 2s. With the ratios applied there too,
16 runs of -x5e14 all took 4.3-4.7s, -x1e15 takes 6.6s (-ja1: over
300s), and D(60,4) -j0 1.8s; the other runs tried are unchanged.

With all that, 13 runs repeated 5 times each varied by under 10%, and
the strategy chosen matters much less (D(60,4) -x1e15 at -j0/-j2/-j4:
1.8/6.2/1.9s against 3.7/295/2.0s under -ja1; D(36,5) -x3e10 4.8-5.6s
for each, against 9.1-14.1s). Tiny runs lose a little: at a zmax far
above the answer to the known weakness below, as before learning
(D(24,5) -j0 -x1e13: 0.19s against 0.15s), and at one just below it
to the cost of choosing (-x15537947: 0.11s against 0.09s). On
the D(96,8) batches at -x393643805345636319 -f5 (b5, b50, b5000,
b350000), -ja2 took 10.3-10.7, 30-31.7, 4.3-4.5 and 12.6-13.5s with
-j0 or -j2, about 10% less than before learning and up to 25% less
than -ja1; with -j4 it was 3% slower than -ja1 on b50, faster on the
rest.

Choosing has a cost of its own, about 1us for each position weighed
(x_range()'s integer root and the sum over primes, for each x), which
is as much as a whole node where nodes are cheap: D(96,3) -j4 -x1e15
made much the same search as under -ja1 (415k recursions against 399k,
the same tests) in 1.10s against 0.74s. By the -dv8 records, at nodes
that would cost under 10us to walk (60-90% of them) the choice is
estimated to save 0.03-0.9us a node, and from 100us tens of us or
more. So where walking would cost under 100us (JA_MIN_WALK) the
strategy's choice stands and the gate decides, as under -ja1. Over 42
runs (the benchmark set, and n = 24, 48, 96, 192 at -j0, -j2, -j4) that
was never slower beyond noise (1.02x at worst), up to 2x faster
(D(48,4) -j4 -x1e15: 0.76s to 0.38s) and 9% less time in all. A
threshold of 10us did much the same; 1ms lost up to 60% on D(36,5) and
D(36,6) at -j2, where the choices matter.

Recovery: 315 lines mark only levels chosen against the strategy, the
rest replayed by it. A 316 line before each progress line records what
has been learnt (see ja_save()): the cost counted, the gate's walk
samples and -ja2's actual and estimated costs by level, so that a
recovered run carries on from them. Recovering twice from one log gives
identical runs. Of 9 runs killed partway and recovered, 7 then made
exactly the tests the uninterrupted run made in all, and 2 differed (by
0.2% and 2%; without the 316 lines, 8 differed): what was being
measured as the line was written, a walk and each choice on the path to
it, is not recorded, so the recovered run learns nothing from those.

### Instrumentation

A VERBOSE=1 build has it all, chosen at runtime by -dv<bits>
(trace.h): 1 the trace, 2 the records, 4 stage timing, 8 the -ja2
choices, 16 the test preparations (T and U records), 32 the run's
counts and CPU time (a W record).

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

1. -ja2 (done, experimental; see below): a real model of x leaving a
   square, rather than the overestimate corrected by learning; and of
   recursing near the root, where learning starts blind and single
   choices are dearest (for now the learnt ratio for recursing starts
   from 1/4 rather than 1, see ja_ratio()). Measure run-to-run
   variation as a matter of course where choices depend on timings:
   one slow run in several is easily missed.
   Known weakness: when zmax is far above the answer, -ja2 can be slow
   to find the first candidate, since it optimises the cost of the
   whole search at the current zmax, not how soon zmax falls. D(24,5)
   -j4 -x1e13 took 0.57s to the first against 0.00s under -ja1 (0.75s
   against 0.16s in all); with the prior of 1/4 it finds the first at
   once, but takes 0.25s in all. At a zmax near the answer the two are
   within 0.03s there, so this matters little for runs proving a bound
   minimal.
2. Fixed squares under the cost gate: a child that completes a second
   square (Pell, nearly free) or flips must be costed as such; the
   per-iteration cost of square walks varies too much between levels
   to borrow.
3. Deeper lookahead (a further -ja level), and -W decided per node by cost.
4. In calibrate: Neyman allocation of samples across strata and a
   per-power (-Wx) search; with -ja1 the gain drops out of the search
   for non-square batches.
5. Mock accuracy: the leaf-stub shape in loops of mostly rejected
   primes; ctail varies by batch (0.187-0.229us per prime, no predictor
   yet); walks ~6% high on D(48,10); D(90,4) 0.88; fixed-power walks
   lack the inverse filter's exclusions; the loop0/looptest (and
   sqsetup/sqloop0) fits are nearly collinear.
6. The ladder above 299 bits: price the single ECM rung from timed
   failing attempts and hit rates by smallest-factor size measured at
   smaller n; end-to-end validation above 159 bits.
7. The batch harness.
8. Counted costs: price test preparation from its own work (trial
   primes tested, gcd bands skipped, prime tests by size) at per-step
   costs calibrated in situ from instrumented runs, as the walk loops
   are; likewise apply_single() and the ladder. Then t rows by class
   of t rather than per t, so that one table serves every n (the
   largest n with known values is 8000).

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
- Never walking a loop whose children can flip (t = 2q^2): D(60,3) -j2
  -x1e13 7x slower under -ja1, D(36,5) -j0 -x3e10 3x slower under
  either, D(36,4) -j4 1.7-3x; only D(64,3) -j4 gained, by 1.5%.
