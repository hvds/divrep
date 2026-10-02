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

The benches' inputs are the same from run to run (each bench seeds a
GMP generator of its own from a constant and the size, and each size is
a fresh process, so MPU::GMP's ISAAC starts from seed 1 too), but need
not be between versions of GMP, whose default generator may differ.
Only the inputs depend on it: the search draws on ISAAC alone. Five
runs of the 112-bit ladder bench agreed in every column but the times,
of which four agreed within 5% and one was 15-60% slower throughout.

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

### Rejecting primes early

Broken into components, the counted cost of -ja2 -j4 runs was about
half in the recursion loops' primes on the production-like batches
(D(96,8) b5, b50, b350000 and D(48,10) b7: 46-50%, with 43-51% in
tests and 2-7% in walk loops), where 200-360 primes are tried for each
one that applies; D(60,4) -x1e16 58%, D(12,8) 42%, D(96,4) 26%. The
choice to recurse is right there (walking those nodes would cost
seconds); what dominates is the cost of rejecting a prime, 240ns: the
level set up, p^{x-1} and the CRT in mpz_t, then rq > zmax.

Almost all are rejected for that last reason, which is t > (zmax - rq)
/ aq for the multiple t of aq the CRT finds, a bound shared by the
whole loop. Of 24M rejections on D(96,8) b5, nearly all were of p^2
with p of 16-24 bits. So the loop now finds t itself in single limbs
first (reject_single()): its last digit base p, which is no more than
t and rejects most, needs only a 32-bit inverse mod p; for p^2 the
next digit comes from the same inverse; other powers take the inverse
mod p^{x-1}. That is about 100ns a prime, 80ns of it the inverse. The
search is unchanged: of 82 runs compared with it on and off (-ja1,
-ja2 and plain -g, with -W, and at 2 limbs), all that finished made
the same recursions, walks and tests.

With cprime and ctail measured again (0.22us to 0.14us, 0.23us to
0.12us), and the gate's cost per prime lowered to match (GR_APPLY,
0.2us to 0.12us), the 42 runs took 12% less time in all under -ja2,
and the production-like ones 21-25% less: D(96,8) b5 11.3s to 8.8s, b50
33.7s to 26.5s, b350000 14.2s to 10.8s; D(48,10) b7 2.02s to 1.63s;
D(60,4) -x1e16 7.8s to 5.9s; and the D(162,3) batch used to calibrate
ctail (-x3.07e21, aq of 2 limbs) 32.4s to 22.5s. Under -ja1 the 29 runs
of the benchmark set took 24% less in all. A table made before this
has cprime and ctail too high: rebuild its leaf and tail sections.

### Primality in single limbs

With primes rejected early, the next cost was the primality test of
what trial division leaves: about 60 bits on the D(96,8) and D(48,10)
batches, half of them prime. _GMP_is_prob_prime() takes 3.2-3.4us for
those, nearly all of it the Lucas test in mpz_t arithmetic (its
strong test to base 2 is 0.5us). u64_bpsw() makes the same BPSW test
for a value of a single limb in Montgomery arithmetic: the same strong
test to base 2, then the same "almost extra strong" Lucas test with the
same parameters, so the same answer, in 0.6-0.9us. test_prime checks
it against _GMP_BPSW() on 9.7M values (every n below 2^22, squares,
cubes, semiprimes, random values of every size to 64 bits, the ends of
the range and known pseudoprimes); 42 runs made the same search with
it as without.

Values of more than a limb still go to MPU::GMP, and there the cost of
a preparation steps up sharply (about 20us for a 65-70 bit value that
reaches the primality test), so the K rows price the bits tested apart
(preppbit for a single limb, prepzbit beyond). The calibration run
that was to supply such values gave only 19 records in its minute, so
the situ section now takes them from the D(162,3) batch and from
D(36,5) -x1e22. And tau_prime_run()'s own tests, which the K rows had
left uncharged, are now charged as tau_multi_prep()'s are.

With the table fitted again, against the state before primes were
rejected early: D(96,8) b5 11.3s to 6.5s, b50 33.7s to 19.3s, b350000
14.2s to 8.0s, b5000 4.9s to 2.7s; D(48,10) b1, b7, b12 1.5-2.0s to
0.9-1.2s; D(60,4) -x1e16 7.8s to 5.1s; D(18,4) -x1e16 4.3s to 3.3s;
the 42 runs 19% less time in all under -ja2, and the benchmark set 35%
less under -ja1. Runs whose values are small or whose time is in walk
loops gain little (D(96,4), D(192,3), D(48,4): within 5% either way).

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
estimate by 1/4 (GR_RSCALE; -ja2 learns the scale instead): 0.05s there,
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

The ratio for recursing was at first learnt per level, like the rest,
but nodes of one level differ far more than nodes of one size. From
175k records of estimate against actual cost on D(96,4) -j4 -x1e16,
actual/estimated falls smoothly with the size of the node: 0.6 for
nodes that would cost 0.1-1ms to walk, 0.06 at 0.1-1s, 0.004 at 1000s.
The ratios per level, each dominated by the largest nodes of its level,
were 0.000 at levels 2-4, 0.57 at level 5 and 0.016 at level 6, so
that at level 5 it walked what -ja1 recursed (20.7M walk iterations
against 8.7M, 17.6s against 12.5s). Correcting each record by its
level's ratio left a cost-weighted error of 3.1 decades there and
0.15-2.3 on eight other runs; by decade of size 0.33, and 2-8x less
than by level on every one. So the two recursing parts are now learnt
in bands of the node's estimated cost to walk, a factor of 8 each
(ja_rsize()), a band with no evidence starting from 0.4 of the ratio
in use for the band below (0.25 and 0.6 do the same within 3%). Over
the same 42 runs that was never slower beyond noise and 4% less time
in all: D(96,4) -j4 -x1e16 17.6s to 11.9s, D(48,4) -j4 -x1e15 0.38s to
0.28s, D(96,3) -j4 -x1e15 0.77s to 0.64s, D(60,4) -j0 -x1e15 2.04s to
1.77s, D(96,8) b50 -j4 36.0s to 33.4s.
Keying by the position's own estimate instead fits the records as
well, but chooses worse (D(60,4) -j0 -x1e15: 9.5s): it shrinks large
estimates more than small ones, so distorts the comparison between
positions at a node, where a ratio shared by the node cancels.

#### Where -ja2 pays

Each run under -ja1 and -ja2 at four strategies (seconds, 120s
allowed; the D(48,10) batches at -x22911293821947932 -f7 -g30, the
D(96,8) batches at -x393643805345636319 -f5), with primes rejected
early and primality tested in single limbs (see above):

| run | -ja1: -j0 | -j1 | -j2 | -j4 | -ja2: -j0 | -j1 | -j2 | -j4 |
|---|---|---|---|---|---|---|---|---|
| D(24,6) -x1e13 | 2.92 | 2.94 | 2.65 | 3.09 | 2.46 | 2.46 | 2.56 | 2.56 |
| D(48,4) -x1e15 | 0.31 | 0.30 | 0.32 | 0.30 | 0.31 | 0.31 | 0.31 | 0.29 |
| D(96,3) -x1e15 | 6.36 | 6.37 | 14.05 | 0.72 | 6.31 | 6.36 | 6.38 | 0.61 |
| D(96,4) -x1e16 | 40.70 | 39.93 | 36.23 | 11.17 | 38.34 | 38.30 | 38.07 | 11.13 |
| D(192,3) -x1e16 | >120 | >120 | >120 | 28.54 | >120 | >120 | >120 | 31.03 |
| D(40,5) -x1e17 | 0.80 | 0.80 | 0.66 | 0.84 | 0.74 | 0.75 | 0.78 | 0.76 |
| D(80,5) -x1e16 | 2.41 | 2.39 | 2.08 | 2.39 | 2.26 | 2.24 | 2.42 | 2.33 |
| D(20,6) -x1e18 | 1.60 | 1.60 | 1.33 | 1.59 | 1.22 | 1.22 | 1.22 | 1.22 |
| D(64,3) -x1e15 | 30.35 | 30.39 | 30.66 | 0.05 | 30.87 | 31.17 | 31.06 | 0.07 |
| D(32,5) -x1e14 | 51.99 | 48.53 | 49.06 | 1.15 | 48.85 | 49.07 | 48.78 | 1.09 |
| D(36,5) -x1e10 | 4.90 | 4.81 | 3.41 | 4.90 | 1.73 | 1.72 | 1.86 | 1.78 |
| D(36,6) -x1e11 | 14.07 | 14.00 | 8.66 | 13.69 | 4.25 | 4.27 | 4.72 | 4.22 |
| D(18,4) -x1e16 | 3.44 | 3.60 | 26.70 | 3.42 | 3.46 | 3.45 | 26.43 | 3.43 |
| D(100,3) -x1e18 | 1.75 | 1.77 | 1.97 | 1.74 | 1.29 | 1.27 | 1.97 | 1.26 |
| D(100,4) -x1e18 | 6.95 | 6.99 | 3.09 | 6.91 | 1.91 | 1.90 | 1.81 | 1.92 |
| D(90,3) -x1e15 | 5.65 | 4.30 | 76.00 | 4.33 | 4.47 | 4.44 | 27.21 | 4.40 |
| D(144,3) -x1e15 | 3.09 | 3.15 | 3.02 | 3.23 | 2.11 | 2.16 | 2.75 | 2.14 |
| D(60,4) -x1e15 | 2.64 | 1.48 | >120 | 1.46 | 1.25 | 1.25 | 5.16 | 1.28 |
| D(60,4) -x1e16 | 14.06 | 6.53 | >120 | 6.55 | 5.28 | 5.21 | 17.13 | 5.16 |
| D(120,4) -x1e16 | 13.36 | 7.12 | >120 | 7.12 | 6.33 | 6.33 | 14.46 | 6.20 |
| D(12,8) -x1e12 | 16.62 | 16.65 | 16.56 | 16.80 | 12.99 | 12.71 | 12.71 | 12.82 |
| D(12,7) -x1e9 | 0.17 | 0.17 | 0.15 | 0.17 | 0.14 | 0.14 | 0.14 | 0.14 |
| D(24,5) -x1e12 | 0.16 | 0.13 | 0.13 | 0.14 | 0.14 | 0.14 | 0.14 | 0.15 |
| D(48,10) b1 | 1.25 | 1.25 | 2.56 | 1.30 | 0.92 | 0.91 | 0.91 | 0.92 |
| D(48,10) b7 | 1.25 | 1.23 | 2.58 | 1.24 | 1.15 | 1.16 | 1.16 | 1.18 |
| D(96,8) b5 | 9.19 | 9.23 | 6.35 | 9.31 | 6.73 | 6.71 | 6.65 | 6.65 |
| D(96,8) b50 | 23.32 | 23.21 | 19.29 | 23.23 | 19.38 | 19.54 | 19.54 | 19.60 |
| D(96,8) b5000 | 2.85 | 2.86 | 3.45 | 2.91 | 2.80 | 2.80 | 2.83 | 2.80 |
| D(96,8) b350000 | 10.28 | 10.26 | 12.60 | 10.53 | 8.18 | 8.10 | 8.11 | 8.20 |

Taking the best strategy for each:

- -ja2 is 1.7-2.0x faster than -ja1 on D(36,5), D(36,6) and D(100,4);
  1.15-1.45x on D(144,3), D(100,3), D(48,10) b1, D(12,8), D(60,4),
  D(96,8) b350000, D(96,3) and D(120,4). Those are mostly n with an odd
  square, or two odd primes, or small n with large k.
- They are level (within 10%) on the other D(96,8) and D(48,10)
  batches, n = 20, 24 and 48, D(32,5), D(96,4), D(18,4), D(90,3),
  D(80,5) and D(192,3).
- -ja1 is ahead by 12% on D(40,5) (at -j2), and by 0.02s on D(64,3).

But the best strategy is not known beforehand, and -ja1 depends on it
far more: its worst strategy takes over 10x its best on 7 of the 29
runs, and over 120s on 4 of them; -ja2's only where -j4 is needed
under either (D(96,3) and the powers of 2). -ja2 at -j4 is never more
than 15% behind the best of -ja1's four (D(64,3) apart, 0.07s against
0.05s), nor more than 7% behind -ja2's own best.

Two things still tie -ja2 to the strategy. Only -j4 lets it allocate
p^{2^x-1}, without which D(96,k), D(192,3) and the powers of 2 take
3-600x longer whatever chooses the positions. And at nodes with a
square already fixed the strategy still chooses: that is why -j2 costs
it 2-8x on D(18,4), D(90,3), D(60,4) and D(120,4) (on D(60,4) -x1e15,
strategy 2 takes the position with tau 3 left, for walk_1_set() over
600k primes at a time). With another strategy little time goes there
(square walks and walk_1_set() under 1.5% of 13 runs of 14, D(18,4)
apart), so a cost model for those nodes has little to gain beyond
avoiding that; and overriding strategy 2 at them still leaves D(90,3),
D(100,3) and D(144,3) slower at -j2, where it also chooses the nodes
that a flip may follow.

Recovery: 315 lines mark only levels chosen against the strategy, the
rest replayed by it. A 316 line before each progress line records what
has been learnt (see ja_save()): the cost counted, the gate's walk
samples and -ja2's actual and estimated costs by level and by size of
node, so that a recovered run carries on from them. Recovering twice from one log gives
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
   choices are dearest (for now the ratio for recursing is learnt by
   the size of the node, see ja_rsize()). Measure run-to-run
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
