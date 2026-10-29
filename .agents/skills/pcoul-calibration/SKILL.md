---
name: pcoul-calibration
description: How pcoul costs its own work - the cost table, the mocks, and the option that decides by cost (-ja) - with what was measured and what was tried and dropped
---
## Calibration and cost models for pcoul

Reference for the cost work in pcoul: what each part is for, how it
works, what was measured, and what did not work. For the code's own
layout and vocabulary see pcoul-internals.

### The brief

The work began from this request (the introduction to pcoul itself is
left out):

> Three of the main options that control how the program operates are:
> - the strategy (set with -j)
> - the "force all" level (set with -f)
> - the "gain" (set with -g)
>
> During the primary recursion, the strategy determines which value we
> will try to allocate the next prime power into.
> The "force all" level determines which batches we generate: we
> generate every arrangement of powers for all primes up to and
> including this level, for higher primes p <= k we generate only
> those arrangements in which multiple values are divisible by a power
> of p, and if any arrangements are skipped we catch them with a
> single "tail" batch in which no power of p is specified.
> The "gain" forms part of the heuristic used to decide whether to
> recurse deeper or walk all values at this stage. The heuristic
> attempts to compare an estimate of the range of primes that would
> need to be allocated at the next level against an estimate of the
> number of values that would need to be checked if we walked at this
> level; the latter is multiplied by the gain before comparing them,
> so increasing the gain causes us to recurse deeper before walking.
> (Optionally a second "gain" rational can be specified, used for the
> special case where the unallocated part of some value is known to be
> a square.)
>
> I wish to write a perl program that would efficiently determine an
> optimal or near-optimal selection of settings of the strategy,
> force-all and gain for a given set of parameters (n, k, v_max), and
> I would like help doing that.
>
> Some difficulties I foresee:
> - The options have non-linear effects. A bad selection may run 10^9
>   times slower than the optimal selection.
> - Different batches behave very differently from each other. If we
>   know which batches are slow it is probably sufficient to optimize
>   for those batches, but it is not safe to select only some batches
>   to test without that knowledge.
> - The time taken is not simply proportional to v_max: since the walk
>   stage involves factorization, larger values will tend to be slower
>   to test than smaller values. Additionally, some batches will not
>   show up at all with a small v_max, since they can immediately be
>   ruled out.

The brief was tailored to a guess at what the model of the time could
do. It was intended as a stepping stone towards an ultimate goal of:

- getting calibration fast enough to perform it separately for each
  batch;
- getting it fast and accurate enough to calculate it dynamically
  within pcoul itself, possibly even at finer granularity than the
  batch.

### Aims

Most of pcoul's CPU time goes on runs that prove an upper bound is
minimal: zmax is fixed (as if with -X), and no candidate is expected to
lower it mid-run. Everything here is costed at the requested zmax.

- End goal: a runtime optimiser. At each node pcoul chooses walk or
  recurse, which position to allocate next (best_v()) and whether and
  how far to pre-walk large primes (-W), by estimated cost, instead of
  by fixed options (-g, -j, -W) tuned by hand.
- Further off: a batch harness that runs batches separately with
  per-batch settings. Requirements, kept from the earlier design: a
  persistent per-batch ledger (batch, bound confirmed, settings, time,
  status); one authoritative current bound, propagated to every new
  dispatch (a batch confirmed against a larger bound stays confirmed);
  an independent audit tool that proves an aggregated run complete,
  distinguishing not-attempted from timed-out batches; dispatch order
  by cost, or by an externally supplied likelihood when given.

### Instrumentation

A VERBOSE=1 build has it all, chosen at runtime by -dv<bits>
(trace.h): 1 the trace, 2 the records, 4 stage timing, 8 the -ja2
choices, 16 the test preparations (T and U records), 32 the run's
counts and CPU time (an N record).

- -dv2: one record per gate decision, recursion subtree, walk,
  walk_1_set(), flip and midp phase (trace.c). With -dv6 its clock
  reads inflate walks (~10% on D(48,10)); use it for structure and
  ratios, not absolute walk times.
- $MULTIBENCH: the benches behind the cost table (bench.c, see
  multibench-table).

### The cost table (bench.c, multibench-table, coulcost.c)

One table per machine and MPUGMP build, serving every n (`-f<flake>`
for runs using -o), timed by work_clock(): cycles at the -Lc reference
clock (3.6GHz) where pcoul can open the cycle counter, so independent
of the turbo clock while it is made, else CPU seconds; each section's
V line records which (CY3.6 or CPU, none meaning CPU), and -dT warns
of a section in a different unit from the run's. Rows: C
(per-operation constants fitted from -dv6 runs and paired mock runs),
S/L (trial division by size and prime), P/R (prime tests),
test_multi() rows by size for each class of (t, e) (cm_tclass(): after
trial division, tau_multi_prep() depends on t and e only through t vs
e + 1 and their parities; older tables have a row per divisor of their
n, used where exact, else by class), G (the ladder per rung: reach,
cost, hit rate, factor size, cofactor primality), Q (QS alone by
size). Sizes sit either side of the limb boundaries at 64 and 128
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
tail and situ. pcoul builds in a default table from the file timings,
used unless $COST_TABLE names another; `-dT` notes sections from a
different build.

### The mock pcoul (mock.c, MOCK=1)

Runs the search with the costly parts replaced by their modelled cost,
from the machine's cost table. The 367 line reports real time outside
the mocks plus modelled time; the 368 line is the modelled part alone,
with what was stubbed.

- walk_v(): linear walks and walks of one fixed power (nqc < 2) are
  costed, not run: per iteration the loop, plus the inverse-filter
  pass rate (exact from inv[]; over root residues for fixed powers)
  times the tests. Tests model trial division from the exact or
  modelled valuations of each position's value (honouring the inverse
  filter's exclusions), primality tests stage by stage as
  test_primes() runs them, and the factoring ladder rung by rung as
  tau_multi_run() interleaves its pending values. The root of a fixed
  power is costed as the walk tests it: trial division at once, and if
  that does not settle it, the ladder with the other values once the
  primes have passed. Pell walks (nqc >= 2) run for real.
- walk_1_set(): the first 10000 primes run for real with modelled
  tests (every 8th exactly), the rest charged at their rates.
- next_unforced(): an innermost loop whose first child walks is
  charged in closed form (cprime plus walks scaling as
  (p0/p)^(x-1)); loops of fixed-power walks, and loops above the
  leaves, are sampled (above 65536: 8 children of every 128 run and
  timed, the rest charged their mean); the tail of a loop where nearly
  every prime fails on rq > zmax is charged ctail per prime.
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

With leaf loops real ($MOCK_LEAF_OFF) the 397^2 subtree is 1.00-1.02:
the walk, test and ladder models are right there, and the rest is in
the leaf stubs (~5%) and striding (~3%). Mock runs vary ~4% run to run
(stride samples), as do real ones.

### -ja1 (runtime cost gate, coulplan.c)

At a node with no fixed square, walk or recurse is decided by
estimated cost instead of gain: walking costs a setup plus Z/aq
iterations at a cost per iteration learnt per level during the run;
recursing costs GR_APPLY per prime tried (0.2us then, 0.12us since
primes are rejected in single limbs) plus the children's walks, as if
every child walks. On every non-square batch tried (8
D(96,8), 3 of them at 10x zmax, and 5 D(48,10)) it matched or beat the
best gain tried within a few %, with no tuning; the user's -g24 on
D(96,8) was 20-35% slower than both. Recovery honours the recursion the
recovery line shows, without asking the gate again, so -ja1 can be
turned on or off mid-run; tested by recovering D(12,4) and D(24,5) from
100 random log points, and in t/t10init.

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

### Costs counted, not timed

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
(capply); a -dv32 N record per run allows a regression of the run's
CPU time on all the counts, but over 30 runs it barely improves on
that (0.79-1.13) and the constants are poorly determined, so it is
left as a check. With counted costs D(64,3) -j4 -x1e15 took 7.9s,
then 29s as the pricing improved, then 5.2s: its choices at the root
are made before any learning, so they turned on small differences in
the estimates, until the learnt ratio for recursing was given a prior
of 1/4 (0.1s).

### -ja2 (choosing positions by cost)

At a node with no fixed square, walking it costs W whichever position
is chosen, and recursing over some x then walking is never better, so
the choice is between walking and recursing over every x of some
position (ja_choose()): W and the strategy's choice are incumbents, and
other positions are costed (classify_x() and the -ja1 estimate) until they
pass the incumbent; positions alike in (t, q, last p, x, first prime
tried) cost the same. A loop is costed from the first prime it will
try (cost_start()): known primes, such as a forced prime already
placed, are skipped by the loop at no cost, so the estimates skip them
too. An x leaving a square is costed as if it did not (an
overestimate, corrected by learning, below), and likewise an x leaving
t = 2z (z a can_flip() value) whose children may flip, learnt apart;
where a position would flip at once, the model cannot cost it, and if
it is the strategy's choice that choice stands. On four
D(96,8) batches at the usual zmax, -ja2 matched the best of -j0..-j2
under -ja1 on each (whichever it falls back on), beat all of them on
one by 20%, and took 26-45% less time than -j4 -g24. There, 99% of its
choices walk the node, and under 1% choose another position. On
D(48,10) batches 1-12 at -x22911293821947932 -j2 -f7 -g30 it took
25-60% less time than -ja1 on every batch that took measurable time,
and on runs with many squares 45-50% less (D(36,5) -j2 -x1e12: 85s
against 169s; D(60,4) -j0 -x1e15: 2.2s against 4.2s).

Choosing has a cost of its own, about 1us for each position weighed
(limit_p()'s integer root and the sum over primes, for each x), which
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

### What -ja learns

-ja2 learns from its choices: each choice made by cost is costed (at
first by thread CPU time, now by what it did, see above), a walk whole
and a position by each of its x, and per level the actual cost against
the estimate, in four parts (walking, recursing, recursing into a
square, walk_1_set()), gives a ratio by which later estimates of each
part are corrected (starting from 1ms of evidence at ratio 1). Each x is
of a single part, so the attribution is exact: splitting a whole
subtree's cost between its parts in proportion to their estimates
contaminated the ratios (walk_1_set() at 40-65x), and once squares were
costed, sent D(60,4) -j4 -x1e15 from 2.1s to 190s. On D(36,5) -j4 -x1e10
the ratios found were 0.00-0.01 for recursing at level 2, 0.1 at 3, 0.4
at 4 and about 1 at 5 (the depth-1 estimate assumes every child walks),
about 2 for walk_1_set() (now charged 2us per prime reaching its tests,
as measured, not 1us), and 1.2-1.5 for walking. Without that, -ja2 -j4
on D(36,5) chose vast walk_1_set() ranges: -x3e10 took 87s against 14.5s
under -ja1, -x1e11 over 300s against 44s; learning, 5.5s and 15s.
Elsewhere learning changed nothing beyond noise. Costing positions that
leave a square helps where the strategy is poor: D(60,4) -j2 -x3e14 took
3.6s against 133s (-j0 takes 1.6s), and on the other runs tried it
changed nothing beyond noise. The square ratios learnt are small (1e-5
at level 2, 0.01 at level 4, 0.6 at level 5).

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
(D(24,5) -j0 -x1e13: 0.19s against 0.15s), and at one just below it to
the cost of choosing (-x15537947: 0.11s against 0.09s). On the D(96,8)
batches at -x393643805345636319 -f5 (b5, b50, b5000, b350000), -ja2
took 10.3-10.7, 30-31.7, 4.3-4.5 and 12.6-13.5s with -j0 or -j2, about
10% less than before learning and up to 25% less than -ja1; with -j4 it
was 3% slower than -ja1 on b50, faster on the rest.

The ratio for recursing was at first learnt per level, like the rest,
but nodes of one level differ far more than nodes of one size. From
175k records of estimate against actual cost on D(96,4) -j4 -x1e16,
actual/estimated falls smoothly with the size of the node: 0.6 for
nodes that would cost 0.1-1ms to walk, 0.06 at 0.1-1s, 0.004 at 1000s.
The ratios per level, each dominated by the largest nodes of its level,
were 0.000 at levels 2-4, 0.57 at level 5 and 0.016 at level 6, so that
at level 5 it walked what -ja1 recursed (20.7M walk iterations against
8.7M, 17.6s against 12.5s). Correcting each record by its level's ratio
left a cost-weighted error of 3.1 decades there and 0.15-2.3 on eight
other runs; by decade of size 0.33, and 2-8x less than by level on
every one. So the two recursing parts are now learnt in bands of the
node's estimated cost to walk, a factor of 8 each (ja_rsize()), a band
with no evidence starting from 0.4 of the ratio in use for the band
below (0.25 and 0.6 do the same within 3%). Over the same 42 runs that
was never slower beyond noise and 4% less time in all: D(96,4) -j4
-x1e16 17.6s to 11.9s, D(48,4) -j4 -x1e15 0.38s to 0.28s, D(96,3) -j4
-x1e15 0.77s to 0.64s, D(60,4) -j0 -x1e15 2.04s to 1.77s, D(96,8) b50
-j4 36.0s to 33.4s. Keying by the position's own estimate instead fits
the records as well, but chooses worse (D(60,4) -j0 -x1e15: 9.5s): it
shrinks large estimates more than small ones, so distorts the
comparison between positions at a node, where a ratio shared by the
node cancels.

#### Two costs the counts exposed

Broken into components, the counted cost of -ja2 -j4 runs was about
half in the recursion loops' primes on the production-like batches
(D(96,8) b5, b50, b350000 and D(48,10) b7: 46-50%, with 43-51% in
tests and 2-7% in walk loops), where 200-360 primes are tried for each
one that applies; D(60,4) -x1e16 58%, D(12,8) 42%, D(96,4) 26%.

That led to reject_single(), which rejects most of a loop's primes in
single limbs, and then to bpsw_u64(), which tests the primality of a
single limb in single limbs. Both went to master ahead of this work,
with their measurements there in their commit messages. Under -ja2 the
42 runs of the benchmark set took 12% less time with the first and 19%
less with both, and the production-like batches more: D(96,8) b5 11.3s
to 8.8s to 6.5s, b50 33.7s to 26.5s to 19.3s. Under -ja1 the benchmark
set took 24% less with the first and 35% less with both. Runs whose
values are small or whose time is in walk loops gain little (D(96,4),
D(192,3), D(48,4): within 5% either way).

reject_single() needs the CRT multiple mod p^{x-1}, in a limb below
2^61; where that did not fit (p^10 for n = 44 above p = 68) any prime
not rejected mod p went to apply_single() and was rejected there at
about 2550 cycles against 200-350 (2026-10-25). On D(44,7) -x1e42
-ja2 that was 10.8M primes, 13s of 15s CPU, counted at the single-limb
rate so that the run counted 3.6s. Testing mod the largest power that
fits instead rejects nearly all of them (577k left; 14.7s to 3.4s, a
patch for master); and the primes that still fail there are counted
apart and priced at cfail (C row, 1.1us until multibench-table fits
it), and -ja's estimate of a loop expects them (gr_nfail()).

With the first, cprime and ctail were measured again (0.22us to
0.14us, 0.23us to 0.12us), and the gate's cost per prime lowered to
match (GR_APPLY, 0.2us to 0.12us). A table made before that has cprime
and ctail too high: rebuild its leaf and tail sections.

Values of more than a limb still go to MPU::GMP, and there the cost of
a preparation steps up sharply (about 20us for a 65-70 bit value that
reaches the primality test), so the K rows price the bits tested apart
(preppbit for a single limb, prepzbit beyond). The calibration run
that was to supply such values gave only 19 records in its minute, so
the situ section now takes them from the D(162,3) batch and from
D(36,5) -x1e22. And tau_prime_run()'s own tests, which the K rows had
left uncharged, are now charged as tau_multi_prep()'s are.

#### Where -ja2 pays

Each run under -ja1 and -ja2 at four strategies (seconds, 120s
allowed; the D(48,10) batches at -x22911293821947932 -f7 -g30, the
D(96,8) batches at -x393643805345636319 -f5), with primes rejected
early and primality tested in single limbs:

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

### Recovery under -ja

315 lines mark only levels chosen against the strategy, the rest
replayed by it.

### Findings under a fixed gain (to 2026-09-25)

These predate -ja. They were measured with the gain set by hand and
CHECK_OVERFLOW on (now the default), from the gate's records (-dv2), on
D(48,10) -x22911293821947932 -j2 and nqc == 0 walks unless stated, with
two complete units that take 27-50s:

- I: `-I"3^2 2^5 . 2.3.5 7^2 2^2 3 2 5^2 2^3.3^2"`
- J: `-I"2^5.3^3 5^2.7 2 3 2^2 . 2.3.5 . 2^3.7 3^2"` (b0's forced part
  under `-f7`)

The unit costs have fallen since (chinese_ppow(), primes rejected in
single limbs, primality in one limb), so the figures are for their
ratios and for the structure, which stand.

#### Recursion cost: c_prime

For each recurse decision, subtree time minus nested recurse subtrees
and walks, divided by primes tried at that level: ~0.56-0.58us per
prime, the same at levels 5-8 in both patterns (R^2 ~0.996 for a
linear fit per level). Covers prime iteration, `apply_single()`
(including the overflow rejection), and for surviving allocations the
next level's `best_v()`/`prep_unforced_x()`/`limit_p()`/gate.

#### Walk cost: c_walk

Per ati inside non-empty `walk_v()` calls, decomposed by direct timing:

    c_walk ~ 30ns + P_inv * C_p + P_inv * P_prime * C_m

- P_inv (inverse-filter pass rate): exact at walk setup from `inv[]`:
  product over distinct moduli m of (1 - distinct excluded residues/m).
  Naive products over positions are wrong (e.g. 3 allocated at several
  positions constrains a single residue class).
- P_prime (all `test_primes()` positions prime): product over
  need_prime residuals of b bits of K/(b ln 2), K ~ 4.8 (4.375 from
  coprimality to 2,3,5,7, the rest presumably larger allocated primes);
  K held at 4.5-5.2 across both patterns, 1-3 positions, 20-43 bits.
- C_p ~ 0.83-1.15us per `test_primes()` call (lower when several
  positions let the cheap pretest fail early); C_m ~ 15-16us per
  `test_multi()` call.

| | J | I |
|---|---|---|
| P_inv actual/predicted | 0.3709/0.3709 | 0.2185/0.2185 |
| P_inv*P_prime actual/predicted | 0.00873/0.00942 | 0.0454/0.0447 |
| c_walk actual/model (us/ati) | 0.476/0.547 | 0.976/0.942 |

The number and size of need_prime positions dominate: each extra one
cuts `test_multi()` traffic ~5x (J averages 2.3, I has 1).

#### Gate: predicted vs measured optimal gain

Treating a decision as a leaf (children's walks negligible for x=3),
walk ~ c_walk * (zmax - zmin)/aq, recurse ~ c_prime * (cap - p)/ln(cap),
so break-even gain ~ ln(cap) * c_walk / c_prime.

| | predicted | measured optimum (flat region) |
|---|---|---|
| I (c_walk ~0.85) | ~20 | 20 (15-30) |
| J (c_walk ~0.40, 0.27-0.47 by level) | ~10 (7-13 by level) | 10 (7-14) |

Sweeps: I: g5 31.7s, g10 27.3, g15 26.8, g20 26.1/26.4, g30 26.6/27.4,
g40 28.3, g60 31.0, g120 39.5. J: g3 53.8, g5 47.6, g7 45.8/45.5, g10
44.5/45.1, g14 45.5, g20 47.9, g30 52.0. The minima are flat (within
~30% of the optimum costs a few %), so a dynamic gate would need only
a rough per-allocation c_walk.

#### -W (midp)

`-W<w>` runs `walk_midp()` once per batch: each allocation p^(x-1) with
p > w at each position is applied on its own at the batch level and
walked immediately; the recursion then runs with every cap limited to
w. The saving is not mainly from cutting loops short: with the large
primes gone, `cap - p` shrinks, so the gate *recurses* at nodes that
used to walk large ranges, into much more constrained and cheaper walks.
The cost is the midp phase: its walks total ~X/(w ln w) ati for x=3
(X = (zmax - zmin)/aq at the batch; checked to 2%), at a higher c_walk
than recursion walks since few positions are need_prime yet, plus
~c_prime * pi(L) for trying every p up to each position's limit L,
whatever w is.

Measured (s), CHECK_OVERFLOW on:

| batch | no -W | best -W | optimum w |
|---|---|---|---|
| D(48,10) I, g20 | 26.1 | 5.9 | 1e4-3e4 |
| D(48,10) J (= b0 under -f7), g10 | 44.5 | 6.4 | 2e4 |
| D(96,8) b1 (`-I"2^5.3^3.5 7^5 2 3 2^2 5 2.3 ."`), g20 | 8.37 | 1.74 | 1e4 |
| D(24,12) b1 (`-I"2^5.5 3^2 2.7^5 . 2^2.3 5 2 3 2^3 7 2.3^2.5 ."`), g20 | 104.7 | 25.7 | 1e4 |

With w near its optimum, gain matters much less (J: g3-g30 within
~25%). Too low a w is costly (I: 37.7s at w=1e3), and where there is
little recursion to save -W only adds cost (f(60,3): 0.04s -> 6.6s at
-W1000).

#### Single square (nqc == 1)

Measured on D(18,4) at reduced `-x` (1e15-1e17):

- A square walk iterates roots r up to (zmax/q)^(1/g) through rc
  residue classes mod qq: ~rc * root / qq iterations. Per iteration:
  `c_sq ~ 0.15us + P_inv * 0.63us + P_inv * P_sq * 11.8us` (loop, square
  position's own test, `test_zmulti()`), reproducing 2.23us/iteration;
  the loop is 5x the linear walk's (mpz arithmetic). P_inv is again
  exact from `inv[]` (0.5536 vs 0.5537). When the square's tau is 3
  the root must be prime: P_sq fits K/(b ln 2) with K ~ 4.0. Walks are
  small but numerous, so setup (~2.7us per walk) matters.
- Allocating p^(x-1) elsewhere turns the square's r into 2r/p^(x-1)
  (two square roots) for about half of p, and prunes the rest; checked
  exactly on logged children. Recursion costs ~4.2us per prime tried,
  7x the nqc == 0 figure, presumably mostly square residue upkeep.
- Unit costs carry over to the full range (2.24us/iteration at 29.6-bit
  roots vs 2.23 at 22 bits), but structure does not: at full range the
  first allocations' caps grow as zmax^(1/4) against r_walk's
  zmax^(1/2), so recursion goes a level deeper, while the final
  allocation at a position (t=6 -> 2) has cap ~ zmax^(1/2) and always
  walks - giving a few enormous walks (7.3M iterations, 16s) instead of
  hundreds of thousands of small ones. So reduced-`-x` runs are sound
  for unit costs but not for structure.
- `-W` is ruinous here (26s -> >90s at -x1e17): positions needing two
  x=3 allocations (odd part 9) have a batch-level midp limit necessarily
  far looser than the recursion's first-allocation cap, and midp has no
  gate. Master's skip of odd-prime-tau positions in `prep_midp()` cut
  the first batch's midp work 7.3M -> 3.0M tries but does not fix this.
- The square gate estimates the walk from the root of the width
  (zmax - zmin); the walk itself starts at the root of zmin, so narrow
  windows overstate square walks and push the gate towards recursion.

#### Fixed powers across the n groups

`pcoul -a` flags batches with a fixed power as `[sq=<count>]`. At each
tuple's current upper bound: every batch for n == 6 (mod 12), 3-20% of
batches for n == 0 and 4/8 (mod 12), none for D(128,7); forcing alone
never fixes two (so no Pell batches). Root degrees g = gcd(p - 1) over
primes p | t: 2 (t = 3, 9, 15, 27, 45, 55), 4 (t = 5, 25: D(30,4),
D(90,4), D(60,6), D(100,5), D(200,5)), 6 (t = 7: D(224,6)), 10
(t = 11: D(220,4)). Fixed-power batches in n == 0 (mod 12) carry heavily
constrained forced primes and are usually trivial.

r^g takes few values mod small p, so some fixed-power batches are
impossible modulo a small forced prime yet are searched in full (see
TODO-coul); for the same reason the inverse-filter pass rate of a
fixed-power walk must be computed over root residues, not by assuming
uniform ati: `gs_square_pinv()` does this, and is exact in every case
checked (e.g. D(100,5) b33: 0 vs 0.23 from the uniform formula).

#### n = 50, 100 and -j2

Complete runs: D(50,3) -j0/-j1 3.4-3.6s vs -j2 4.9s; D(100,3) -j2 27.9s
vs -j0/-j1 33.8-34.2s; D(100,4) -x1e19 -j2 62.0s vs -j0 63.6s; D(100,5)
-x1e17 -j2 11.2s vs -j0 3.05s. In D(100,5) at that range, -j2's walks
test 6.5x more candidates: it first allocates at low-tau positions
(t = 10, 20), where one p^4 leaves a prime or small tau, with large
caps and many primes tried, leaving the high-tau positions to be walked
at larger ranges. Whether -j2 wins at the full range (X ~ 5e35, where
the flip also matters more) is not yet known.

#### Candidates

Calibration assumes no candidate lowers zmax during the run; if one does
substantially, the calibrated options may no longer be optimal.

### Methodology lessons

- LARGE_MIN (on by default in the Makefile) makes the gate use
  zmax - zmin, so narrow -x windows walk where the full range would
  recurse. Build without it to make a narrow window just below zmax
  reproduce the full run's gate decisions and recursion, walking only
  the window (walk counts then scale by the window's fraction of the
  range, or 1 - (zmin/zmax)^(1/g) for fixed powers). Without
  LARGE_MIN, a walk's starting ati beyond 2^64 goes unchecked.
- Time with nothing else running: two vCPUs slow each other 10-15%.
  Real runs of the same batch vary ~4%.
- For fine timing inside pcoul use work_clock() (coul.c; ct_clock in
  coultau.c): in the unit of reported times, cycles where the counter
  is open, else CLOCK_THREAD_CPUTIME_ID, since once the diag and log
  timers are armed, the process CPU clock advances only at scheduler
  ticks.
- Progress after a fixed CPU time (-Ld) is noisy on a VM (25-50% run
  to run): compare complete units. A fully specified -I pattern is one
  batch.
- Read the mock's 367 line, not the 368 line.
- Build without PORTABLE (it is for distribution binaries).
- Per-node comparisons across runs need the node set to be the same:
  pair by order only at levels whose parents decide identically.
- Profile the mock's own overhead like anything else: most of its time
  once went on building the trial model's cache key (12.4s to 4.0s on
  D(96,8) b220367 once that was fixed).

### Tried and dropped

- MOCK_LADDER (coulmock.c): a per-residual chain model of the ladder
  from Dickman's rho; superseded by the measured G rows.
- For -ja1: fixed-square nodes with the same estimate (lost 12-40%), a
  per-level correction learnt from timed recursions (wrong shape: the
  big recursions set it, the marginal ones suffer), and a two-level
  estimate (no gain over one level).
- WALK_FROM (once a child of a loop walks, later children walk
  without the gate) as a speedup: the gate costs ~1us, so skipping it
  gains nothing measurable. Its check mode found the gate monotone
  within a loop apart from flips.
- Never walking a loop whose children can flip (t = 2q^2): D(60,3) -j2
  -x1e13 7x slower under -ja1, D(36,5) -j0 -x3e10 3x slower under
  either, D(36,4) -j4 1.7-3x; only D(64,3) -j4 gained, by 1.5%.
- Learning from timed costs: choices then depend on the machine's load
  and on rare costly factorizations, and identical runs differ. D(60,4)
  -j2 -x5e14 took 4.6s in most runs but 100s in about 1 in 7. Hence
  costs counted.
- In the leaf mock, stubbing rejected primes one by one: once
  update_chinese() used chinese_ppow() a real reject cost only about
  0.045us more than the mock's own test of it. The stubbed ends of
  loops of rejects still halve the mock's time, and are kept.
- rungbench, a standalone bench of single rungs of the ladder: its pq
  mode built n = p*q, so multiplicity was 1 by construction and said
  nothing of real inputs. The ladder bench in bench.c replaced it.
