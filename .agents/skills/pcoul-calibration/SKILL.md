---
name: pcoul-calibration
description: How pcoul costs its own work - the cost table and the mocks - with what was measured and what was tried and dropped
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
(trace.h): 1 the trace, 2 the records, 4 stage timing.

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
leaf, tail), each stamped with the build that made it ("V section
sha"): `-s<sections>` rebuilds only some, and `-u<table>` takes the
rest from an existing table, so a new MPUGMP needs only scan, prime,
ladder and qs (and multi), a change to coul.c only walk, w1s, leaf
and tail. pcoul builds in a default table from the file timings,
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

### Findings under a fixed gain (to 2026-09-25)

These were measured with the gain set by hand, from the gate's records
(-dv2), on D(48,10) -x22911293821947932 -j2 and nqc == 0 walks unless
stated, with two complete units that take 27-50s:

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
- In the leaf mock, stubbing rejected primes one by one: once
  update_chinese() used chinese_ppow() a real reject cost only about
  0.045us more than the mock's own test of it. The stubbed ends of
  loops of rejects still halve the mock's time, and are kept.
- rungbench, a standalone bench of single rungs of the ladder: its pq
  mode built n = p*q, so multiplicity was 1 by construction and said
  nothing of real inputs. The ladder bench in bench.c replaced it.
