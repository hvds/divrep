# walk/recurse gate cost model - status, 2026-09-25 (updated)

Companion to `walk-cost-model-status.md` (which covers the factoring
ladder). This covers the gate in `prep_unforced_x()`, which walks
`prev_level` when `gain * (zmax - zmin) / aq < cap - p` and otherwise
recurses over primes p..cap at the current level.

All numbers below are from `D(48,10) -x22911293821947932 -j2` on one
machine, nqc == 0 walks only, built with `GATE_STATS=1` (commit above)
and, unless stated, `CHECK_OVERFLOW=1`.

## Methodology lessons

- Narrow `-x` windows are useless for the gate: `r_walk` scales with
  the window width while `cap` (from `limit_p()`) depends only on zmax,
  so narrow windows always walk. Fine for measuring per-ati walk cost.
- Progress-after-fixed-CPU (`-Ld`) comparisons are noisy on a VM
  (25-50% run to run). Use complete units instead: a fully specified
  `-I` pattern is one batch; the two used here finish in 27-50s:
  - I: `-I"3^2 2^5 . 2.3.5 7^2 2^2 3 2 5^2 2^3.3^2"`
  - J: `-I"2^5.3^3 5^2.7 2 3 2^2 . 2.3.5 . 2^3.7 3^2"` (b0's forced
    part under `-f7`)
  Repeat runs of these agree within ~0.5-1s.

## CHECK_OVERFLOW

Now on by default in master. Without it, 99.7% of `walk_v()` calls in
the `-g30` D(48,10) regime exited immediately on rq > zmax, after
~1.8us per allocation spent in `best_v()`/`prep_unforced_x()`/
`limit_p()`; with it, pattern I at g30 goes 34.4s -> 27.4s. Everything
below assumes it is on.

## Recursion cost: c_prime

For each recurse decision, subtree time minus nested recurse subtrees
and walks, divided by primes tried at that level: ~0.56-0.58us per
prime, the same at levels 5-8 in both patterns (R^2 ~0.996 for a
linear fit per level). Covers prime iteration, `apply_single()`
(including the overflow rejection), and for surviving allocations the
next level's `best_v()`/`prep_unforced_x()`/`limit_p()`/gate.

## Walk cost: c_walk

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

## Gate: predicted vs measured optimal gain

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

## -W (midp)

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

Note that `-b<id>` still enumerates every later batch without
processing it (~6s for D(96,8)): use the batch's pattern with `-I` for
timing single batches.

`batch-estimate` implements the idealised recursion (walk if
gain * r < cap, else try pi(cap) primes and recurse into r/p^(x-1))
plus the midp phase from a log's B/BP records, with no per-tuple
fitting:

| batch | measured vs predicted |
|---|---|
| D(48,10) I | within ~5-15%, optimum right |
| D(48,10) J | 10-15% high, optimum right |
| D(96,8) b1 | 20-25% low, optimum right |
| D(24,12) b1 | 3-13% low, optimum right |

It also reproduces the no-`-W` gain sweeps above (I within ~10% at all
gains; J up to 25% high at low gain, from C_p). In C it would cost well
under 1ms per w evaluated, so choosing w (and gain) per batch looks
feasible.

## Single square (nqc == 1)

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

## Fixed powers across the n groups

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

## batch-estimate, generalised

`batch-estimate` now follows the search closely enough to reproduce
its structure (per-depth counts of recurse loops, primes tried, walks
and walk sizes match the GATE_STATS records to within a few percent):

- position choice by strategy 0/1/2 rules (and STRATEGY_6X when its
  conditions hold); at a position only divisors x sharing t's highest
  prime are tried (`highdiv`), smallest first, with `prep_unforced_x()`'s
  loop start and skip rules (continue after the previous prime for a
  repeated x; primes fixed by the batch are tried but rejected);
- limits as `limit_p()`: the x == nextt prime case, the STRATEGY_6X
  bound, restricted mintau (from BR records), else mintau (BM);
- a fixed power's walk is in root iterations, rc * root / qq; an
  allocation elsewhere multiplies it by (number of g-th roots)/p^(x-1),
  exact for p < 1000 (0 or gcd(g, p-1)) and 1 on average beyond; one at
  the fixed power shrinks its root by p^((x-1)/g); a second fixed power
  is the Pell case (nearly free);
- `recurse()` stops a loop when the same-x continuation becomes empty
  (t = 2z^2) and hands the rest to `run_flip_pqsq()`, costed from its
  outer primes and the primes its `walk_1_set()` calls iterate;
- walk cost updates the inverse pass rate by (1 - 1/p) per allocation,
  and `test_multi()` cost as ~11us + 0.5us per need_other position;
  fixed-power walks: ~0.16us loop per iteration, the root test (passes
  ~4.0/(b ln 2) when the root must be prime), ~2.5us setup per walk;
  recursion ~4.3us per prime tried with a fixed power present.

Measured vs predicted total, default strategies, no retuning between
tuples (GATE_STATS builds):

| run | measured | predicted |
|---|---|---|
| D(18,4) -x1e18 | 70.7 | 80.5 |
| D(18,4) full range, b3 alone | 104 | 109 |
| D(18,4) -x1e17 -W100000 (b1/b3/b4) | 87.9/19.8/86.7 | 62.3/34.3/55.7 |
| D(30,4) -x1e24 | 19.6 | 27.2 |
| D(54,4) -x1e16 | 6.0 | 10.6 |
| D(90,4) -x1e20 (incl. 6X and flips) | 12.4 | 16.1 |
| D(48,10) I, g20, no -W / -W30000 | 26.1 / 5.9 | 29.8 / 7.2 |

Per batch, larger batches are mostly within 1.1-1.8x, consistently
high; run-to-run noise on the VM was up to ~20% for the same batch.
The structure shift with range for n == 6 (mod 12) - recursion going
a level deeper at full range, leaving a few very large walks - comes
out of the gate logic and scaling laws unchanged (full-range b3 above).
-W is correctly predicted to be ruinous for D(18,4) at every W.

Further details now modelled:
- run_flip_pqsq()'s outer allocation p^(2z-1) usually leaves an odd
  tau, making v_i a further fixed power that apply_allocv() rejects
  about half the time; with that, its accepted outer primes (230 vs
  191) and inner walk_1_set() primes (2.5M vs 1.7M) come close;
- when the fixed power's tau is not prime its root goes through the
  multi prep, whose cost grows with root size (0.43us at 19 bits to
  6.6us at 39 bits) and whose pass rate depends on the shape required
  (~0.4 for t = 9, 27; ~0.125 for t = 15);
- for bucketed primes only a fraction mean(1/gcd(g, p-1)) of children
  leave the fixed power roots; a fixed-power walk expected to cover
  under one root iteration usually never happens (overflow rejection),
  so its setup is scaled accordingly.

## Open

- C_p refinement (pretest cost + P(reach BPSW) * BPSW cost); C_m as a
  function of need_other count and sizes.
- Only x=3 decisions, one n/k, one machine, nqc == 0; top-level
  decisions whose children recurse need the full recursive estimate.
- A dynamic gate would need P_inv/P_prime before walk setup has run;
  worth it only for decisions that are not clear-cut.
- batch-estimate: fixed powers arising below the batch level (only
  the Pell case is handled); midp (-W) with fixed powers; strategies
  3 and 4; g >= 4 walks validated only for pass rates, not timing;
  multi-prep pass rates for fixed-power tau shapes other than 9, 15,
  27; the remaining ~1.1-1.8x overestimate (worst D(54,4)); g >= 4
  batches in these tuples were too small to test timing.
- Other n groups; fixed higher powers than squares.
