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

## Open

- C_p refinement (pretest cost + P(reach BPSW) * BPSW cost); C_m as a
  function of need_other count and sizes.
- Only x=3 decisions, one n/k, one machine, nqc == 0; top-level
  decisions whose children recurse need the full recursive estimate.
- A dynamic gate would need P_inv/P_prime before walk setup has run;
  worth it only for decisions that are not clear-cut.
- batch-estimate: odd part > 3 (positions needing several
  allocations, whose limits change after each), square positions,
  allocation order taken from `best_v()` rather than inferred.
- Other n groups; fixed higher powers than squares.
