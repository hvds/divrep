# sqdiff: a square whose partner factors (STRATEGY_6X generalised)

Design for implementation. Written against master at d69696c
(2026-11-22), with mt (pctul stages 3 to 5, unreviewed) and
calibrate-mt read alongside. Function and option names are as found
on master; line numbers are deliberately not given. This document
stands alone, and is meant to be discarded once implemented.

Status: draft 4, 2026-11-22, after hv's review of the whole; his
decisions are recorded where they apply, marked "Decided", and none is
left open. Items marked **[verify]** are my reading of the code and must
be checked before being relied on.

What stands behind this document:

- The identity of section 2 was checked numerically for 23 pairs
  across TYPE_o and TYPE_t, including STRATEGY_6X's own.
- The enumeration of section 6 was prototyped in Python and checked
  against brute force over Y for 480 (pair, multiplier) cases, 191 of
  them with solutions, with no miss (section 10.1).
- The f(198, 12) figures of section 1 come from runs of calibrate-mt
  pctul (with the fixes of 2026-11-20) and a throwaway C search.


## 0. Before starting

Read, in this order:

1. `CLAUDE.md` (the standard: a run is a proof).
2. `.agents/skills/divrep-conventions/SKILL.md`.
3. `.agents/skills/pcoul-internals/SKILL.md`.
4. In coul.c: `apply_secondary()`, `best_6x()`, `walk_6x()`,
   `limit_p()`'s STRATEGY_6X branch, `loop_limit()`, `diag_6x()`,
   `suffix_6x()` and `parse_6x()`, `prep_maxforce()`, and the CH_6X
   and IS_6X cases of the main loop.

Stages 1 and 2 are done from master. Stage 3 is on calibrate only.
Stage 4 is optional, and not designed here.

Decided (hv): the name changes from "6X" to "sqdiff" throughout
(section 9.1).


## 1. The problem

STRATEGY_6X (pcoul only) exploits one identity. If v_i = 2z^2 then

    v_{i-2} = v_i - 2 = 2(z - 1)(z + 1)

so v_{i-2} splits into two factors that differ by 2. Once v_{i-2} has
tau 2 left, the rest of it is one prime p in one factor, and the
allocations already made there say what the other factor is: the
candidates are finite, and `walk_6x()` lists them. Before that, any
prime power allocated at v_{i-2} lies wholly in one factor, so it is
at most about the root of v_{i-2}, and the loop of q^2 there runs to
about the 4th root of zmax rather than the root.

The detection is hard-wired to that one case: p = 2, x = 2 at v_i,
i >= 2, n == 2 (mod 4) (`apply_secondary()`), partner i - 2. The
identity is one case of a general one (section 2), which applies to
every type, with other partners and other square parts.

The case that prompted this is pctul f(198, 12). All four of its
batches fix v_9 = 198 + 10d = 8r^2, and

    10.v_10 = 22(2r - 3)(2r + 3)

In b3 (11^1 at v_10, tau 6 left) one of 2r +/- 3, less its 5, is a
prime square s^2, so d grows as s^4; in b0 and b2 (tau 2 left at
v_10) the candidates are finite. pctul took 3977s for b3 to 1e30
under -ja2 -ka; a throwaway search over s covers it to d ~ 2e43 in
about 30 minutes.

A scan of `pctul -a` for n <= 250, k <= 14 found 25 (n, k) with
one-square batches where some later position factors this way. In
many of them, the batches that would gain (section 3) carry a large
share of -ka's estimate: f(160, 8) ~88%, f(150, 7) and f(150, 8)
~70%, f(198, 12) ~70%, f(200, 10) ~65%, f(96, 8) ~30%.

For TYPE_o the general rule also covers pairs pcoul does not use today
(section 2.3).


## 2. The identity

### 2.1 General form

With a_i = TYPE_MULT(i), c_i = TYPE_OFFSET(i), coul.h's TYPE_RES()
gives, for every d,

    a_s.v_j - a_j.v_s = TYPE_RES(s, j)

Let v_s be the node's one fixed square position (sq0): its remaining
tau is odd, so v_s = q_s.w with w a perfect square. Write
q_s = x.u^2 with x squarefree; then v_s = x.Y^2 for an integer Y. So

    a_s.v_j = a_j.x.Y^2 + TYPE_RES(s, j)

If TYPE_RES(s, j) = -N with N > 0, and a_j.x.N = S^2 is a perfect
square, then multiplying by a_j.x:

    a_s.a_j.x.v_j = (a_j.x.Y - S)(a_j.x.Y + S)

Take out h = gcd(a_j.x, S): with alpha = a_j.x/h, sigma = S/h,

    f1 = alpha.Y - sigma,  f2 = alpha.Y + sigma
    f1.f2 = (P/Q).v_j,  P/Q = a_s.a_j.x / h^2 in lowest terms
    f2 - f1 = 2.sigma,  gcd(f1, f2) | 2.sigma

If TYPE_RES(s, j) > 0 the right-hand side is a sum, which does not
factor; so only partners with TYPE_RES(s, j) < 0 count.

### 2.2 Which x

For a pair (s, j) with N = -TYPE_RES(s, j) > 0, the condition holds
for exactly one squarefree x: xneed(s, j) = the squarefree part of
a_j.N. It divides a_j.N <= k^2.n, so it always fits a ulong. Each
pair's xneed, alpha, sigma, P and Q depend only on (s, j), so they are
found once at startup, for every ordered pair.

x itself is fixed once the square is: at a position with odd tau left,
every allocation p^{x-1} has x | t odd, so x - 1 is even and the
squarefree part of q_s cannot change. So the partners of a square are
known the moment it is fixed: those j with xneed(s, j) = x.

### 2.3 By type

| Type | N = -TYPE_RES(s, j) | partners | condition |
|---|---|---|---|
| o, r | s - j | j < s | x.(s - j) a square |
| a | (s - j).n | j < s | x.(s - j).n a square |
| t | (a_j - a_s).n | j > s | a_j.x.(a_j - a_s).n a square |

STRATEGY_6X is TYPE_o with x = 2, s - j = 2 (alpha = 1, sigma = 1,
P/Q = 1/2: v_j = 2.f1.f2). TYPE_o also gives, for instance, x = 2
with s - j = 8, x = 3 with s - j = 3, x = 6 with s - j = 6. I have
not checked how often pcoul's batches produce those. (x = 1 would
need odd n, so it does not arise: hv.)

Worked examples (all checked numerically):

| case | (s, j) | x | alpha | sigma | P/Q |
|---|---|---|---|---|---|
| pcoul 6X | (i, i - 2) | 2 | 1 | 1 | 1/2 |
| pctul f(198, 12) | (9, 10) | 2 | 1 | 3 | 5/11 |
| pctul f(150, 8) | (0, 3) | 2 | 2 | 15 | 1/2 |
| pctul f(150, 8) | (0, 6) | 7 | 7 | 30 | 1 |

### 2.4 The forced primes

Every prime of 2.sigma, P and Q divides a_j, a_s, N or x, and x's
primes divide a_j.N: they are primes <= k or primes of n. Sections 5
and 6 need the power of each of them at v_j fixed by the batch, so
that any prime the search still has to find at v_j is coprime to
2.sigma.P.Q.

`maxforce[j]` says which: a prime r is fixed at v_j if
r <= maxforce[j], or (TYPE_a, TYPE_t) r | n, the divisors of n being
forced at every position (hv). Under pcoul with n == 0 (mod 4),
maxforce[j] can be below k, so this is a real condition: check it for
each pair at startup (section 4.1), and do not keep a pair that fails
it.


## 3. What a pair gives

What a partner j gives depends on the tau t_j left there:

- **t_j odd:** v_j is a second square, and the existing Pell walk
  takes the node. Nothing new.
- **t_j = 2:** v_j = q_j.p for one prime p not yet found. Then
  f1.f2 = M.p with M = (P/Q).q_j, and the two factors differ by
  2.sigma: the candidates are finite (section 6).
- **t_j even, > 2:** any prime power r^e at v_j with r not dividing
  2.sigma.P.Q lies wholly in f1 or f2, both at most
  f2 = sigma + sqrt(sigma^2 + (P/Q).v_j). So every allocation at v_j
  is capped (section 5), and for q^2 that cap is a 4th root of zmax.
  This pays most when t_j has an odd factor (q^2 is then needed).
  Where t_j is a power of 2 above 2 its primes may all be distinct, so
  the cap shortens the loops less; but the two factors are each about
  the root of v_j, so the tests factorize smaller numbers, and in some
  cases one or both factors come down to an is_prime() check (hv).
  Using that changes how a candidate is tested: optional stage 4,
  not designed here.

For f(198, 12): b0 and b2 have t_j = 2 at v_10 (finite), b3 has 6
(the 4th-root loop, then t_j = 2), and b1 has 4, which gains nothing.


## 4. Detection and strategy

### 4.1 Startup

For every ordered pair (s, j) with N = -TYPE_RES(s, j) > 0 whose
primes of 2.sigma.P.Q are all fixed at v_j (section 2.4), record
xneed(s, j), alpha, sigma, P, Q, and the primes of 2.sigma with their
powers g (section 6). The table is at most k^2 entries of small
integers (the products fit a ulong: N <= k.n and a_j <= k).

Decided (hv): keep every pair; there is no bound on xneed. The table
costs at most k^2 small entries, and the test made when a square is
fixed (section 4.2) is a comparison per partner, so a pair that never
matches costs next to nothing.

Decided (hv): if every target tau is a power of 2, no position can be
left with odd tau above 1, so no square is ever fixed: skip the table
entirely, allocation included. That matters only for size: under
pctul those cases can have n = k, but the largest k attempted is
around 27.

### 4.2 When a first square is fixed

Today the switch is in `apply_secondary()`, for a forced allocation
only. A first square can also be fixed by an unforced allocation (an
odd power that leaves odd tau, as under -k's pass, or in the unforced
loops), and the pair holds there as well. So test wherever a node's
`have_square` becomes 1:

- x is the product of the primes with an odd power among sq0's
  allocations, found from the allocations without factoring. If any of
  those primes is not fixed at sq0 in the sense of section 2.4 (an
  unforced prime allocated to an odd power before the square was
  fixed), x has a prime no xneed can have: no partner.
- Otherwise the partners are those j with xneed(sq0, j) = x.

As today, switch to STRATEGY_SQDIFF when there is at least one,
keeping `prev_strategy`, and not when the strategy is STRATEGY_FIXED.
`best_sqdiff()` reverts when the conditions no longer hold. The
partners go on the node, as a short list (they are fixed while that
square is the only one). **[verify]** that every path that sets
`have_square` = 1 goes through one place where this can be done.

### 4.3 best_sqdiff()

`best_6x()` generalised; the shape stays:

- No longer exactly one square, or `kern_batch()`: revert to
  `prev_strategy`, as today.
- Some partner has odd tau: BV_WALK (Pell), as today.
- Some partner has tau 2: BV_SQDIFF, with that partner recorded for
  `walk_sqdiff()`.
- Otherwise allocate at a partner, unless the default strategy's
  choice has a lower `loop_limit()`, as today.

Decided (hv): with several partners, best_v() (or later the planner)
chooses between them, with little effort spent unless such matches
can be shown to be a significant part of a total run. From the scan
of section 1, a square with two or more useful partners (tau 2 left,
or an odd factor) occurs in only two cases: f(150, 9) and f(150, 10),
two batches each, which -ka estimates at 6270s and 7585s. So offer
the partners to best_v() as its candidates, and let it choose as it
does among positions.

The -ja2 exclusion (`strategy != STRATEGY_6X` in the choice code)
stays, as STRATEGY_SQDIFF.


## 5. The cap in limit_p()

Decided (hv): keep a cap as tight as the current one.

Replace the TYPE_o STRATEGY_6X branch by one for any type, at the
node's partner j (or any of them), for any x and any nextt. Let

- m be the product, over the primes r of 2.sigma, of r^{e_min(r)},
  where e_min(r) is the least exponent either factor can take in the
  splits of section 6 step 2 (fixed for the batch, since those primes'
  powers at v_j are);
- V_j be v_j at zmax (`dtov()`).

The factor holding p^{x-1} is at least m.p^{x-1}, and the other is
within 2.sigma of it, so (Q/P).F.(F - 2.sigma) <= V_j with
F = m.p^{x-1}, and the limit is

    p^{x-1} <= (sigma + sqrt(sigma^2 + (P/Q).V_j)) / m

taking the lesser of this and the usual limit. It holds for any prime
not dividing 2.sigma.P.Q, which is every prime the recursion allocates
at v_j (section 2.4). It is a true bound whatever the canonical order
of allocations within a position, so it cannot lose solutions.

For STRATEGY_6X's case (sigma = 1, P/Q = 1/2, M with 2^e for e >= 3,
so the splits of 2 are (1, e - 1) and (e - 1, 1) and m = 2) this gives
p^{x-1} <= (1 + sqrt(1 + V_j/2))/2, about (V_j/8)^{1/2}: today's
bound, which it now gives for every nextt rather than nextt = 2 only.

The comment on `limit_p()` requires that a lower zmax never gives a
higher result. The bound is increasing in V_j, so that still holds.


## 6. walk_sqdiff()

`walk_6x()` generalised. At t_j = 2, v_j = q_j.p with p a prime not
yet found, coprime to 2.sigma.P.Q (section 2.4).

1. M = (P/Q).q_j. If that is not an integer there is no solution:
   return.
2. Split M into A (the side without p) and B (the side with p), part
   by part:
   - each allocation at v_j whose prime does not divide 2.sigma goes
     wholly to one side: one bit, as in today's bit vector over the
     allocation levels;
   - each prime of P that is not among the allocations at v_j (the 5
     of f(198, 12)) likewise: one more bit, past the allocation levels;
   - each prime r of 2.sigma, with e = v_r(M) and g = v_r(2.sigma),
     takes an exponent e_B on B's side, with e_A = e - e_B, from the
     splits that v_r(B.p - A) = g allows: e_A != e_B and
     min(e_A, e_B) = g, or e_A = e_B <= g. This replaces today's
     special handling of 2 (`ap->x - 4` and the removed 8).
3. For each split, as today, try both signs: B.p = A +/- 2.sigma, so
   p = (A +/- 2.sigma)/B must be a positive integer, prime, and not
   divide q_j. Today's pruning a >= b becomes A >= B.p_min - 2.sigma,
   with p_min the least prime that can be unallocated at v_j.
4. Y = (min(A, B.p) + sigma)/alpha must be an integer.
5. Then v_j = q_j.p is fixed: `walk_1()` it, as today.

The order of the walk must be fixed, so that it can resume (section
7): outer over the bit vector (descending, as today), inner over the
exponents e_B of the primes of 2.sigma in ascending order of prime.

Cost against today's `walk_6x()`: the number of splits tried is about
2^(bits) times the few splits of each prime of 2.sigma; for the pcoul
6X cases prototyped that came to 4 to 32 per call, the same order as
today. The extra work per candidate is a few divisions. hv expects
that a slowdown of the order of 5% on the old 6X batches would not
show in any full run, since they appear alongside much slower batches.

**[verify]** that `walk_1()` rejects a d outside the node's residue
class and checks every position, so step 5 need do nothing more.


## 7. Recovery

Decided (hv): resume inside the walk, since it may be doing expensive
factorizations, but do not resume inside the `walk_1()`.

So the walk's state is what recovery needs: the bit vector of section
6 (allocations, then the extra primes of P), and e_B for each prime of
2.sigma. The sign is tried within a state, as today, and needs no
record. Decided (hv): the mark becomes

    " Q(p,vi,a,e)"

with p the candidate in progress, vi the partner, a the bit vector,
and e the exponents e_B, dot-separated in ascending order of prime
(for example "1" for 6X's case, where 2 is the only prime of
2.sigma). On recovery the walk restarts at that (a, e).

Old logs: the mark " 6X(p,vi,a)" means a state of `walk_6x()`, whose
split of 2 differs from section 6's. Rather than translate it, accept
it and start that walk from the beginning; it is short, and only a run
stopped inside such a walk is affected. Decided (hv): that is fine.

`-j5` still selects the strategy directly (STRATEGY_SQDIFF keeps
STRATEGY_6X's value).


## 8. -k and -ka (calibrate, stage 3)

- `kern_6x()` becomes `kern_sqdiff()`: "this batch has a partner of
  its square", for every type.
- `ke_6x()` (as `ke_sqdiff()`) builds in 6X's constants
  (L = (zmax/8)^{1/4}, tau 6 at v_{i-2}). It becomes: for each
  partner, L from section 5's bound with x = 3, and the root count as
  now; take the cheapest partner.
- `ke_prefer_6x()` (as `ke_prefer_sqdiff()`) and kern_plan's choice
  keep their logic.
- The disallowing rule of 2026-11-20 (a -k batch disallows every
  position -k does not apply to) does not clash: a batch left to
  STRATEGY_SQDIFF has -k off. **[verify]** for a batch where -k is
  chosen over sqdiff but a partner remains.


## 9. Stages

**Stage 1 (master): the general machinery, for 6X's case only.**
The rename (9.1), the startup table, detection at the first square,
the cap, the general walk and its recovery, but with detection limited
to the old pattern (TYPE_o, x = 2, partner s - 2). pcoul's output must
be unchanged apart from candidates found in a different order, and its
times within a few percent (section 10.2).

**Stage 2 (master): every pair, every type.** Lift the limit on
detection. pctul f(198, 12), and new pcoul pairs.
pcoul-internals gains a section on sqdiff.

**Stage 3 (calibrate): -k and -ka**, section 8.

**Stage 4 (optional, not designed):** test a candidate at a partner
through its two factors (smaller factorizations, sometimes an
is_prime() check), section 3.

### 9.1 Names

| now | becomes |
|---|---|
| STRATEGY_6X | STRATEGY_SQDIFF |
| best_6x() | best_sqdiff() |
| walk_6x() | walk_sqdiff() |
| BV_6X, CH_6X, A_6X, IS_6X | BV_SQDIFF, CH_SQDIFF, A_SQDIFF, IS_SQDIFF |
| diag_6x(), suffix_6x(), parse_6x() | diag_sqdiff(), suffix_sqdiff(), parse_sqdiff() |
| mark " 6X(p,vi,a)" | " Q(p,vi,a,e)" (old mark still parsed) |
| kern_6x(), ke_6x(), ke_prefer_6x() (calibrate) | kern_sqdiff(), ke_sqdiff(), ke_prefer_sqdiff() |

The mark is " Q(" (hv), which no other mark uses on master, mt or
calibrate-mt.


## 10. Testing

### 10.1 Done for this design

- The identity of section 2: 23 pairs, Y = 50..59 each, exact.
- The enumeration of section 6, prototyped in Python: 480
  (pair, q_j) cases over eight pairs (pcoul 6X, pcoul x = 1 and x = 3
  pairs, the first only as arithmetic since x = 1 cannot arise, pctul
  f(198, 12) and four f(150, 8) pairs), each compared with brute force
  over Y. No solution was missed once p was required to be coprime to
  2.sigma (section 2.4); without that requirement there is one miss,
  where p = 5 divides 2.sigma, which a real batch cannot produce since
  5 is forced there.

### 10.2 For the stages

1. Stage 1: pcoul on cases where STRATEGY_6X fires (n == 2 (mod 4),
   k >= 4, e.g. D(18, 5), D(174, 3), D(30, 5)) at several bounds:
   identical solution sets under -X, and times against master. Check
   that the cap of section 5 gives today's limits where today's applies.
2. Stage 1: recovery from each " Q(...)" line of a -X run with a
   long walk, as t10init does for other marks; and from an old
   " 6X(...)" line.
3. Stage 2, pctul: f(198, 12) b0, b2 and b3 to 1e30 (b3 took 3977s
   under -ja2 -ka; expect seconds), and a match under -X against mt's
   pctul on small bounds of the scan's cases (150 7 and 8, 160 8,
   200 10, 96 8).
4. Stage 2, pcoul: new pairs (x = 2 with partner s - 8, x = 3 with
   s - 3, etc.) under -X against master at small bounds.
5. t80tseq (TEST_TSEQ) and `make dtest`, as always.
6. A t/ test of the walk on a small case with a known pair solution
   (the f(198, 12) b0-like case q_j = 77 gives two Y).


## 11. Decisions

Decided (hv):

1. The name is "sqdiff" (9.1).
2. Recovery resumes inside the walk, not inside walk_1() (7).
3. best_v() chooses among several partners (4.3).
4. The cap stays as tight as today's (5).
5. Every pair is kept, with no bound on xneed (4.1).
6. This document stands alone, to be discarded once implemented.
7. Testing through the two factors is optional stage 4, not designed
   here (3, 9).

8. An old " 6X(...)" mark starts that walk again (7).
9. The mark is " Q(p,vi,a,e)" (7, 9.1).
