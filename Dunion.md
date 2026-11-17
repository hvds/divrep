# pcoul shared windows: searching overlapping runs at once

Design in progress, NOT yet ready to implement. Written against
master at 5a553ae (2026-11-14), with the planner design (Dplanner.md)
and the pctul design (Dpctul.md) read alongside.

Status: second draft, 2026-11-15, after hv's first review. The first
draft paired runs two at a time by the parity of d. hv proposed a
better rule (4.2), which replaces it; much of the first draft went
with it. What is here is the model as agreed in discussion, what is
decided, and what must be checked or designed before any C is
written. Section 6 lists the checks not yet made; do those first.

Marks: "Decided" is hv's decision. **[hv]** needs his decision.
**[verify]** is my reading of the code. **[unchecked]** is an argument
made in discussion that nothing has tested.

Revised the same day: checks 1 to 3 made (6.1). Check 1 found a
second hole in 4.4, now fixed there; hv's form of the rule (4.4)
replaces mine and is confirmed. Check 2 confirms it with tails, and
adds one rule (4.3). Check 3 confirms that pcoul's batches are the
patterns the checks assume, and finds a third hole: pcoul's own
pruning of batches can drop an owner whose runs are still live
(4.8; hv has chosen the fix).

What stands behind this document:

- `wcheck.c`, a brute-force check of 4.2 to 4.4 with all forced
  primes together, with and without tails (6.1).
- The measurements of appendix A (throwaway patch over master
  daa8f4a, on batches of hv's D(96,8) and D(48,10) runs).
- An earlier brute-force check, `ucheck`, of the FIRST draft's rules for
  windows of k + 1. It does not test the rule of 4.2. It is evidence
  that the "more outside" idea of 4.4 is sound in that one case, and
  a starting point for the check that is needed.
- Statements about the C code are from reading master. Nothing was
  prototyped: the gain is inferred, not shown.


## 0. Before starting

Read `CLAUDE.md`, the divrep-conventions and pcoul-internals skills
("Forced primes, batches, and the tail"; `t_node.dis`), pctul-design
sections 4.2, 4.3 and 5, and planner-design sections 4 and 5.7.

New option letters, log syntax and line codes are hv's decisions.


## 1. The problem

pcoul searches for the least d with tau(d + i) = n for 0 <= i < k,
one batch per pattern of the forced primes across the k values. Two
batches often describe the same integers. With n = 96, k = 8:

    b240021:  2^2.3  5  2  3^3  2^5  .  2.3.5^3  .
    b181320:         5  2  3^3  2^5  .  2.3.5^3  .  2^2

The second is the first moved along by one. Each builds its own tree
and tests the same integers in its own walks.

Measured (appendix A): where one batch is exactly another moved by
one, 92 to 100 percent of the candidates reaching the tau tests are
the same integers in both, failing at the same shared position.
Where the move is not exact almost nothing is shared. The number of
moves a walk's forced structure allowed was typically 4 to 10, so
pairs are not the limit.


## 2. Goal

1. Search each family of batches that are one pattern moved along
   once: one tree, one walk, over the values every member shares.
2. The general case from the start: as many runs together as the
   pattern allows, not pairs. (Decided: hv does not want code for the
   special case first.)
3. No restriction on k. (Decided: hv has k = 3 runs that take
   months.)
4. Keep the run a proof, by an argument that is stated and tested.
5. With the feature off, logs identical to the build before.
6. The choices (whether to share, how far, where to allocate) are the
   planner's, as tactics with prices.

Non-goals: pcaul, pcrul, pctul (section 9). Moving a run in progress
onto the scheme: hv confirms there is no such need, since D(96,8) and
D(48,10) are to be rerun from scratch.


## 3. Principles

S1. **A run is a proof.** Every d is answered for by exactly one
    piece of the search (4.2 to 4.4), and that is tested by brute
    force before it is relied on.

S2. **Skipping is by rule, never by choice.** Whether a batch is
    searched or left to another is fixed by its pattern. The planner
    never decides that; it decides only how the batch that owns a set
    of runs covers them (4.6). So no decision depends on one made in
    another branch of the search.

S3. **A node reasons only from what all its runs share.** A bound, a
    limit or a rejection may use a position only if every run the
    node still answers for contains it. Using any other position
    first gives up the runs that lack it (4.5).

S4. **Testing too much is safe; answering for too little is not.**

S5. **One layout, one set of walks.** An ordinary node is a node with
    one run.

S6. **Fail loudly, or fall back by giving up sharing**, which is
    always sound.


## 4. The model

### 4.1 Vocabulary

- **run**: one d, with its k values d .. d+k-1.
- **primary** of a forced prime p in a run: the first position with
  the greatest power of p, as in `test_forcep()`. It is relative to
  the run's window: moving the window can change it. That is the
  source of every difficulty below.
- **span** of a batch: from its least primary to its greatest, over
  the forced primes that have one (a tail has none).
- **shared window** of a node: the positions every run it answers for
  contains. For a set of runs starting at s_lo .. s_hi it is
  s_hi .. s_lo+k-1. hv's term for a batch seen this way is a
  **narrow batch**; its runs are its full-width children.
- **reach**: all positions of all its runs, s_lo .. s_hi+k-1.

Giving up a run at one end widens the shared window by one position
at that end.

### 4.2 Which batch answers for a run (hv's rule)

Build the batches as now. For a complete batch with span [a, b] in
its own window 0 .. k-1:

- If a = 0 (its least value holds a primary) it is an **owner**. It
  answers for its own run and for the runs to its left that contain
  the whole span and show the same pattern: starts s in [s_min, 0].
- If a > 0 it is the same pattern as the owner a places to its right,
  and is not searched, except for the part of its class that owner
  cannot answer for (4.4).

Batches are met in the same order as now, with the same ids. (hv:
different options already give different ids, so `-a` users are not a
concern either way.) Decided: owners are displayed and numbered as
narrow batches; their full-width children are neither. **[hv]**:
whether a batch that is wholly left to its owner still takes an id.

### 4.3 The runs of an owner (checked: 6.1)

Take an owner C, primaries i_p with power e_p. Moving the window left
brings in earlier positions. For C to be the same pattern in the
moved window, each new position j must have a power of p strictly
below e_p (else the primary moves). With g the power of p in i_p - j:

- g < e_p: the power at j is exactly g. Fine if g + 1 divides n;
  otherwise no run containing j can live.
- g >= e_p: the power at j is e_p or more. The primary moves.

Both are fixed by the pattern, not by the class. So:

    s_min = the greatest of
        b - k + 1                        (the span must fit)
        i_p - p^{e_p} + 1, for each p    (nearest earlier rival)
        j + 1, for each earlier j whose exact power is invalid

and for every anchor in C's class every run in [s_min, 0] has its
forced powers fully determined. Moving left only drops positions on
the right, where C already states exact powers.

Tails (checked: 6.1, check 2). In pcoul (TYPE_o, 4 | n) a prime
p > f with only one multiple in a window is on that window's tail: no
primary, nothing fixed. So "the same pattern" also means the same set
of primes on the tail, and two more kinds of limit arise, on both
sides of a family:

- **A batched prime p > f must keep two multiples.** Moving the window
  can leave it with one, which puts it on the tail: a different
  pattern. Its multiples are at i_p + m.p, so this is fixed by the
  pattern (mandatory). It applies both to "can the window move right"
  and to the left limit. (Found by check 2; not in the first form of
  4.3.)
- **A tail prime q must stay single.** Moving the window can bring in
  a second multiple of q, which makes q batched: a different pattern.
  Where q's multiple lies is not fixed by the class, so this depends
  on d mod q. It limits the family on the left (a left limit for
  each candidate), and on the right it makes a window an owner on
  only part of its class: the classes mod q where the entering
  position is a multiple of q.

Three ways of handling the second, as before:

- in a walk, for each candidate (d is then known): checked;
- in the tree, once q is allocated: the same rule, known earlier, so
  the same check covers it;
- giving up the tail (f >= k), which makes everything static: the
  no-tail case of check 1.

They are all sound, so the choice is one of cost, and the planner's.
The second kind of limit has the same shape as a floating impediment
(4.4): an owner on part of its class, with that part known only per
candidate unless it is folded in. Against the first two, the third
splits more batches. Check 2 gives an unweighted idea of what tails
cost in sharing: 1.58 runs per owner with f = 2 against 1.77 with no
tails (6.1). In the D(96,8) measurement (q = 7 on a tail) this effect
is why 4 to 8 percent of candidates were not shared.

A batch with no primary at all (every forced prime on its tail: k = 2
with f < 2, where pcoul has no forced primes) has no family; it
answers for its own run only, as now.

### 4.4 What a non-owner must still search (checked: 6.1)

The hole in the rule as first stated. n = 12, k = 4, d = 5:

- window 5..8: 3's primary is 6, 2's is 8. Not an owner (5 holds no
  primary); it expects the window at 6 to answer for it.
- window 6..9: 3's primary is now 9. Not an owner either.
- window 8..11: an owner, primaries 8 and 9; its runs start at 6, 7,
  8.

Nobody answers for d = 5. In general: batch B with a > 0 is the same
pattern as its owner only if no position that enters on the right,
k .. k+a-1, holds a greater power of p than B's primary. Such a
position j is one where j - i_p has exactly p^{e_p}; it then has
p^{e_p} (a tie, harmless on the right) or more. "More" is one class
of v_{i_p} / p^{e_p} (mod p): a fold, in `t_forcebatch` terms.

So B searches, as an ordinary single run, the part of its class where
for some forced prime some entering position has more. Per prime that
is a small set of folds R_p; across primes it is every combination
except "no prime has more", which is the part its owner has.
(hv: this fix makes sense to him.)

**A second condition, found by check 1.** Where no entering position
has more, the powers of the forced primes at every entering position
are determined, and their forced tau may not divide n. Then the owner
batch is invalid and is never searched, so B must search itself here
too. Example, n = 6, k = 5, d = 1: the window 1..5 is valid (3's
primary at 3, 2's at 4, so a = 2), but the owner's window 3..7 brings
in 6 = 2.3, forced tau 4, which does not divide 6. Without this
condition check 1 misses runs in 125 of its 312 cases. Unlike "more",
it is fixed by the pattern, not the class: a batch with an invalid
entering position simply is not a non-owner, and is searched whole as
one run.

So B searches itself where some entering position has more (class
dependent), and wholly if some entering position is invalid (pattern
dependent). This is the mirror of the "invalid earlier position" term
in 4.3's s_min: the owner stops short of such a position, so the runs
beyond it must answer for themselves.

**hv's form, which replaces the above.** A family is a maximal set of
consecutive windows with the same primaries, all valid. Its owner is
its rightmost window: the one that cannot move right by one. From a
narrow window, look right for the first impediment caused by further
instances of its primes, and take the window that ends just before
it. An impediment is:

- **mandatory**: from primes at fixed powers. The entering position's
  forced tau, from determined powers, does not divide n. For p = 2 a
  tie is also mandatory: if v_i has exactly 2^e and the entering
  position is 2^e.odd further on, the sum of two odd multiples of 2^e
  has more than 2^e, so the entering position always has more.
- **floating**: from a prime (odd p) at a floating power. A tie at
  the entering position has more on one class of v_i / p^e (mod p)
  and exactly p^e on the rest. On the first part the family ends
  here; on the rest the scan continues to the next impediment.

Plus the existing end: the least position holds a primary, so moving
right would drop it. On the left every limit is mandatory (span,
rivals, invalid positions: 4.3), so s_min is fixed by the pattern.

So a window owns its family where its least position holds a primary,
or where the position entering on the right is an impediment; and a
window that owns nothing is skipped, never searched alone. Where 4.4
above has a non-owner search a run by itself, this form makes that
window an owner of every run to its left, so they still share. It is
checked (6.1, mode 5).

Open: a floating impediment makes a window an owner on only part of
its class (one class mod p, or a union of such for several primes).
That part must reach the search either as a fold (aq times p) or as a
filter in the walk. A fold is the cheaper walk, but the condition
depends on the complete batch (it matters only if the window is not
already an owner for a static reason), so it cannot simply be set at
p's forced level. The remaining part belongs to the window one place
right, whose batch states the exact power at that position and so
excludes "more" there through `inv[]` as now.

The argument that every d is then answered for once:

- d's own batch B is unique. If B is an owner, d is its run 0.
- Otherwise either no entering position has more, and d is run -a of
  the owner (which is within that owner's s_min, because B's own
  window has no rival and no invalid power); or one does, and B
  searches d itself.
- An owner's run -t is the window of a non-owner whose "more" part
  lies at positions inside the owner's window, where the owner states
  exact powers; so the two never both answer.

For p = 2 there is always a fold, so nothing is open: an entering
position's power of 2 is determined.

Not yet worked out:

- How the extra folds reach the search. a is known only when the
  batch is complete, but a fold belongs to a prime's level. Either
  the forced lists are refined for every a that could arise, or the
  class is tightened at batch completion, which needs a way to add a
  class with no allocation (pctul's `batch_resclass()` and its plain
  batches are the nearest thing).
- Whether the part B searches should itself be shared with its
  neighbours. Proposed: no, until measured.
- Batches with no primary at all (every prime on a tail, or no forced
  primes): ordinary, one run.

### 4.5 Allocating below an owner

An allocation at a position constrains only the runs that contain it.

- Inside the shared window it constrains them all, and the argument
  that a loop covers its node is as now.
- Outside it, the allocation is valid only for the runs that contain
  that position, so those that do not must be given up first (covered
  separately, in place): the shared window widens to include it.

hv: this is hard to decide by rule, because the cost of allocating
outside the shared window is the widening itself, which is a reason
to defer the bulk of the work until the planner exists. Decided.

Likewise S3 for everything that prunes: `mintau()` and what feeds
it, `apply_allocv()`, the square count, the check for a completed
value, the overflow check. A site list is needed **[verify]**; the
first draft's section 5 named these from reading, for 59 loops over
k in coul.c.

A position outside the shared window with an odd remaining tau (a
square only some runs have) is the same question: use it, and give
up the runs without it.

### 4.6 Giving up sharing in place

An owner (or any node below it) can always split its runs into two
ranges and search one then the other under the same node: a level
that allocates nothing, in the manner of `apply_null()`. Each child
has a wider shared window. Splitting down to single runs gives
today's search.

This is the only place a choice is made (S2), and it is made where
the runs are owned, so recovery replays it from the log like any
other level (planner P3). **[hv]** for how it shows in a progress
line.

### 4.7 The walk (hv's direction, not yet designed)

On each iteration the walk knows the range of runs still possible.
A value that fails:

- inside the shared window ends the iteration;
- outside it rules out the runs that contain it, which narrows the
  range and so widens the shared window, bringing more values into
  it.

The iteration ends when no run is left; a run all of whose values
pass is a solution.

hv does not want the outside values left to the end (as the first
draft's "rider" did; that was justified only for windows of k + 1,
where under 1 percent of candidates got past the shared values). With
a shared window as small as one position, the order of tests has to
weigh, for each value, whether it is mandatory and, if not, how much
of the range its failure would remove. That needs a modified form of
the multi-tau tests (`tau_multi_prep()`, `tau_multi_run()`) that
takes such weights. To be designed.

The range also starts narrower for a candidate than for the node
where a tail prime's position is known only per candidate (4.3).


### 4.8 Pruning of an owner (found by check 3; approach decided)

pcoul prunes batches as the forced chain applies them and at batch
completion: no roots for a forced square (`alloc_square()`), the
secondaries' effect on a square (`update_residues()`), two squares
(Pell), a value fixed. Each decides that no d in the batch's class can
be a solution, using every position of the window. For an owner that
is not enough: its runs to the left lack its rightmost positions, and
a reason that rests on one of those does not apply to them. Check 3
finds such cases in real pcoul batches (6.1): the owner is pruned,
the run to its left is a batch pcoul searches today, and under the
rule nobody searches it.

This is S3 (a node reasons only from what all its runs share) applied
to the forced chain, where the runs are not yet known: the left limit
of a family is found only at completion.

Decided (hv): **narrow instead of drop.** Pruning stays where it is
now, in the forced chain and at batch completion. Batch generation
does not try to foresee all the ways a batch might be pruned. Instead
each pruning site is taught, through new abstracting functions, that
denying a possibility need not deny the whole batch. (Rejected: count
a pruned right neighbour as an impediment. That would have each window
look forward at its neighbour's pruning, and the neighbour's at its
own, and so on.)

**Why one number per node suffices.** A window's runs, as an owner,
are the windows starting at s for s from s_min up to 0 (its own run).
All of them lie at or to the left of it. A reason that rests on
positions jlo .. jhi of the window (all 0 or more) applies to a run
only if the run contains all of them. A run [s, s+k-1] with s <= 0
contains every position from 0 to s+k-1, so it contains jlo whenever
it contains jhi. So the reason removes the runs with
s >= jhi - k + 1, and only its rightmost position matters. A node
therefore carries one bound,

    s_hi:  the greatest start of a run still possible (0 at first)

and a reason resting on positions up to jhi sets
s_hi = min(s_hi, jhi - k). At completion the owner's range is
[s_min, s_hi], and the batch is dropped only if that is empty. A reason
found in the window always removes the window's own run (jhi <= k - 1
gives s_hi <= -1), as today.

**The abstraction.** Proposed, for the implementer to refine:

```c
/* A reason found at np rules out every run that contains position
 * jhi of np's window (and the positions before it that the reason
 * uses). Returns true if some run may still be possible, in which
 * case the caller carries on as if nothing had been ruled out; false
 * if none can be, in which case the caller prunes as it does now.
 */
bool deny_runs(t_node *np, uint jhi);
```

With the feature off a node has only its own run, `deny_runs()`
always returns false, and every site behaves exactly as now. During
the chain, s_min is not yet known: a caller carries on while
s_hi >= -(k - 1) (some run could still hold the span), and the range
is settled at completion. So batches that are dropped today go further
down the chain under the feature. That costs a little in batch
generation, which is not where the time goes.

**What each site passes.** The rightmost position the reason uses.
Passing k - 1 (the whole window) is always safe: it removes only the
window's own run, and loses nothing. A site may pass less only where
it is shown to use nothing to its right. Start with every site
passing k - 1, then tighten site by site, each with a check that it
loses nothing.

**What the residues of a square rest on** (from reading master). In
`apply_batch()` only the primary changes the class (rq, aq), through
`apply_primary()` (since pctul stage 2, from the batch's
`batch_resclass()` through `apply_resclass()`). A
secondary goes only through `apply_allocv()`: the tau check, its q,
and, if its own position has just become a square, `alloc_square()`
there, from the class and that position's q. For a square already
fixed, `update_residues()` is called for the primary, unless a
secondary lies on the square itself, when that is applied first and
then the primary's remainder. A secondary's power is itself fixed by
the primary's class and its own position. So the residues of a square
at s rest only on the span, on s, and on secondaries at s, never on a
secondary elsewhere. (The fold for p = 2 is always "v / 2^e odd" and
rests on nothing else; odd p have no fold today.) Hence a square
without roots at s rests on max(s, the span's right end): if s is in
the shared window, the reason applies to every run, as it should.
**[verify]** the remaining sites (the terminal and Pell checks, and
anything under -m or -c, which are refused under the feature anyway).

**Separating runs at a special position** (hv). Where a position j
outside the shared window has a state the code acts on, the runs that
contain j are separated from those that do not:

- j has a fixed square (a forced square there, or one a secondary
  fixed): the runs containing j can walk over roots, the others
  cannot use it at all.
- j is fully allocated: for the runs containing j, d is fixed (as
  `walk_1()` does now); for the others nothing is.
- a secondary at j raises the power there: this matters only through
  the two cases above (if j is an existing square, it is the first).

Today's whole-window tests (`have_square`, the count of squares behind
`pell_now()`, `terminal`) then count shared positions only, and a
special position outside the shared window causes a separation
instead. In the forced chain the runs are not yet known, so the
separation is made at completion; it is a split of 4.6, two children
of the owner, each with its own range of runs, and the one with the
special position can then use it. Below the batch it cannot arise
unseparated: an allocation outside the shared window already requires
giving up the runs that lack the position (4.5). Whether separation
is always right, or sometimes the square should simply be ignored by
all the runs, is a costed choice for the planner later; by default,
separate.

**The same function in the walk.** hv's walk (4.7) narrows the range
of runs as values are proven bad. That is `deny_runs()` again, for a
candidate rather than a node, and with a lower bound as well: a value
proven bad at a position left of the shared window removes the runs
that contain it, which are those starting at or before it. So the walk
needs s_lo as well as s_hi, and one function for both.

**Pell.** An owner may solve Pell only if both squares are in every
run it still answers for (S3). Otherwise the separation above gives
a child whose runs all contain both (Pell, nearly free) and one whose
runs lack the second square.


## 5. What changes in the code, in outline

Not a site list; that comes after section 6.

- Positions: arrays must hold the reach, up to k - 1 positions left
  of the batch's own window. A node carries its range of runs; the
  shared window follows. With the feature off every node has one run
  and nothing changes (first draft, stage 1: a refactor with
  identical logs).
- The forced chain is today's. The work is at batch completion: find
  a; for an owner, s_min; for a non-owner, the folds of 4.4.
- `candidate()` is given the d of the run that passed. Bounds on d
  apply per run.
- Use pctul's accessors (`TYPE_MULT()`, `TYPE_RES()`, `dtov()`,
  `vtod()`) wherever an offset is touched; no bare offsets.
- Refuse the feature, with a message, wherever a stage does not yet
  support it (`-c`, `-m` at least).


## 6. Checks

### 6.1 Made

**Check 1: the rule of 4.2 to 4.4, all forced primes together, no
tails.** `wcheck.c` (delivered with this document). For each d it
finds the primaries of every forced prime in d's window, then applies
the rules from the batch alone: an owner claims runs s_min .. 0, with
s_min from the pattern by 4.3; a non-owner searches itself if an
entering position has more (4.4, tested against the real valuation,
which is the same as testing its class) or is invalid. A d is to be
answered for if the forced tau at each of its k positions divides n.
It also confirms that the powers 4.3 derives to the left of an owner
from its pattern are the real ones.

Grid: n in {2, 4, 6, 8, 9, 10, 12, 16, 18, 20, 24, 28, 30, 32, 36,
40, 48, 60, 64, 72, 96, 100, 120, 144, 192, 240}, k from 2 to 13,
d from 1 to 3 million. 312 cases; every valid d answered for exactly
once, no invalid d answered for, no pattern mismatch. Across the grid
(unweighted): 119 million owners claiming 225 million runs, a mean of
1.88 runs each; 152 million non-owners, of which 31 percent search
themselves; so 83 percent of runs are covered by an owner.

Controls, on d up to 200000, each shown to fail:

| control | cases failing | failures |
|---|---|---|
| no "invalid entering" condition (4.4 as first written) | 125 | 195417 missed |
| non-owners never search themselves (the rule as first stated) | 204 | 3123587 missed |
| s_min ignores rivals | 192 | 2925974 duplicated, 894034 extra |
| s_min ignores invalid earlier positions | 125 | 84153 extra |

The last is worth noting: without the invalid-position term an owner
claims runs whose windows are invalid. That tests too much but loses
nothing (S4), so that term is an economy, not a matter of
correctness. Its mirror in 4.4 is a matter of correctness.

hv's form (4.4), mode 5 of `wcheck.c`, same grid to 3 million: no
failure. Owners 153.8 million, claiming 271.5 million runs; nothing
searched alone. By reason of ownership: least position holds a
primary 119.4 million, floating impediment 32.5 million, mandatory
impediment 1.9 million (the p = 2 ties are counted as floating here,
though section 4.4 argues they are mandatory). Against mode 0 that is
153.8 million searches in place of 166.3 million (owners plus runs
searched alone), unweighted by cost.

The d = 5 example of 4.4 reproduces: under the rule as first stated
(control 2) d = 5 for n = 12, k = 4 is missed, with non-owner 5 left
to owner 6 which does not exist as such.

Not covered by check 1: tails (check 2); type a; anything below the
forced chain (unforced primes play no part in who owns what, so none
is needed there); d beyond 3 million (high powers of small primes are
rare, but the grid's k <= 13 means p^e up to 3^14 or so appear).

**Check 2: tails.** Mode 6 of `wcheck.c`. pcoul's rule (TYPE_o,
4 | n): a prime p > f with one multiple in a window is on its tail;
otherwise batched. A window owns its family if it cannot move right
by one with the same pattern (hv's form, 4.4, with the tail limits of
4.3). Everything is derived from the batch's pattern except the
limits a tail prime sets, which use the real d, as a walk would for
each candidate. "To be answered for" is a window valid for the primes
batched in it, which is what pcoul walks today. Every claimed run is
also checked to have the owner's pattern.

Grid: n in {4, 8, 12, 16, 20, 24, 28, 32, 36, 40, 48, 60, 64, 72, 96,
100, 120, 144, 192, 240}, k from 2 to 13, f in {0, 2, 3, 5, 7, none},
d up to 1 million. 1440 cases, no failure, no claimed run of another
pattern.

| f | owners | runs claimed | runs per owner |
|---|---|---|---|
| 0 | 77.8 M | 97.3 M | 1.25 |
| 2 | 57.8 M | 91.5 M | 1.58 |
| 3 | 53.0 M | 88.0 M | 1.66 |
| 5 | 50.1 M | 85.8 M | 1.71 |
| 7 | 47.5 M | 84.1 M | 1.77 |
| none | 47.0 M | 83.1 M | 1.77 |

(f = 0 is pulled down by its k = 2 cases, which have no primary.
Unweighted by cost throughout.) Owners by reason, over all f: least
position holds a primary 203 M, floating impediment 57 M, a tail prime
gains a multiple 31 M, a batched prime drops to one multiple 9 M,
mandatory impediment 3 M, no primary at all 30 M. A tail set the left
limit 33 M times.

Its first run found the no-primary case of 4.3 (every d missed for
k = 2, f < 2), which 4.4 already said to treat as a single run and
the check had not.

Controls, d up to 100000, each failing wherever tails exist and
nowhere without them:

| control | failures |
|---|---|
| drop "a batched p > f keeps two multiples" | 490428 missed, 3408047 duplicated |
| drop "a tail prime gains a multiple" from the owner test | 4705238 missed |
| drop the tail limit on the left | 5404606 duplicated, 805559 extra |

Not covered by check 2: a tail at f >= 2 for p = 2 cannot arise for
k >= 4 (every window has two even values), so p = 2 tails were tested
only at k = 2 and 3; type a, whose tails differ (`keep_single` for
p | n).

**Check 3: the checks' patterns against pcoul.** `acheck` (Perl)
compares, for each (n, k, f), the batches `pcoul -a4` lists (master
daa8f4a) with the forced-prime patterns that real windows show, with
`wcheck.c`'s rule for which primes are batched. Two details of pcoul
had to be matched: forced primes are applied in ascending order, and
under -a4 a batch is listed as soon as some value is fully allocated,
before the remaining primes are applied (a short batch). pcoul's
primary needs no separate check: a pattern determines it (first
greatest power, `test_forcep()` rejecting an earlier equal one), as in
`wcheck.c`.

Grid: n in {4, 6, 8, 9, 10, 12, 16, 18, 20, 24, 30, 36, 48, 60, 72,
96}, k from 2 to 9, f in {default, 2, 3, 5} up to k where 4 | n
(pcoul refuses f > k), d and -x up to 60000. 348 cases, 482944
batches listed: no case differs.

- Every listed batch whose LCM is at most 1/16 of the range is shown
  by some window. (169012 listed batches were not seen, all with a
  larger LCM, where the first member of the class can lie beyond the
  range.)
- Every pattern windows show is listed, or is one that no window
  showing it can complete: at each position the forced tau divides
  n, and the cofactor is 1 where nothing is left and a perfect g-th
  power where what is left forces one. 214433 patterns (40 percent of
  those seen) are of the second kind: pcoul prunes them, mostly for
  want of roots of a square, and correctly.

That pruning is not part of the ownership rule as checked, which takes
an owner to exist whenever its pattern is valid for the forced
primes. `ocheck` (Perl, with `wcheck.c` mode 6 dumping who claims each
run) tests that, with d up to 40000: of the shared claims (a run
claimed by an owner other than itself), how many have an owner whose
pattern pcoul prunes, and of those how many have a run that could
complete. Mostly none, but not always:

| case | shared claims | owner pruned | run could complete |
|---|---|---|---|
| n=12 k=6 | 6425 | 3733 | 47 |
| n=12 k=7 | 4647 | 3446 | 30 |
| n=30 k=4 | 7907 | 6170 | 13 |
| n=12 k=6 -f5 | 6384 | 5451 | 41 |
| n=24 k=7 -f7 | 6708 | 3484 | 159 |

and 0 for n=12 k=4 and k=5, n=6 k=5, n=24 k=5 to 7, n=48 k=6 and 7,
n=96 k=6 and 7, n=20 k=5, n=28 k=5, n=36 k=5, n=96 k=7 -f7.

Confirmed against pcoul: for n = 30, k = 4 the run at d = 17 has the
batch `. 2.3^2 . 2^2`, which pcoul lists (b31) and so searches today.
Under the rule it is a non-owner, left to the window at 18,
`2.3^2 . 2^2 3`, which pcoul does not list: the last position, 21,
is left with tau 15 and must be 3.z^2, and with the rest of the
pattern there are no roots. Position 21 is not in the run at 17. So
that run would be searched by nobody. Likewise for n = 12, k = 6 (b190
`. 2^2.3 . 2 3^2 2^5`, owner `2 3^2 2^5 . 2.3 .` not listed) and
k = 7 (b59 `. 2^3.3^2 . 2 3 2^2 .`). See 4.8.

### 6.2 Not yet made

In the order I would make them.

3a. **Pruning of owners (4.8)**: with every site passing k - 1 the
   rule loses nothing by construction (a pruned pattern's own run is
   dead, and no other run is removed), so there is nothing to check
   until a site is tightened. For each tightened site: model it in
   `wcheck.c` (with `acheck`'s completion test as the stand-in for
   pcoul's class-level one) and show that `ocheck` finds no live run
   left unanswered. Better still, test it against real pcoul once
   there is C (check 7).
4. **Folds for odd p.** `update_chinese()` and `update_residues()`
   are written generally but only p = 2 produces a fold today.
5. **How much of a run is shared.** For D(96,8) and D(48,10) at
   production options: from `-a` output, for each batch, a and s_min;
   weight by a cost proxy. Appendix A bounds the gain per walk; this
   would give it per run, and say how wide the reach really gets.
6. **The S3 site list**: every place in coul.c that prunes on a
   position.
7. **End to end**, once there is C: solutions under `-X` with and
   without the feature over a grid, and with recovery from random log
   points; shown able to fail. With the planner, its random-plan test
   (`-dJr`) with splitting and outside allocation among the tactics.

Also made earlier, now superseded: `ucheck` checks the first draft's
k + 1 pieces for one prime at a time (770 cases, 13.1 million anchors,
no failure; fails without the "more outside" pieces).


## 7. Order of work

Decided: the bulk of the work comes after the planner exists.

Proposed, **[hv]**:

- Now, or whenever convenient: checks 1 to 5 of section 6, and this
  document revised into an implementable design from their results.
- The layout refactor (positions and a range of runs per node,
  feature absent, identical logs) is of the same kind as pctul stages
  0 to 2 and touches the same functions. Before the planner it costs
  one more rebase of calibrate; after, it must also convert the
  planner's own loops over positions. hv has not yet said which.
- After planner stage 3: owners and non-owners at batch completion,
  with every owner split to single runs (proves the assignment of
  runs with nothing shared); then shared walks; then allocation
  outside the shared window as a costed tactic.


## 8. The planner

- **Tactics.** Splitting a range of runs (4.6) and allocating outside
  the shared window (4.5) enter as tactics with prices. The second is
  "split off the runs that lack position vi, then loop at vi".
- **Nothing at run level is needed** for correctness: which batch
  owns which runs is by rule. A run-level "feature off" is splitting
  every owner to single runs.
- **The walk price** depends on the range of runs and on how fast it
  narrows (4.7); it is not today's price.
- **What the planner's prices must not assume**: that positions
  0 .. k-1 are the positions of a node; that every position can take
  an allocation at no cost beyond the loop; that a node's children
  answer for the same runs as the node; that v_0 is d.
- **Recovery** replays splits from the log (P3).
- **Scoreboard**: add the pairs of appendix A as shards.


## 9. pctul and the other types

- The feature needs moving d by a constant to map one run's values
  onto another's. True for type o (by 1) and type a (by n); false for
  type r (targets differ by position) and type t. pcrul and pctul
  refuse it. pcaul is possible but not designed here.
- pctul keeps `k` as the positions of a run and adds `true_k`; this
  design must not change `k` either.
- Both designs want a batch's residue class from one function
  (`batch_resclass()`, on master since pctul stage 2, with
  `apply_resclass()` to combine it with a node); the folds of 4.4
  must go through it.
- pctul stage 0 made `insert_forced()` take powers from `bp->x[]`
  (on master); recovery here will depend on that.
- pctul's non-goals (a stride sieve; interleaving trial division
  across values) are independent. The second overlaps 4.7: both want
  the multi-tau tests to choose their order across values.


## 10. Risks

1. **A hole in who answers for what.** Check 1 found a second hole
   (4.4, invalid entering positions); checks 1 and 2 confirm the
   corrected rule, with and without tails, for TYPE_o.
2. **A prune that uses a position some run lacks** (S3). One missed
   site loses solutions of some runs only, rarely. Check 3 found
   that pcoul's existing batch pruning is such a site (4.8).
3. **Tails.** Checked (6.1); they add limits that are known only per
   candidate, which the walk and the planner must handle (4.3).
4. **The gain is inferred.** A node cannot freely allocate outside
   its shared window, and with a wide reach the shared window is
   small. Check 5, then a measurement on the first shared walks.
5. **The walk of 4.7 is new machinery** in the hottest code.
6. **Recovery**: a new kind of level, and patterns wider than k.


## 11. Open questions for hv

1. Whether a batch wholly left to its owner takes an id (4.2).
2. Which treatment of tails (4.3): all three are sound (6.1), so it
   is a choice of cost, and could be left to the planner.
3. The layout refactor before or after the planner (section 7).
4. Pattern syntax for a narrow batch and its reach, and for a split.
5. Whether the part a non-owner searches should try to share (4.4).

Settled: general width from the start; no restriction on k; no parity
setting; batch order and ids as now; owners shown as narrow batches;
skipping by rule and choices in place; bulk of the work after the
planner; no migration of runs in progress; pruning of an owner
narrows its range instead of dropping it, at the sites where pruning
happens now (4.8); runs are separated at a square or completed value
outside the shared window (4.8).


## Appendix A: measurements

Throwaway instrumentation over master daa8f4a (ovstat-ovdump.patch),
sandbox CPU, hv's production options.

Bound from the walks. m is the number of windows moved by one that
the forced structure allows for a walk's class. "Pairs" assumes walk
time halves wherever m >= 2; "all" divides it by m. Both are upper
bounds: they assume the other windows reach the same leaf.

| sample | walk share | m | pairs | all |
|---|---|---|---|---|
| D(96,8) b240028, first 420s | 93% | 4 | 1.87x | 3.3x |
| D(96,8) b240012 on, 280s | 89% | 2 to 8 | 1.81x | 3.0x |
| D(48,10) b700934-700946 | 76% | 4 or 10 | 1.61x | 2.5x |
| D(48,10) b700718 on, 300s | 73% | 2 to 10 | 1.57x | 2.6x |
| D(96,8) first 60s of the run | 73% | 2 | 1.57x | 1.57x |
| D(48,10) first 60s of the run | 49% | 4 to 10 | about 1.3x | 1.75x |
| D(12,7) complete | 92% | 3 to 7 | about 1.8x | 3.8x |
| D(20,6) complete from 1e22 | 39% | 1 or 2 | 1.12x | 1.12x |

Candidates in common: every candidate a linear `walk_v()` sent to the
tau tests, sampled consistently, for a batch and the one a place
along.

| pair | shared | duplicated test time | bound |
|---|---|---|---|
| D(96,8) b240021, b181320 | 95.7% of A, 91.9% of B | 46.3% | 1.86x |
| D(48,10) b700946, b564169 | 100% of both | 49.7% | 1.99x |
| D(96,8) b240013, b181320 | 8.2% of A, 0.2% of B | 0.2% | none |

In the first pair 99 percent of shared candidates failed at the same
shared position in both; in the second all did, and the two searches
had 335874 and 330345 recursions and walk steps equal to 1 part in
a million. The third is a batch with 7 at both ends against the batch
that contains it: a case of 4.4.
