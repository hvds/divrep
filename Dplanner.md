# pcoul planner: one costed decision mechanism

Design for implementation. Written against branch `calibrate` at
d4afd1c (2026-11-13). Function and option names are as found there;
line numbers are deliberately not given.

Status: revised 2026-11-13 after hv's first review; his decisions are
recorded where they apply, marked "Decided". Items marked **[hv]**
still need his decision before the stage that depends on them. Items
marked **[verify]** are my reading of the code and must be checked
before being relied on.

Since this was written, stages 0 to 2 of the pctul design (Dpctul.md)
went to master (5a553ae..f98cbb5), and calibrate has been rebased over
them (2026-11-17, tip e5efc12). Names in calibrate code are as at
d4afd1c, with the interface changes listed in Dpctul.md 9.1. Values
are written as v_i = TYPE_MULT(i).d + TYPE_OFFSET(i), with the sites
going through `dtov()`, `vtod()`, `calc_o()`, `calc_qq()` and
`TYPE_RES()`; calibrate's estimators in doubles use `dtov_d()`
(coulint.h) for the greatest v_i. The price hooks of this design must
be written in those terms. Dpctul.md 9.2 lists what is still open:
the estimators that size a value at position i as zmax / q_i, where
for pctul it is nearer TYPE_MULT(i).zmax / q_i.


## 0. Before starting

Read, in this order:

1. `CLAUDE.md` (the standard: a run is a proof).
2. `.agents/skills/divrep-conventions/SKILL.md` (code, comment and
   commit style; follow it exactly).
3. `.agents/skills/pcoul-internals/SKILL.md` (vocabulary: node, act,
   action, batch, tail, midp, dis, caps, "What makes a batch cheap").
4. `.agents/skills/pcoul-calibration/SKILL.md` (everything measured so
   far; "Tried and dropped" and "Methodology lessons" in particular).

Points where this work departs from, or adds to, those documents:

- `CLAUDE.md` says to work from master and leave calibrate alone. This
  work is the exception. Decided: it goes on a new branch `planner`,
  built over calibrate. The delivery rules of `CLAUDE.md` otherwise
  apply.
- New option letters, new log line codes and any change to progress
  line syntax are hv's decisions. Those already decided are given
  below; for any other, propose a spelling and flag it.
- hv runs anything needing hours of CPU himself. Design each
  measurement so that the long part is a single command line he can
  run, and report what you need back from it.


## 1. The problem

The calibration work set out to choose pcoul's speed options (-f, -j,
-g, -W) automatically. It has made many cases much faster, but by
adding mechanisms, each behind an option of its own:

| option | kind | what it is |
|---|---|---|
| -g, -G | knob | gain: walk or recurse at the gate |
| -j<n>, -js | knob | strategy: position to allocate at next |
| -f<n> | knob | which forced primes get explicit batches |
| -W<w>, -Wx | knob | sweep threshold, per run |
| -k<b> | knob | bound of the odd-power pass in one-square batches |
| -K<c> | knob | positions -k keeps that it would pass over |
| -P | knob | cap on the limits of loops |
| -ja1 | switch | gate decided by cost (replaces -g) |
| -ja2 | switch | position decided by cost (replaces -j, partly) |
| -ka | switch | -k, -W, -K chosen per one-square batch |
| -Wa<d> | switch | per-power -W bounds chosen per batch by estimate |
| -Wf<c> | switch + knob | per-power -W bounds per batch by fitted formula |
| -Wl<d> | knob | sweep d levels below the batch |
| -Wh, -Wha, -Whp, -Whv | switch | sweep where it would flip the gate |

A knob needs a value from the user. A switch means "pcoul decides
this sub-decision itself". The switches are the automatic choosers
the project wanted; they stayed options because nothing says when one
is good enough to become the default, and because each was built with
its own estimator:

| chooser | estimator | how it prices what lies below |
|---|---|---|
| gate (-ja1) | `gr_walk()`, `gq_walk()` | closed form, one level, every child walks, scaled by `GR_RSCALE` or a learnt ratio |
| position (-ja2) | `ja_cost()` | the same per x of each position, corrected by ratios learnt by size band (`ja_rsize()`) |
| position, study only (-dJe) | `ja_cost2()` | two levels: sampled children applied for real, each the cheaper of walking and its best position |
| batch sweep (-Wa) | `wa_node()` | real allocations to depth d, strategy's position, gate's choice, sampled children |
| batch sweep (-Wf) | `wf_plan()` | formula fitted to D(4p,k), D(8p,k) |
| node sweep (-Whp) | `ja_wsweep()` | closed form saving against the gate |
| one-square batch (-ka) | `ke_batch()` | abstract tree (`t_kenode`), its own position rule, from `zmax_given` |
| 6X or -k | `ke_6x()` | closed form plus `ke_cost()` |

Five ways of pricing a subtree, which do not agree with each other,
and no way to price a whole run under given options. That last gap is
why the run-level options (-f, the strategy family, highpow) cannot
be chosen at all.


## 2. Goal

1. One function prices any subtree: `plan_cost(node)`. Every chooser
   is that function restricted to the tactics available at one
   kind of node. The batch is not special; planning applies at any
   node, from the root (before forced primes are complete) to the
   deepest gate.
2. A new idea enters as a tactic action with a price, never as a
   new decision point with its own model or option.
3. A scoreboard measures how far automatic choice is from the best
   known choice, and how far predictions are from outcomes, by level
   of the tree. A switch whose chooser passes the scoreboard becomes
   the default; its knob remains only as an override.
4. End state: `pcoul -x<max> n k` runs near-optimally with no speed
   options. Every knob in the table above still works, pinning its
   decision; every switch is gone.

Non-goals: a batch harness (to-do item 7 in the calibration skill),
changes to the cost table's format beyond what a stage needs, and any
change to what a run covers.


## 3. Principles

P1. **A run is a proof.** The planner only chooses among actions each
    of which, with the caps and disallowed positions it sets, covers
    everything below its node. The coverage argument belongs to the
    action, as now. The planner never weakens it.

P2. **Costs counted, not timed.** Decisions depend only on counted
    work priced from the cost table, so identical runs decide
    identically. (See "Costs counted, not timed" in the skill, and the
    D(60,4) 1-in-7 slow run that timing caused.)

P3. **Recovery replays; it never re-decides.** Any decision that
    changes what is searched below a node must be readable from the
    log before that decision kind is enabled. Today: 315 lines for
    positions chosen against the strategy, 203-line tags for -ka,
    316 lines for what was learnt, the progress-line suffix for
    A_MIDP, A_6X and A_FLIP.

P4. **One price per tactic kind.** The cost of a kind of work is
    computed in one function, used by every decision that involves it
    and by the report (-ap). (kplan's fate, in "Tried and dropped", is
    the warning: a second implementation of an estimate drifts within
    days.)

P5. **Effort follows stake.** Planning effort at a node is bounded by
    a small fraction of that node's estimated cost. Cheap nodes get a
    table lookup; expensive ones get lookahead. No fixed depths.

P6. **Rank, do not predict.** A decision needs the tactics in the
    right order, not their absolute costs. Where two estimates share
    an error (a ratio common to the node), it cancels; keep it shared
    (see the `ja_rsize()` finding: keying the correction by position
    fitted as well but chose worse).

P7. **Bias matters more than spread.** A subtree's price is a sum
    over many children. Random error averages out; bias compounds
    with height. Track bias per level.

P8. **Cost it; do not rule on it.** Prefer a costed choice to a rule
    based on tau or shape. A rule is acceptable only as a prior, a
    tie-break, or a search bound for the costing.

P9. **No behaviour change without a measurement.** Each stage states
    what must stay identical and what must improve, on named runs.

P10. **One process, one thread.** The planner never forks, starts a
    thread or runs another program. hv controls the load on the
    machine by the number of pcoul processes he starts; planning is
    work inside the one process that asked for it.


## 4. The model

### 4.1 Cost of a node

A node is the state after the allocations so far: `nodes[l]` with its
aq, rq, caps (`t_node.cap`, per position and power), disallowed
positions (`t_node.dis`), squares fixed, and the values' remaining
taus. The cost of a node is

    cost(N) = min over tactics C available at N of price(C, N)

    price(C, N) = own(C, N) + sum over children M of C at N: cost(M)

`own` is the work the action itself does at N: primes tried and
rejected, setups, a walk's iterations and tests. The children are the
nodes the action creates. The sum is an expectation, taken exactly
for a few children and by sampling and integration over prime density
for the rest (4.5).

Units: seconds of `work_clock()` at the reference clock, as the cost
table has them.

### 4.2 Tactics

A tactic is one way of covering everything below N. (Not to be confused
with a candidate, which keeps its existing meaning: a value found
that may be a solution, as on a 202 line.)

| tactic | covers N by | exists today as |
|---|---|---|
| WALK | `walk_v(N)` (linear, one fixed power, or Pell) | `CH_WALK`, the gate saying walk |
| LOOP(vi) | for each x of t_i in order: a loop of p^{x-1} at v_i, or `walk_1_set()`, or a flip; a walk of N ends it | `CH_UNFORCED` with the gate per x |
| SWEEP(w[]) then C' | `walk_midp()` above bounds w[], then tactic C' at N under those caps | -W, -Wl, -Wh, -Wa, -Wf |
| PASS(b, keep) then C' | -k's odd-power pass to b at positions `at`, then C' | -k, -K, -ka |
| SIX | `walk_6x()` | `CH_6X`, `ke_prefer_6x()` |
| FORCED | the batches of the next forced prime | `CH_FORCED` (no choice today) |

Notes.

- LOOP(vi) is one tactic per allowed position, not one per
  strategy. A strategy is then only (a) the order in which positions
  are priced, so that a good incumbent is found early, and (b) the
  answer where planning is not worth its cost (4.6).
- Within LOOP(vi) the x are fixed in order (`divisors[t].div[]`,
  `done_in_reverse()`, `start_p()`); the order is part of the
  coverage argument and is not a choice. For each x the price is the
  cheaper of "loop over this x" and "walk N now", exactly as
  `prep_unforced_x()` decides it. That inner choice is the gate.
- SWEEP and PASS are prefixes: they do some work, change the caps or
  the disallowed set, and leave N to be covered by another tactic.
  Their price is own + cost(N under the new caps). So a sweep bound
  is chosen by pricing N with and without the cap: there is no
  separate sweep model.
- A flip (`run_flip_pqsq()`) and `walk_1_set()` are parts of LOOP(vi)
  for particular x, as `classify_x()` returns them. They get `own`
  prices of their own inside the LOOP price. The code notes (in
  `limit_unforced_x()`'s comment) that `walk_1_set()` is taken before
  the gate and never weighed against a walk; the LOOP price should
  weigh it.
- Pell (`have_square > 1`) is WALK with a near-zero price, as
  `wa_walk()` has it. Deferring it (-jp) is not a planning choice.

### 4.3 The price hook

**Per-action hook, with one adjustment.** `action_ops[]` in coul.c is
indexed by `e_action`. Two things do not fit it directly:

1. Walking is not an action: no act is made for it.
2. A_UNFORCED covers two decisions: which position (per node) and
   walk or loop (per x).

So the table that carries prices is indexed by tactic kind, and
each action that a tactic starts points at the same function:

```c
/* The kinds of tactic the planner can choose between at a node; see
 * plan_cost().
 */
typedef enum {
    TC_WALK = 0,
    TC_LOOP,
    TC_SWEEP,
    TC_PASS,
    TC_SIX,
    TC_FORCED,

    TC_NONE         /* none of the above; also the number of kinds */
} e_tactic;

typedef struct s_tactic {
    e_tactic kind;
    uint vi;        /* TC_LOOP: the position */
    ulong *w;       /* TC_SWEEP: the caps, cap_size() entries */
    ulong b;        /* TC_PASS: the bound */
    uint keep;      /* TC_PASS: the count of -K */
} t_tactic;

/* What the planner is asked: see plan_cost(). */
typedef struct s_pctx {
    double bound;   /* give up (HUGE_VAL) once a price passes this */
    uint depth;     /* levels of real lookahead left */
    const t_psample *sample;    /* how loops' children are sampled */
    t_pparts *parts;            /* if set, what the price is made of */
    ulong spent;    /* children costed so far, for the effort budget */
    ulong allow;    /* children that may be costed */
} t_pctx;

/* The price of covering the node at np by tac: its own work and all
 * below it. Returns HUGE_VAL once past px->bound, and PRICE_BLIND if
 * the model cannot price it.
 */
typedef double (*t_price_op)(
    t_node *np, const t_tactic *tac, t_pctx *px
);
```

`t_psample` is today's `t_wasample` and `t_pparts` today's `t_keparts`,
renamed as they become common to every price.

`plan_ops[TC_NONE]` in coulplan.c holds `{ price, available }` per
kind, where `available(np, out[])` lists the tactics of that
kind at a node (for TC_LOOP: one per position not in `np->dis`).
Decided: prices live in `plan_ops[]`, and `action_ops[]` stays as it
is on master. A price belongs in `action_ops[]` only if action kinds
and tactics correspond one to one, and they do not (walking; the two
decisions inside A_UNFORCED; SWEEP and PASS as prefixes), nor can
they be relied on to in future.

The planner:

```c
/* The estimated cost of everything below the node at np, and in *best
 * the tactic that gives it. Tactics are priced in the order
 * their kinds list them, each against the best so far as its bound.
 */
double plan_cost(t_node *np, t_pctx *px, t_tactic *best);
```

`plan_cost()` and the price hooks are mutually recursive: a LOOP
price costs its sampled children by `plan_cost(child)` with
`px->depth - 1`. At depth 0 a LOOP is priced in closed form (4.4).

`PRICE_BLIND` replaces `ja_cost()`'s `*blind`: a tactic the model
cannot price is never chosen by cost; if the fallback strategy would
choose it, the strategy's choice stands (as now).

### 4.4 The closure at depth 0

At depth 0 a loop's children cannot be looked at, so the loop is
priced as today: `gr_recurse()` (no square) or `gq_recurse()` (one
square), "every child walks", times the ratio learnt for its part and
size band (`ja_rpart()`, `ja_rsize()`), floored at the loop's own
cost (`ja_floored()`).

The learnt ratio is defined as actual cost over the depth-0 estimate.
Keep that definition whatever depth was used to choose: at each
choice, record the depth-0 estimate of the x chosen (`ja_cx[]`) and
learn from it, as `ja_learnx()` does. Then the ratios keep one
meaning, and lookahead and learning do not contaminate each other.

Walk prices: `wa_walk()` is the model (Pell near zero; one square by
`gq_wcost()`; linear by the per-level learnt cost per iteration, and
from the cost table via `walk_v_price_prep()`/`walk_v_iprice()` until
a level has samples). That becomes the TC_WALK price.

### 4.5 Children: exact, sampled, integrated

`wa_loop()` and `ja_e2loop()` are the same method with different
constants: the first few primes applied for real and costed, then a
few points spread geometrically over the rest, a short run of primes
at each, summed by `gr_seg()`. Make that one function,
`plan_loop()`, with the sampling spec (`t_psample`: exact, pts, run)
from the context. `wa_coarse` and `wa_fine`, and the "settle a near
tie finely" rule (`WA_TIE`), carry over as they are.

Applying a child for real means `apply_single()` on the scratch
levels above np. One helper pair owns the discipline, which the
existing code applies piecemeal:

- save and restore `cc` (planning is not search work: `ja_e2one()`);
- save and restore the act at np->level + 1 (`wa_node()`);
- restore `cur_vlevel[vi]` after each child;
- leave `np->cap`, `np->wfloor`, `np->dis` as found
  (`sweep_estimate()`);
- no log or screen output, no `candidate()`, no walk, no learning.

Today `wa_plan()` saves and restores `cc` around a whole plan and
`ja_e2one()` around each child; the helper pair replaces both.

The planner counts its own work (positions priced, children applied)
in new `t_cc` fields, priced like anything else and reported on the
369 line apart from the search's cost. Without that, counted cost
flatters lookahead: the dropped -ja3 experiment improved counted cost
by 10% while CPU time rose 28%.

### 4.6 Effort follows stake

Existing thresholds are all instances of P5 with hand-set constants:
`JA_MIN_WALK` (100us: below it the strategy's choice stands),
`KE_PLAN_MIN` (10ms: below it a batch is not planned), `WA_DEPTH` (4),
the -ja3 experiment's 10ms threshold and 8 children per position.

Replace them by one rule. Let S be the stake at a node: the best
price known so far (initially the TC_WALK price). The planner may
spend at most `PLAN_FRAC * S` there, in counted planning work:

    px->allow = PLAN_FRAC * S / (cost of costing one child)

- S below `PLAN_MIN`: no planning. The fallback strategy's position,
  the depth-0 gate. (Today's JA_MIN_WALK behaviour.)
- Enough for every position at depth 0: today's -ja2.
- More: depth 1 for the positions still in contention after depth 0
  (within a factor of the best; the -ja3 data says the overrides that
  paid were not near-ties, so the factor must be generous, 1.5 lost
  the gain), coarse sampling.
- More still: deepen by one level at a time, and sample finely where
  two tactics are within `WA_TIE`.

The planner stops deepening when `px->spent` reaches `px->allow`.
Counts, not clock readings, so P2 holds.

Starting values: `PLAN_FRAC` 0.01, `PLAN_MIN` 100us. Both are to be
fitted on the scoreboard, once; they are constants, not options.
Decided: bounding planning cost as a share of the run is acceptable,
subject to the progress requirement of 4.10.

### 4.7 Plan inheritance

Sibling nodes (children of one loop) differ only in p, and nearby
siblings have the same shape and nearly the same size. The -ja3 data:
reusing a choice for siblings of the same shape and size band turned
+2-4% CPU into -2.4% at the same counted gain.

So a decision made at a child is cached in the parent's act, keyed by
the child's size band (`ja_band()` of its walk price) and by which
tactic set it had (its `dis` generation, squares fixed, caps
generation). A later sibling with the same key takes the cached
tactic without pricing. The cache is cleared when the loop moves
to another x and when the act ends.

What is inherited is the tactic (position, sweep bounds as
multiples of the node's own limit, pass bound), not the price.

A reused choice is logged like a fresh one (P3).

### 4.8 zmax

- Decisions made once per batch and logged (203 tags) may use the
  current zmax.
- A decision that recovery must reproduce without a log record must
  use `zmax_given` (as the `ke_` code does). Prefer logging.
- A candidate found (a 202 line) lowers zmax mid-run. As now, a
  choice to recurse stands
  until unwinding removes the level and only its limit falls (to-do
  item 9). The plan cache must be keyed so that a lower zmax, which
  changes the size band, simply misses.

### 4.9 Correctness test: any plan gives the same answer

P1 says every choice the planner can make is a complete search. That
is testable. Add a debug mode, `-dJr<seed>` (VERBOSE builds; -dJe,
-dJs, -dJb, -dJw and -dJ<n> are taken, -dJr is free), that chooses
pseudo-randomly, from the seed, among the
tactics available at each node, ignoring prices. Then for a set of
small (n, k, -x) with -X:

- every seed reports the same set of solutions as master with no
  options;
- recovery from random log points, under each seed, reports the same.

This tests the tactics' coverage and the recovery records
independently of the cost model, and it will find holes that a
cost-driven run would visit only rarely. Build it in stage 1 and
extend it as each tactic kind is added. It belongs in the soak
tests (env variable to enable), with a short version in dtest.

### 4.10 Progress while planning

A share of a very long run can itself be hours or days. Planning for
that long with nothing shown is not acceptable.

Required: wherever the planner can run for long (`plan_run()`, the
bound searches of 5.3 and 5.4 at a large node, deep lookahead), its
loops check `need_work` as the search's loops do, and when the
display timer has fired (`need_diag`) show a progress line on screen
through the diag mechanism. The line says that this is planning, for
which node (as the search would show it), which tactic and bound are
being priced, and how far through it is (settings or batches done of
how many, in `plan_run()`).

Not required at this stage, but wanted if it can be done: progress
logged so that an interrupted plan can be resumed. Until then:

- nothing the planner writes to the log may be read by recovery as
  search progress, so planning writes no 305 line; if it logs at all
  (`need_log`), it uses a code of its own; **[hv]**
- an interrupted plan is simply made again on recovery, which is safe
  because nothing below the node has been searched yet (and for
  `plan_run()`, nothing at all: see the 002 line in 5.7).

Planning is deterministic (P2), so replanning after an interruption
reaches the same choice, given the same learnt state (the 316 line).


## 5. The decisions, mapped

For each: where it is made now, what it becomes, and what is new.

### 5.1 Walk or recurse (the gate, -g)

Now: `gate_walk()` computes the gain test, then `ja_gate()` replaces
the answer under -ja or at the square under -k. Becomes: inside the
TC_LOOP price, per x, TC_WALK's price against the loop's. `ja_gate()`
calls the same two prices with depth 0. New: nothing at first; with
budget, the gate at a large node may use depth 1 (to-do item 3).

With a planner on, -g and -G are read only where the planner does not
decide. Given explicitly, they pin the gate (the planner then prices
with the gain's answer, as -ap already prices a user's -k and -W).

### 5.2 Position (-j)

Now: `best_v()` by strategy; `ja_choose()` under -ja2 for nodes with
no square, or one square in a -k batch, not under STRATEGY_6X or
-js. Becomes: `plan_cost()` over the TC_LOOP tactics. New: depth 1
where budget allows (4.6), which the -dJe data says orders positions
right 85% of the time against 66%.

Two things the skill records as still tied to the strategy:

- Nodes with a square fixed outside -k batches: the strategy chooses,
  and -j2 there costs 2-8x on D(18,4), D(90,3), D(60,4), D(120,4).
  `gq_recurse()` prices such loops only at positions `gq_costable()`
  accepts. Extending the one-square price to every position removes
  the exception; until then those tactics are PRICE_BLIND and
  the fallback strategy must not be -j2-like there. Stage 5.
- highpow: only -j4 and -js let p^{2^x-1} be allocated, and without
  it n = 2^x.m cases take 3-600x longer. Decided: it is a run-level
  choice (5.7) in this design. hv's account: highpow does not, as far
  as he knows, change the order of the existing powers, but the order
  in which the p^{2^m} are allocated follows different logic from the
  other powers, and several places in initialisation act differently
  under it. Varying it during a run would need every such place
  replaced by the conservative choice, or two parallel structures
  initialised where that costs less at run time, and a detailed
  analysis of what else could break. That analysis is not part of
  stages 0-6. It also bears on 5.7: pricing a run both ways needs the
  initialisation done both ways in one process.

### 5.3 Sweeps (-W and its family)

Now: at a complete batch (`sweep_batch()`), d levels below it (-Wl,
`sweep_mid()`), or where the gate would flip (-Wh, `gate_sweep()`);
bounds from the option, from -ka's grid, from `wa_plan()` or from
`wf_plan()`. A swept node records `wfloor` and is not swept again.

Becomes: TC_SWEEP(w[]) is a tactic at any node not already swept
whose stake passes the effort rule. Its price:

    own  = sweep_own(N, w[])       primes tried above the bounds, and
                                   the walks of those applied
    rest = plan_cost(N with caps w[])

`sweep_estimate()` is already this shape for the batch node (entries
from `prep_midp()`, each priced by `wa_entry()`, plus `wa_subtree()`);
generalise it to any node.

The bounds are searched as `wa_power()` does: per power, least reach
first, a geometric grid from the top down, stopping when two in a row
are no better. `wf_plan()`'s formula supplies the first grid point
and a window around it (P8: a prior, not the decision), which cuts
the search to a few evaluations. If the formula's point is the best
of its window on the scoreboard everywhere, the search can shrink to
one evaluation, but the decision is still by price.

Caps are per position and power (`cap_ix(vi, x)`), so bounds can vary
by position as hv wants; the search space grows, so vary by position
only where the positions' limits differ by more than a factor (start
with: one bound per power, scaled per position by its own limit).

Recovery: a node sweep must be readable from the log. The A_MIDP
suffix shows that a sweep is in progress; the bounds it used must
also be recoverable. -Wa and -ka put the batch's bounds in 203 tags
(`kern_tags()`, `kern_restore()`). Decided: a sweep below the batch
uses the same ` W(...)` mark as one at the batch. The mark holds
(p, x, vi) and not the bounds, which today come from the option or
the 203 tags; a planned sweep's bounds are chosen at the node, so
they must also reach the log, in the mark or in a line written as the
sweep starts. **[hv]** approves the form once the implementer can
show what recovery needs.

Retires: -Wl, -Wh, -Wha, -Whp, -Whv, -Wa, -Wf, once the tactic
matches or beats each on the scoreboard. -W<w> and -Wx remain as
knobs: given, they pin the batch sweep and the planner adds none.

### 5.4 One-square batches (-k, -K, 6X)

Now: `kern_plan()` runs a triple loop over keep, a -W grid and a -k
grid, pricing each by `ke_batch()`, an abstract walk of the tree in
doubles with its own position rule (`ke_best()`), against `ke_plain()`
and `ke_6x()`.

Becomes: TC_PASS(b, keep) and TC_SIX are tactics at the batch
node; PASS's price is the pass's own cost (`ke_npass()` primes at
`KE_PELL`) plus `plan_cost()` of the batch node with the pass's
disallowed set and x-bounds (`kern_sets()`, `kern_xbounds()`). The
subtree is then priced by the same function as every other subtree.

This is the riskiest replacement. `ke_batch()` is fast because it
never touches the real stack; the unified price applies real
allocations. It also models things the others do not (the square
opening and closing, `ke_sqopen()`). So:

- First, make `ke_batch()` the TC_PASS price as it stands (stage 1).
- Then build the unified one-square price beside it and compare both
  with actual costs on D(18,5), D(126,3), D(6p,5) batches (stage 5).
- Keep `ke_batch()` as the depth-0 closure for one-square nodes if
  the unified price cannot beat it at equal planning cost. That is
  consistent with the model: a closure is any cheap price used where
  lookahead is not affordable. What must go is its use as a parallel
  decision path.

-K's count becomes part of the PASS tactic's enumeration and
stops being an option when the planner is on. The known -ap gaps on
D(126,3) (the fixed "whole" guess where the table has no rows; the
`2^6 . 2.3^2` batches given neither a -k nor a 6X estimate) are bugs
to fix in this stage.

### 5.5 Forced layer (-f)

Now: `force_all` decides at startup, per forced prime, whether single
allocations get batches of their own or share a tail
(`prep_forcep()`, `keep_single`). No cost is involved.

Becomes, in two steps:

- Run level first (5.7): price the run under a few values of -f and
  take the cheapest.
- Later, per node: at a partial batch, "expand this prime's singles"
  against "take the tail" as two TC_FORCED tactics. This needs the
  forced tables to carry both forms. Not in this design's stages;
  noted so that stage 6's structure does not preclude it.

### 5.6 Above the batch (sq12-type actions)

The D(12,k) method (wiki "D(12,k) calculation") sweeps primes above a
threshold Z once for all patterns with a separate program (sq12), then
runs each pattern capped at Z. In planner terms that is TC_SWEEP at a
node above the complete batches: at a partial batch, or at level 0.

The price has the same shape as 5.3. What is missing is mechanism,
not costing:

- `walk_midp()` needs a complete batch below it today (item A made it
  walkable at any point below the batch; **[verify]** how far that
  reached on calibrate). Above the batch, each swept prime's child
  must still go through the remaining forced primes, so the sweep's
  children are nodes whose next action is A_FORCED.
- A run with no forced primes refuses -W at startup (the level-0
  dummy has no level above it). The same limit applies.
- `rest` is the cost of all batches below under the cap, which is the
  run-level sum of 5.7.

So this comes last (stage 7), and only after 5.7 gives the sum. It
needs a design pass of its own with hv once stages 1-6 show what the
planner can price. This document fixes only that it is a tactic of
the existing kind, priced by the existing recursion.

### 5.7 Run level

`plan_run()`: before the search starts, price the run under each of a
small set of run-level settings and choose the cheapest.

- Settings: -f in {0, the primes up to k} (pruned: forcing more
  primes only splits batches further); highpow on or off where n
  allows it; the fallback strategy. Each explicitly given option pins
  its dimension.
- Price of a run: the sum of `plan_cost(batch)` over its batches.
  Batches are enumerated as -a does. With many batches (D(96,8) has
  about 470k) price all of them at depth 0 with no planning budget,
  which is cheap, then re-price the heaviest ones, which carry most
  of the total, with the normal budget. This answers the brief's
  warning that sampling batches blind is unsafe: the cheap pass is
  the knowledge of which batches matter.
- **[verify]** that `prep_forcep()` and what depends on it can be
  rebuilt for another -f within one process. If not, make them so:
  that restructuring is then part of stage 6. Never price a setting
  in a child process (P10).
- The same sum, shown per batch, is -ap for every batch kind, and its
  total is a predicted run time, logged at the start and compared
  with the 367 line at the end.

Recovery: the 001 line is written before any work is done, so it
cannot hold what planning chose. Proposed (hv inclined to this, not
final): a separate 002 line, written when `plan_run()` has chosen,
holding the settings chosen in a form that is parsed strictly. A
recovered run takes them from there and does not choose again; a log
with a 001 line and no 002 line was interrupted while planning, and
plans again. **[hv]** for the line's format.


## 6. Options: the end state

- One planner switch during development: `-J` (hv inclined to this;
  the letter is free). It turns on every tactic the planner has
  absorbed so far, and implies what -ja2 implies today. -ja1 and
  -ja2 stay as they are until stage 3 passes, for comparison.
- Every knob still parses. Given, it pins that decision and the
  planner prices around it.
- Each switch in the section 1 table is removed in the stage that
  absorbs it, once the scoreboard criterion is met; until then the
  old path stays selectable so the two can be compared on one build.
- When the planner passes the scoreboard as a whole it becomes the
  default, with an option to turn it off.
- No new option may be added for a mechanism the planner could
  choose. A new mechanism arrives as a tactic kind or as a new
  parameter of one, with a price.


## 7. The scoreboard

### 7.1 What it measures

For each shard (a run short enough to repeat: one batch, a batch
range, or a small complete run):

1. **Regret**: CPU time of the planner's run over the best CPU time
   known for that shard under any options. CPU time, not counted
   cost, is the judge, because it includes planning.
2. **Calibration at the root**: predicted cost over actual counted
   cost (the 369 line), and over CPU time.
3. **Calibration by height**: for subtrees whose prediction was
   recorded, log(actual/predicted), summarised as mean (bias) and
   spread, grouped by height above the leaves and by size band.

### 7.2 Mechanism

- Prediction records. Under a new -dv bit, a node priced at more than
  a threshold writes its prediction when chosen and its counted cost
  when unwound. The -dv64 Y/Q/K records and the `ja_t0`/`ja_ew`
  fields already do this for -ja2 choices; extend them, do not add a
  parallel set.
- A file of shards, tracked in the repo: id, n, k, the arguments that
  define the shard (-x, -b or -I, -f where the shard needs it), the
  best known option string, its CPU time and counted cost, the build
  sha, the date. Runs never modify it (hv's rule for `timings`); a
  tool rewrites it on request.
- A driver in Perl, `evalplan`. It runs each shard under the planner
  build, one at a time (P10), reads the 367 and 369 lines and the
  prediction records, and prints one line per shard and a summary.
- Two sets of shards: a quick set (a couple of minutes in all, run
  for every commit) and a full set (hours; hv runs it). The criteria
  of 7.4 are judged on the full set.

### 7.3 Seed shards

All from runs already in the skill, with their best known times
there: the 29-run table under "Where -ja2 pays" (it has four
strategies under -ja1 and -ja2 for each); the D(96,8) batches b5,
b50, b5000, b350000 and D(48,10) b1, b7 at production zmax; the -Wa
set (D(12,7), D(12,8) -f5, D(20,6), D(28,7), D(20,5), D(28,5)); the
-ka set (D(18,5) batches, D(126,3) b0-b17); the -W table batches
(D(48,10) I and J, D(96,8) b1, D(24,12) b1).

Those are what happens to have been measured: they follow the shapes
each stage of calibration focused on, and are a seed only. The set
to build towards represents the whole problem space, without (for
now) spending most of its time in slow factorizations.

Shape is set largely by n mod 12 (with n = 2^m a special case), then
by the factorization signature of n. k has a much subtler effect,
except where k >= 4 forces a square. So the grid is class by
signature, with for each n one k below 4 and one at or above it
where a solution is known:

| n mod 12 | signatures to cover | examples |
|---|---|---|
| 2, 10 | 2p, 2p^2, 2pq | 10, 14, 22; 50, 98; 70, 110 |
| 4, 8 | 4p, 8p, 16p, 4p^2, 4pq | 20, 28, 44; 40, 56; 80; 100; 140 |
| 2^m | (special case) | 8, 16, 32, 64 |
| 6 | 6, 6p, 6p^2, 18, 54, 162 | 6; 30, 42, 66, 78; 150; 18, 54, 90, 126, 162 |
| 0 | 12, 24, 48, 96, 192; 36, 72, 108, 144; 60, 120 | as listed |

The examples are a proposal; **[hv]** to correct from knowledge of
which cases are tractable.

Two further groups, by hv's priorities:

- Short term: every remaining candidate of the proof rerun. hv
  supplies the list (the runs still flagged old); each contributes
  shards as it is reached.
- Medium term: the remaining cases for n < 100, n not 0 (mod 12):
  D(30,5), D(42,5), D(54,4), D(54,5), D(66,5), D(78,5), D(90,4),
  D(90,5), D(100,5), D(100,6), D(100,7). hv expects these to be more
  tractable than the high-k cases with 12 | n, though probably not
  without new optimization strategies. They cannot be run whole, so
  they contribute batches at production zmax, chosen from the cheap
  pricing pass of 5.7 once it exists and by hand before then.

The losing runs of the option races are in earlier chats and exported
files, not in the repo. Mining them into the shard file is a separate
task for hv to schedule; the format above is what they should land
in.

### 7.4 Criteria

Decided as a starting point; hv will revisit the numbers once there
are results to judge them by:

- To retire a switch: on every shard the planner's regret is no worse
  than the switch's own best setting by more than 3%, and the
  geometric mean is no worse.
- To make the planner the default: geometric-mean regret below 1.10
  and worst-case below 1.5 on the full set, and no shard slower than
  master with no options.


## 8. Stages

Each stage is a short series of commits, each working, each
explainable in its message. Each stage ends with `make dtest` clean,
the quick scoreboard run, and a note of what changed in it.

"Identical" below means: the same 367 counts (recurse, walk, walkc)
and the same solutions as before the stage, on the quick set, with
the same options. Times may differ.

### Stage 0: scoreboard and baseline

No change to what pcoul decides.

- Prediction records for the choices that exist (-ja2 positions, -ka
  batches, -Wa batches).
- Planning work counted in `t_cc` and shown on the 369 line.
- The shard file, seeded from 7.3, and the driver.
- Baseline tables: regret and calibration by height for the current
  switches.

Done when: the baseline reproduces the skill's figures to within
their stated noise, and hv has seen the tables.

### Stage 1: one interface, same decisions

- `e_tactic`, `t_tactic`, `t_pctx`, `plan_ops[]`, `plan_cost()`.
- Each existing estimator becomes a price hook or a closure, moved
  but not changed: `wa_walk()` to TC_WALK; `ja_cost()` to TC_LOOP at
  depth 0; `sweep_estimate()` to TC_SWEEP at the batch;
  `ke_batch()` to TC_PASS; `ke_6x()` to TC_SIX.
- `ja_choose()`, `ja_gate()`, `kern_plan()`, `wa_plan()` call
  `plan_cost()` or the hooks.
- The scratch discipline of 4.5 in one helper pair.
- The random-plan test of 4.9, for the tactics that exist.

Done when: identical on the quick and full sets under each existing
switch; random-plan test passes.

### Stage 2: one lookahead

- `plan_loop()` replaces `wa_loop()` and `ja_e2loop()`.
- TC_LOOP at depth d > 0 costs children by `plan_cost()`.
  `wa_node()` becomes `plan_cost()` with the tactic set restricted
  to the strategy's position (to reproduce -Wa) and `ja_cost2()`
  becomes TC_LOOP at depth 1.
- Learning keeps its depth-0 meaning (4.4).

Done when: identical under -Wa<d> and under -dJe's E records; no
decision yet uses depth > 0 except where -Wa did.

### Stage 3: effort and inheritance

- The effort rule (4.6) replaces `JA_MIN_WALK`, `KE_PLAN_MIN`,
  `WA_DEPTH` and the -dJe threshold.
- The plan cache (4.7).
- Positions chosen with lookahead where the budget allows.

Done when: on the quick and full sets, never slower than -ja2 beyond
noise, and faster on the shapes where the skill found the two-level
estimate to order positions better (n = 12, 36, 60, 100, 162).
`PLAN_FRAC` and `PLAN_MIN` fitted and recorded. First behaviour
change: review the regret table with hv before going on.

### Stage 4: sweeps anywhere below the batch

- TC_SWEEP available at any unswept node below the batch, bounds by
  the search of 5.3, per power and (where limits differ) per
  position.
- The log record for a node sweep, and its recovery, with tests in
  t10init style (recover from random log points).
- Random-plan test extended to sweeps.

Done when: matches or beats the best of -W, -Wf, -Wa, -Wl, -Wh on
every sweep shard (the D(4p,7), D(12,k), D(24,11), D(48,9) family in
particular). Then remove -Wl, -Wh*, -Wa, -Wf.

### Stage 5: one-square nodes

- A one-square LOOP price for every position (removes the
  `gq_costable()` exception of 5.2).
- TC_PASS and TC_SIX priced through `plan_cost()` for the subtree,
  compared with `ke_batch()` as in 5.4; keep whichever closure is
  better at equal cost.
- Fix the two -ap gaps on D(126,3).

Done when: matches or beats -ka on the -ka shards and on D(6p,5),
D(18,5); -j2 no longer costs 2-8x on D(18,4), D(90,3), D(60,4),
D(120,4). Then remove -ka. -K goes as soon as the planner's own
choice of the count does better than any fixed one, which hv expects
to be easy; it need not wait for the rest of this stage.

### Stage 6: the run

- -ap from `plan_cost()` for every batch, with a total.
- Predicted run cost logged at the start; compared at the end.
- `plan_run()` choosing -f, highpow and the fallback strategy.

Done when: predicted over actual is within a factor hv accepts on the
full set (propose: 0.5 to 2 for runs over 10s), and the run-level
choice matches the best known -f and -j family on every seed shard
that has them. Then the planner can be proposed as the default.

### Stage 7: above the batch, and defaults

- The design pass for 5.6 with hv, then TC_SWEEP at partial batches
  and at the root if the mechanism allows.
- Per-node TC_FORCED (5.5) if stage 6 shows -f matters enough.
- Planner on by default; -g, -j become overrides.


## 9. Risks

1. **The unified price is slower than the special ones.** `ke_batch()`
   and the closed forms exist because they are cheap. Mitigation:
   closures are part of the model (4.4, 5.4); the effort rule decides
   when lookahead is used. Stage 1 changes no costs.
2. **Compounding bias near the root.** The skill records the
   depth-0 estimate being wrong by factors of 250 at 1000s nodes, and
   the learnt ratios starting blind exactly where single choices cost
   most. Lookahead at high-stake nodes is the mitigation, and the
   by-height calibration table is how to see whether it works. If it
   does not, run-level choice (stage 6) fails first and visibly.
3. **Factoring-bound shapes.** Where the ladder dominates, prices
   rest on the G rows, which are rough above about 191 bits. Stage 6
   will show this as poor calibration on those shards; the fix is in
   the cost table, not the planner.
4. **Recovery.** Each new decision kind needs a log record (P3). The
   record formats are hv's to approve, and each needs random-point
   recovery tests before it is enabled.
5. **Reproducibility against the plan cache.** A cached choice
   depends on which sibling was planned first; that is deterministic
   within a run, but a recovered run starts with an empty cache.
   Since choices are logged and replayed, only choices made after
   recovery can differ, as with the 316 state today (the skill:
   2 of 9 recovered runs differed, by under 2%).
6. **Scope creep.** Stages 4 and 5 each replace code with measured
   wins. Do not replace a path until the scoreboard says the planner
   is at least as good there; keep both selectable until then.


## 10. Open questions for hv

Settled in the first review, and recorded above: the branch
(`planner`), `plan_ops[]`, -dJr, the ` W(...)` mark for sweeps below
the batch, highpow at run level, planning cost as a share of the run
with progress shown, `evalplan`, the 7.4 criteria as a starting
point, and -K going as soon as the planner does better.

Still open:

1. `-J` as the planner switch: hv is inclined to it, not final (6).
2. How a planned sweep's bounds reach the log (5.3).
3. The 002 line: whether to have it, and its format (5.7).
4. The example n in the 7.3 grid, and the list of remaining rerun
   candidates.
5. Whether planning progress should also be logged recoverably
   (4.10): wanted if possible, not required at this stage.
