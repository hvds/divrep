# pctul: TYPE_t (tauseq) in the pc?ul codebase

Design for implementation. Written against master at 5a553ae
(2026-11-14), with calibrate at 1183015 and the planner design
(Dplanner.md, 2026-11-13) read alongside. Function and option names
are as found on master; line numbers are deliberately not given.

Status: revised 2026-11-14 after hv's first review; his decisions are
recorded where they apply, marked "Decided". Items marked **[hv]**
still need his decision before the stage that depends on them. Items
marked **[verify]** are my reading of the code and must be checked
before being relied on.

Stages 0 to 2 are on master (5a553ae..f98cbb5, 2026-11-16/17),
and their record is in section 8 ("As done"). Stage 3 was written over
f98cbb5 (2026-11-17), delivered as patches; its record follows stage 3
in section 8. Where the code differs
from what is written below for those stages, the record says so; the
names in sections 4 and 5 are now those of the code.

What stands behind this document:

- The arithmetic of sections 4.4 to 4.6 was checked by brute force
  (section 4.11). The reference values of appendix A come from a sieve
  of tau that shares nothing with pc?ul.
- Every statement about the C code is from reading it. Nothing here
  was checked by running pc?ul: the sandbox this was written in has no
  GMP headers, so the programs could not be built.


## 0. Before starting

Read, in this order:

1. `CLAUDE.md` (the standard: a run is a proof).
2. `.agents/skills/divrep-conventions/SKILL.md` (code, comment and
   commit style; follow it exactly).
3. `.agents/skills/pcoul-internals/SKILL.md` (vocabulary: node, act,
   batch, primary, fold, tail, "Forced primes, batches, and the tail").
4. `lib/Type/TauSeq.pm`, for what the Perl code takes the sequence to
   be. Nothing else in the Perl tree is needed.

This work follows `CLAUDE.md` without exception: it is done from
master, and nothing is done on calibrate or on the planner branch.
Section 9 says what the planner work needs to know about it, and what
this work must leave alone for the planner's sake.

New log syntax, new line codes and the meaning of an option under
pctul are hv's decisions. Those this design needs are listed in
section 11; do not settle one by implementing it.


## 1. The problem

pc?ul searches for the least d such that tau(v_i) takes given values
at k values v_i that are functions of d. Three families are built
from one source by `-DTYPE_o`, `-DTYPE_a`, `-DTYPE_r`. The fourth, the
Perl type `TauSeq` ("t"), is named in the comment at the head of
coul.c and not supported:

    f(n, k) = the least d > 0 with tau(n + i.d) = tau(n), 0 <= i < k

The term i = 0 is n itself, so k - 1 values are searched for.

All four families are affine in d:

    v_i = a_i . d + c_i

| type | a_i | c_i | target tau | values |
|---|---|---|---|---|
| o | 1 | i | n | k |
| a | 1 | i.n | n | k |
| r | 1 | i | tau(n + i) | k |
| t | i + 1 | n | tau(n) | k - 1 |

For type t the table numbers the values from 0: position i holds
v_i = n + (i + 1).d. Section 4.1 says why.

Types o, a and r have a_i = 1, and the code assumes it throughout:
`TYPE_OFFSET(i)` is c_i, "v_0" is both the first value and the thing
searched for, and v_j - v_i is a constant. None of the three holds for
type t. What does hold is listed in 4.2, and it is enough: the
allocation of prime powers, the walks, the square and Pell machinery,
mintau, the caps, the log and recovery all carry over. One part has no
counterpart in pc[oar]ul and is new: the batches of a forced prime
(4.4 to 4.6).


## 2. Goal

1. New targets `pctul` and `dpctul`, built from the same sources with
   `-DTYPE_t`, whose runs are proofs to the standard of `CLAUDE.md`.
2. pc[oar]ul unchanged: after each stage that touches shared code,
   their logs are identical to those of the build before it (8.1).
3. No option, switch or build flag added for pctul. Where pctul has a
   choice that pc[oar]ul does not, this design fixes one rule and
   names the choice in section 9, for the planner to cost later.

Non-goals. Each of these may matter more to pctul's speed than
anything here, and each is its own piece of work:

- A stride sieve in `walk_v()`. For prime n the whole search is one
  batch and one walk (4.10), so a sieve over the walk index is where
  the time would go. It is independent of the type.
- Interleaving the trial-division bands of `tau_multi_prep()` across
  the values of a candidate (discussed 2026-11-10). Also independent
  of the type.
- Unforced tails for pctul (4.6, 9.3).
- Tactics or prices specific to type t in the planner (section 9).

hv does not expect to do serious work with pctul until the pcoul
reruns are near complete, and will want the sieve and the other
improvements then. So this design is to get a correct pctul into the
codebase; its speed on prime and semiprime n comes later.


## 3. Principles

T1. **A run is a proof.** Each batch of a forced prime states the
    exact power of that prime at every position, and the set of d it
    answers for. Its walks may test d outside that set; they may never
    leave out a d inside it.

T2. **One codebase, no type tests at the sites.** The differences
    live in three accessors (4.2) and one batch builder (4.5). A site
    that needs the multiplier writes it in; for pc[oar]ul the accessor
    is the constant 1 and the compiler removes the work. Where a
    branch is needed it is `if (TYPE_MULT(vi) != 1)`, not `#if`.

T3. **Identical logs for pc[oar]ul.** A stage that changes shared
    code is a refactor for them, and is shown to be one.

T4. **Fail loudly at what is not yet supported.** Each stage refuses,
    with `fail()` and a message that names what is missing, every case
    it does not cover. A pctul that silently mishandles a square is a
    false result; one that stops at it costs nothing.

T5. **The residue class of d is stored with the batch, not derived from its
    primary.** In pc[oar]ul the residue of v_0 follows from "p^e
    divides v_primary". In pctul it does not (4.5), so the batch
    carries what is needed to give it.


## 4. The model

### 4.1 Positions

`k` stays what it is everywhere in coul.c: the number of positions,
the size of `value[]`, the bound of every `vi` loop. Under TYPE_t that
is one less than the k of f(n, k), since the term n needs no search.
A new global holds the k the user gave, for the lines that echo it:

    uint true_k;     /* the k of f(n, k); k + 1 under TYPE_t, else k */

Position i of pctul is the value n + (i + 1).d. The alternative, a
position 0 that holds n and is complete from the start, was rejected:
`apply_batch()` treats a complete value as the end of its batch
(`terminal`), and every walk would have to pass over it.

Consequences, all under TYPE_t only:

- `main()` requires k >= 2 as given, sets `true_k`, then
  `k = true_k - 1`.
  The `MAXK` and `MAXK_KERN` tests apply to the positions.
- The lines 001, 200, 367, 500 and the 403 of `check_exceptions()`
  print or compare `true_k`. `setproctitle()` likewise.
- `report_211()` shows v = n + i.best for i = 0 up to true_k and beyond
  while the run continues to match, as it does now for the others.
- Patterns in 203, 305 and 315 lines, and in `-I`, have k entries: the
  first is for n + d.

Decided: the name is `true_k`, and logs show k - 1 positions.

### 4.2 Three relations

Everything the shared code needs from a type is in three relations.

Forward. v_i from d:

    v_i = a_i . d + c_i

Inverse. d from v_i, which can fail:

    d = (v_i - c_i) / a_i,  only if a_i divides v_i - c_i

Pair. For two positions the combination that does not depend on d:

    a_i . v_j - a_j . v_i = a_i . c_j - a_j . c_i

In code, beside `TYPE_OFFSET()` (on master that is in coul.c, with a
copy in coulvec.c; define all three once, in a header both include):

```c
/* v_i = TYPE_MULT(i) . d + TYPE_OFFSET(i), for the d searched for */
#if defined(TYPE_t)
    static inline uint TYPE_MULT(uint i) {
        return i + 1;
    }
    static inline uint TYPE_OFFSET(uint i) {
        return n;
    }
#else
    static inline uint TYPE_MULT(uint i) {
        return 1;
    }
    /* TYPE_OFFSET() as now */
#endif

/* The resultant of v_i and v_j as linear polynomials in d: with
 * a_i = TYPE_MULT(i), c_i = TYPE_OFFSET(i),
 *   a_i.v_j - a_j.v_i = a_i.c_j - a_j.c_i
 * for every d.
 */
static inline sint TYPE_RES(uint i, uint j) {
    return (sint)TYPE_MULT(i) * TYPE_OFFSET(j)
            - (sint)TYPE_MULT(j) * TYPE_OFFSET(i);
}
```

For types o and r `TYPE_RES(i, j)` is j - i, for type a n.(j - i);
for type t it is n.(i - j). An int holds it: with k positions,
|i - j| <= k - 1 <= 65 (MAXK), so for type t it needs only
n.(k - 1) <= INT_MAX, which allows n up to about 33 million whatever
k is. Decided: an int, with pctul failing at startup (stage 3) if
n.(k - 1) does not fit. The other types are far within range.
Any common factor of v_i and v_j divides it (generalising "gcd(d + i,
d + j) divides j - i"). It is computed from both positions, so does
not assume TYPE_RES(i + m, j + m) = TYPE_RES(i, j), though that holds
for all four types. (Named TYPE_PAIR() until review.)

Two helpers over mpz_t, used wherever a site now adds or subtracts
`TYPE_OFFSET(vi)`:

```c
/* Set v to v_i for the given d. */
static inline void dtov(mpz_t v, uint vi, mpz_t d);

/* Set d to the greatest d with v_i <= v. Returns TRUE if v_i is v
 * for that d, so that a caller can test d against a bound before
 * rejecting a v that no d gives.
 */
static inline bool vtod(mpz_t d, uint vi, mpz_t v);
```

(As done in stage 1. A first version left d unspecified when there
was none, which in the Pell branch of `walk_v()` skipped the test
against zmax, and so could walk on for ever.)

`dtov(v, vi, zmax)` is the greatest value v_i can take, which is
what most of the sites want (section 5).

### 4.3 What a node knows

A node holds (rq, aq) with d == rq (mod aq), and for each position
the product q_i of the prime powers allocated there. For pc[oar]ul
q_i divides aq and rq == -c_i (mod q_i). For any type:

    I1.  q_i divides a_i . aq
    I2.  q_i divides c_i + a_i . rq

and the walk over d = rq + aq.t has, at position i,

    v_i / q_i = o_i + t . qq_i
    o_i  = (c_i + a_i . rq) / q_i       (wv_o[i])
    qq_i = a_i . aq / q_i               (wv_qq[i])

I2 is what makes o_i an integer and I1 what makes qq_i one. With
those two definitions `walk_v()` needs no other change of substance:
its linear walk, its walk over the roots of a fixed square and its
checks of a Pell solution are all written in terms of o_i and qq_i.
A candidate is d itself: rq + aq.t.

The modulus that v_i is known to is a_i.aq, not aq. That is the one
idea to hold on to: wherever the code forms aq / q_i for a position,
type t needs a_i.aq / q_i.

Assert I1 and I2 in the DEBUG builds where `wv_o[]` and `wv_qq[]` are
formed. Section 4.11 says how far they were checked.

### 4.4 A prime against the values

Fix a prime p and write

    e   = the power of p in n
    f   = the power of p in d
    g_i = the power of p in a_i
    n'  = n / p^e

At position i the power of p in a_i.d is f + g_i, and so the power of
p in v_i = n + a_i.d is

    f + g_i        if f + g_i < e        ("low")
    e              if f + g_i > e        ("high")
    e or more      if f + g_i = e        ("critical")

At a critical position write a_i = p^{e-f}.a', d = p^f.d'. Then
v_i / p^e = n' + a'.d', with n' and a' prime to p, and p divides it
again only if d' == -n'/a' (mod p).

Three cases follow.

p does not divide n (e = 0). Then f = 0 is the only level with
critical positions: those with p not dividing a_i. Either p divides d
and p divides no v_i at all, or d lies in one of the p - 1 other
classes mod p and p divides exactly the v_i with
a_i == -n/d (mod p). For p <= true_k every such class holds at least
one position; for p > true_k at most one. So the primes p <= true_k are
forced, as in pcoul, and for each there is one batch more than pcoul
has: "p divides d", which fixes d mod p and uses none of tau.

p divides n and p >= true_k (so g_i = 0 everywhere). For f < e every
v_i has exactly p^f. For f >= e every v_i has p^e, and for f = e
exactly one position at most has more.

p divides n and p < true_k. As the last case, but the positions with
p dividing a_i run f + g_i ahead of the rest, so one level f can have
low, high and critical positions together.

**Which primes are forced under TYPE_t: every p <= true_k, and every p
dividing n, whatever its size.** `never_unforced(p)` is true for
p dividing n, as under TYPE_a, and `maxforce[i]` is true_k at every
position (pcoul has k there for n not divisible by 4), so that no
prime up to true_k is ever allocated outside its batch. An unforced
prime is then greater than every a_i, which 4.7 relies on. Note the
bound is true_k, one more than the positions: the prime true_k, if it
is one, divides d or exactly one value, and its batches say which.

p can be as large as n. `test_forcep()` cannot take that (it keeps a
bit for each class mod p in a ulong, and fails for p > 64); the
builder of 4.5 must not have that limit.

### 4.5 The batches of a forced prime

For one forced prime p the batches are built level by level, f from 0
to e. Level e stands for every f >= e: the powers of p at the
positions are the same for all of them. Within a level the low and
high positions have their exact power from 4.4, and C is the set of
critical positions, each with its a' = a_i / p^{e-f}.

**The plain batch of level f.** Every critical position has exactly
p^e. The d it answers for are d = p^f.d' with

- d' not == -n'/a' (mod p) for each position in C, and
- d' not == 0 (mod p), if f < e.

Let X be the set of classes mod p so excluded.

- If X is all p classes, there is no plain batch at this level.
- If one class r is left, the batch fixes d == p^f.r (mod p^{f+1}).
  For p not dividing n and p <= true_k this is always the case, with
  r = 0: the batch "p divides d".
- Otherwise it fixes d == 0 (mod p^f) only, which for f = 0 is no
  constraint. The excluded classes are left to the walks (4.6).

**The batches with an extra power, of level f.** For each m in C,
in order, and each c >= 1 with (e + c + 1) dividing tau(n): position
m has exactly p^{e+c}, and is the primary. With a'_m its a':

- d' == -n'/a'_m (mod p^c). Write u = (n' + a'_m.d') / p^c, which
  must not be divisible by p.
- For each other position j in C let w be the power of p in
  a'_j - a'_m.
  - w < c: position j has exactly p^{e+w}.
  - w >= c and j < m: no batch. Position j would have p^{e+c} or
    more and come first, so this is the batch whose primary is j.
  - w > c: position j has exactly p^{e+c}.
  - w = c: position j has p^{e+c}, exactly so if
    u not == -((a'_j - a'_m) / p^c).d' (mod p). That takes one more
    class from u. (d' mod p is known from the first line.)
- If no class is left for u, no batch. If exactly one is left and
  p = 2, fold it in: the batch fixes d' mod p^{c+1}. Otherwise it
  fixes d' mod p^c. (pc[oar]ul fold only for p = 2; keep that.)

In both kinds the batch is dropped unless (E + 1) divides tau(n) for
the power E at every position, as `test_forcep()` does with
`target_t(vj) % (ej + 1)`. `apply_allocv()` still makes the full test
against what is left of tau when the batch is applied.

The primary of a plain batch is the first position with its greatest
power, as for any batch.

What a batch stores. `t_forcebatch` has `primary`, `fold` and `x[]`.
Type t needs, besides: the level f, and for a plain batch whether one
class r is fixed and which. The class of d is then:

    plain:   d == p^f.r (mod p^{f+1}), or d == 0 (mod p^f)
    extra:   d == p^f.rho (mod p^{f+c}), or (mod p^{f+c+1}) if folded,
             with rho the class of d' above

Moduli can exceed a ulong (p^{f+c} with p near n), so the class is
formed in mpz_t when the batch is applied, as `update_chinese()` does
now for a large px; it is not stored.

Proposed, for stage 3: two fields, `dv` (the level f) and `cls` (r,
or a value meaning none), unused by pc[oar]ul. (Stage 2 did not add
them: nothing reads them before the builder.)

Done in stage 2: one function turns a batch into the residue class of
d, and one combines a residue class with a node,

```c
/* Set (res, m) to the residue class of d that batch bi of forced
 * prime fpi fixes: d == res (mod m), m a power of p.
 */
void batch_resclass(mpz_t res, mpz_t m, uint fpi, uint bi);

/* Combine d == res (mod m), m a power of p, with old into new;
 * FALSE if inconsistent.
 */
static inline bool apply_resclass(
    t_node *old, t_node *new, ulong p, mpz_t res, mpz_t m
);
```

For pc[oar]ul `batch_resclass()` computes what `update_chinese()` did
from (primary, x, fold), asserting a_i = 1 at the primary; for pctul
it is to return the `dv`/`cls` the builder recorded (stage 3).
`apply_primary()` now takes (fpi, bi) and uses the two, and recovery
uses `batch_is_best()`, the batch form of `least_is_best()` (which no
longer takes a fold). Checked: those were the only places a batch's
fold reached `update_chinese()`. A batch's fold also reaches
`update_residues()` from `apply_batch()`, on the square path that 4.8
replaces under TYPE_t.

Appendix B has the batches of some small cases, as the rules give
them.

### 4.6 Coverage, exactness, and the batch that allocates nothing

Coverage. For a forced prime the batches of 4.5 are disjoint in the
powers they state, and every d that can be a solution has the powers
of exactly one of them (checked: 4.11). So the batches of all forced
primes together split the search as pcoul's do.

Exactness. A batch says "exactly p^E at v_i". The class it fixes need
not exclude the d that give more. Three mechanisms cover that, and
together they must cover every case:

1. The class itself. A folded class, or a plain batch with one class
   left, excludes them outright. Then p divides qq_i and o_i is prime
   to p.
2. The exclusions of `walk_v()` (`inv[]`). For each allocation of p at
   v_i with p not dividing qq_i, the walk leaves out the t with
   o_i + t.qq_i == 0 (mod p). With the o_i and qq_i of 4.3 this needs
   no change, and it is what enforces "d' not == 0 (mod p)" for a
   level f >= 1, and the excluded classes of the critical positions.
   (`small_divmod()` returns p for "no inverse"; that is case 1.)
3. `walk_1()` and `walk_1_set()` test gcd(v_j / q_j, q_j) = 1.

One case has no allocation for the exclusions to hang on: a plain
batch of level 0, for p dividing n, that fixes no class and in which
no position has a power of p below p^e. (That is every such batch
with p >= true_k or with e = 1, unless one class was left.) It
answers for the d not divisible by p, and nothing in it says so. A
walk in it would also test the d divisible by p, which belong to the
higher levels. That is safe (T1) but wasteful: for k = 4 and 5 | n,
a fifth of the walk. So `walk_v()` adds one entry to `inv[]` for
each such level in the stack: p, and the class of t with
rq + aq.t == 0 (mod p). Size `inv[]` for `forcedp` more entries.
With that entry the three mechanisms are complete (checked: 4.11).

No tails. In pcoul a prime that would be allocated at one position
only can be left "unforced" on a tail, a batch that fixes nothing.
pctul has none in this design: every batch of 4.5 is listed
(`keep_single` is always true), and `is_tail()` is never true.
The reasons:

- The batch "p divides d" and a tail would both show nothing for p in
  a pattern, and recovery could not tell them apart.
- A tail's walk covers p classes mod p at once; p single batches
  cover the same d in the same number of walk steps, each knowing
  where p is.

So `-f` and `-F` have nothing to act on under pctul. Decided: pctul
refuses them. Tails for pctul are parked (9.3).

No tails is also what makes `update_chinese()` safe under pctul: it
divides by a_i, so p must not divide a_i, and for an unforced p that
holds only because every unforced p > true_k. A tail would leave a
forced p (p <= true_k, possibly dividing a_i) to be allocated
unforced. Stage 3 must leave a comment where tails are generated
(where `keep_single` is set, and at the tail's `fpb_init()`) saying
that tails under TYPE_t would break that assumption, pointing at
`update_chinese()`. (Its own comment already says so, since stage 2.)

The batch that allocates nothing. In pcoul a batch always shows in the
pattern, the tail apart. In pctul the commonest batch of a prime
allocates nothing: "p divides d" for p not dividing n, and level 0 for
a large p dividing n. For prime n the one batch that is walked is of
that kind for every forced prime, and its pattern is ". . . .".

`insert_forced()` rebuilds the forced levels from the pattern. Given
an empty pattern it cannot tell how many forced primes had been
applied when the line was written, and "every progress line is a
usable recovery point" fails. So such a batch must show in the
pattern. Proposed: it shows as `p^0` at the first position.

    203 b0: 2^0.3^0.5^0.13^0 . . . [aq=30]
    305 b12: 2^0.3^0.5.17^0.19^0 . . . . (1.23s)

(The first is the batch of f(13, 5) that is walked; the second, for
f(323, 6), has 5 at the first position and nothing else. Both are
to show the syntax only.)

This is what the code already says of such a level: `apply_null()`
calls it "a notional level of p^0 at v_0" and gives its act x = 1.
What is needed:

- `prep_show_v()` prints p^0 in the first entry for each forced
  level, up to the node's own, whose batch has no allocation. It
  takes them from `acts[]`; there is no allocation record for them.
- `parse_305()` keeps an entry with exponent 0 under TYPE_t. Today it
  reads one and drops it.
- `insert_forced()` finds the highest power of p in the pattern as
  now. A `p^0` there selects the batch of p that allocates nothing,
  of which a prime has at most one (4.11).
- Under `-I`, a forced prime missing from the pattern means "not
  given", as now.

Decided: try `p^0`. It is written in one place and parsed in a
couple, so it can be changed if it proves the wrong choice; keep it
that way. (The alternative considered was a separate field before the
pattern, listing what is known of d.)

`apply_level()` marks a prime as used for `mintau()` only if x > 1
(`apply_pfreev()`). Under pctul a forced prime is settled by its batch
whatever the batch, so mark it always: mintau then starts above
true_k, which is a better bound and a valid one.

### 4.7 Unforced primes

An unforced p is greater than true_k and does not divide n (4.4), so
it is prime to every a_i. Allocating p^{x-1} at v_i fixes

    d == -c_i / a_i (mod p^{x-1})

`update_chinese()` computes the residue -c_i mod p^{x-1}, and since
stage 1 multiplies it by the inverse of a_i when `TYPE_MULT(vi) != 1`
(`ppow_invert()` in the single-limb path, `mpz_invert()` in the mpz
path). It asserts that p does not divide a_i.
`single_fold()` is for p = 2, which is never unforced in pctul.

`reject_single()` solves aq.t == -(rq + c_i) (mod p) for t. Under the
affine form that is

    a_i.aq.t == -(c_i + a_i.rq) (mod p)

so it multiplies both the residue of aq and that of rq by a_i mod p
(done in stage 1, in `reject_mod()`, which now takes the position)
before it inverts. The same for its second stage mod p^2 and its
general stage.

### 4.8 A fixed square

A position whose remaining tau is odd is v_s = q_s.z^g. Its roots are
the z with

    z^g == o_s (mod qq_s)

in the o_s and qq_s of 4.3. Three places keep that true.

`alloc_square()` forms o and qq from (rq, aq) and calls
`allzrootmod()`. With the definitions of 4.3 it is otherwise
unchanged. qq_s now has the factor a_s; o_s is prime to every prime
of qq_s, as now, because the batches state exact powers (4.11).

`update_residues()`, on an unforced allocation of p^{x-1} at v_i.

- At another position: the new knowledge is v_i == 0 (mod p^{x-1}),
  and by the resultant
  a_i.v_s == TYPE_RES(i, s) (mod p^{x-1}). Today the code sets
  `ur_a` to the offset between the two and divides by q_s; it becomes
  `TYPE_RES(vi, sq0)` divided by a_i.q_s. p is prime to both.
- At the square itself: the residues are divided by p^{(x-1)/g}
  modulo the old qq_s with p removed, as now.
- In both, the modulus `ur_m` it forms as aq / q_s becomes
  a_s.aq / q_s.

`update_residues()`, in a forced batch. This is the intricate part of
the function: a primary and secondaries, a fold, the square taking
the secondary first and then the primary's remainder (`retry`). All
of it derives the class of v_s from "p^e divides v_primary", which
type t cannot do (T5). Under TYPE_t do not extend it. When a batch is
applied below a fixed square, find the roots afresh, as
`alloc_square()` does: `allzrootmod()` on the new o_s, the new g if
the batch allocated at the square, and the new qq_s. Forced levels
are few and at the top of the tree, and `alloc_square()` already pays
this price whenever a square appears. Return false, as now, if there
are no roots. **[verify]** that `allzrootmod()` is safe to call again
for a level that already holds residues.

Decided: do this, subject to a timing test. hv's reason goes beyond
pctul: the handling of secondary powers in `update_residues()` has
been the source of several bugs, and he is still not confident in
it. The timing test, in stage 4: on pcoul, where both ways exist,
build once with the batch path of `update_residues()` and once
finding the roots afresh, and compare CPU time over the forced part
of a run (`-a` lists the batches without searching them;
**[verify]** that it applies them as a search does) for two
cases with a square fixed before the batches end and an aq of
production size; hv to name them. The logs must be identical. If the
cost is nothing to speak of, pctul uses it, and removing the batch
path from pc[oar]ul becomes a change hv can ask for separately. If
it is not, report the figures before going further.

`reject_square()` tests whether q_s.z^g == d (mod p) can hold when p
is tried at v_i, with d the offset from v_i to the square. By the
resultant the congruence is

    a_i.q_s.z^g == TYPE_RES(i, s) (mod p)

so `rs_d` becomes `TYPE_RES(vi, sq0)` and the residue of q_s is
multiplied by a_i (mod p, and mod p^2 for the lift). Its tests are
then as now: the Jacobi symbol for h = 2, the power for h > 2, and
the lift to p^2. No new inverse is needed. The call in `walk_midp()`
changes the same way. (Done in stage 1: `reject_square()` now takes
the position as its first argument.)

`square_endr()` and the limits of the root walk in `walk_v()` take
the greatest v_s from `dtov()`.

### 4.9 Two squares: Pell

With v_i = q_i.x^2 and v_j = q_j.y^2 the resultant gives

    a_j.q_i.x^2 - a_i.q_j.y^2 = TYPE_RES(j, i)

so `walk_v()` calls `new_pell()` with a_j.q_i, a_i.q_j and
`TYPE_RES(sqj, sqi)`. Each solution is then checked against o and qq
at both squares, as now; with the qq of 4.3 that check also ensures
that d is an integer. (The call is so written since stage 1; with
TYPE_RES() an int, `new_pell()` keeps its int argument.)

The limit passed for x must come from the greatest v_i, not from
zmax: until stage 0 it was zmax / q_i, which lost any solution with
d within TYPE_OFFSET(i) of the maximum (fixed on master as a bug of
its own, alongside stage 0).

One change in pell.c (its int argument stays, see 4.2):

- `new_pell()` loops f from 1 to |N| looking for the f whose square
  divides the right side. For pc[oar]ul |N| is below 66 or a small
  multiple of n. For pctul |N| = n.|i - j| can be tens of millions,
  for each equation. The f wanted are divisors of N with f^2 dividing
  N.ra; enumerate them from the factors of N. N takes at most k - 1
  absolute values in a run, and n's factors are known (`nf`).

`test_pell` covers pell.c; extend it to large N, and run the soak
test.

n itself a square makes tau(n) odd, so `prep_presquare()` fixes
every position as a square before any batch, and with k >= 3 that is
a Pell case from the start. No change is needed there beyond 4.8, but
it is the first thing a test of stage 5 will meet.

### 4.10 What a pctul search looks like

Prime n, k <= n. tau is 2, so nothing can be allocated anywhere.
Each prime p <= true_k has the batch "p divides d" and one batch for
each other class, which puts p^1 at one or more positions, completes
them, and is tested at once and dropped (`terminal`). The prime n has
the level-0 batch, and a level-1 batch that completes every position.
So one batch is walked: d a multiple of every prime up to true_k, not
a multiple of n, each of the k - 1 values to be prime. pctul adds
nothing to that walk but the speed of C.

n = p.q. tau is 4, and a position can take one forced prime (leaving
a prime) or a cube. The level-1 batch of p, with d a multiple of p,
leaves v_i / p = q + (i + 1).d / p to be prime at every position:
tauseq(q) again, in the multiples of p. The Perl code finds this by
`check_mult()` and its "p$k" test; here it is one batch among the
others.

tau(n) with an odd factor: positions reach an odd remaining tau and
become squares, as in pcoul for n with an odd factor. This is where
the recursion, the gate and the rest of pcoul's machinery start to
earn their keep.

### 4.11 What was checked, and how

Three checks were made of sections 4.4 to 4.6, by a Perl script
that builds the batches of a forced prime from the rules of 4.5 and
nothing else. They are worth rebuilding as a test (section 7).

One prime at a time. For p in {2, 3, 5, 7, 11}, n up to 60, up to 9
positions, and tau in {2, 4, 6, 8, 12}: every d in a full period that
could be a solution (each power E at each position has E + 1 dividing
tau) has the powers of exactly one batch, lies in that batch's class,
and no two batches of a prime state the same powers. 6867 cases,
38954 batches, no failure; and again for n up to 40 with folding
allowed for odd p.

Coverage of the whole search. For n in 2..40 (k in 2..6, d to 2000),
41..130 (k in 2..8, d to 3000) and 300..345 (k in 3..10, d to 3000):
take every combination of one batch per forced prime, combine the
classes, walk d in the result, and test tau directly. Every solution
a plain scan finds was found: 1193 cases, 84807 solutions, no
failure. I1 and I2 held at every combination. A control that drops
level 1 lost solutions, as it should.

Exactness. For n in 2..120, k in 2..8, d to 2000: at every step of
every such walk, for every forced prime, either d has exactly the
powers its batch states, or one of the exclusions of 4.6 leaves it
out. 833 cases, 749513 steps, no failure. Without the added entry
of 4.6 the same check fails; with it, that entry alone removes 15
percent of the steps in this sample.

Not checked: anything involving unforced primes, squares or Pell
(4.7 to 4.9 are algebra only), and tau(n) above 12 in the first
check.

### 4.12 Dependent n

Added 2026-11-14 after hv's first reading.

The Perl code knows that f(n, k) is often a multiple of a smaller
case: f(105, k) = 3.f(35, k) for every k from 16 up. `gtauseq` calls
`check_mult()`, which looks at what its constraints have fixed; if
they force p^{e+1} to divide d for a prime p with p^e exactly dividing
n, it prints

    201 Dependent - <k>:<p^e> f(<n / p^e>) # fix <p^e>

and stops, unless `-f` was given. The harness records the dependence
and does not search.

In the terms of 4.5 this needs no new mathematics. Call a batch live
if it leaves every position incomplete; a batch that completes a
position holds one d, which is tested as soon as the batch is applied.
Then:

    p fixes n at k if the only live batch of p is the plain batch of
    level e with the class d == 0 (mod p^{e+1}).

In that batch every v_i has exactly p^e, and
v_i / p^e = n' + a_i.(d / p^e) must have tau(n) / (e + 1) = tau(n')
divisors. So the solutions of (n, k) in it are exactly p^e times the
solutions d'' of (n', k) that are divisible by p.

That is not yet f(n, k) = p^e.f(n', k): the least solution of (n', k)
might not be divisible by p. `TauSeq.pm` has this as a FIXME ("we
should report this only if g(n / p^k) would fix p"). pctul can settle
it, because the same builder gives the batches of p for n'. There
p does not divide n', so if the only live batch of p for (n', k) is
"p divides d", every solution of (n', k) outside the completing
batches is divisible by p, and the two solution sets correspond.

Checked with the script of 4.11:

- For n = 105 and p = 3 the rules give, at k = 14 and 15, two live
  batches: d == 0 (mod 9), and d == 5 (mod 9) with 27 exactly
  dividing 105 + 6d. From k = 16 only d == 0 (mod 9) is left: the
  position 105 + 15d joins the class of 105 + 6d and would need 3^2.
  That is where hv's report for 105 shows its dependence
  beginning, and f(105, 15) = 230390168 is 5 (mod 9).
- For n up to 200 and k up to 12, p fixes n at k in 780 cases. In
  none of them did n' have a live batch of p other than "p divides
  d". That is a scan, not a proof that it cannot happen.

What a dependent run costs. If pctul searches (n, k) regardless, it
is right, and it does the walk that (n', k) would do, on values p^e
times larger. So nothing is lost in the run itself. What is lost is
the run: if f(n', k) is known, f(n, k) needs no search.

Proposed:

- After `prep_forcep()`, for each p dividing n in turn, test whether
  p fixes n at k, and whether "p divides d" is the only live batch of
  p for (n', k). This is a few calls of the builder.
- If both hold, write the 201 line in the form above, so that the
  harness reads it as it does `gtauseq`'s. Then stop.
- If only the first holds, (n, k) is not dependent, and pctul
  searches. The relation is still worth having: every solution is a
  multiple of p^{e+1}, and f(n, k) >= p^e.f(n', k), which bounds the
  minimum from below. Decided: show a warning that says so, naming
  p^e and n'. **[hv]** its code and wording. Note that `gtauseq`
  would call such a case dependent (its FIXME), so a dependence
  recorded from it is not one that pctul need confirm.
- The completing batches of p, for n and for n', each hold one d.
  For the 201 line to be a claim and not a hint, those d must be
  shown not to be solutions, or to be greater than the answer. They
  are few and small; test them before the line is written.

Decided: pctul stops at a dependent n by default, since searching
gains nothing but a check of this logic. `-jd` makes it search
regardless. (`-jd` is free on master and on calibrate. hv notes that
`-jd` and `-jp` may one day move from `-j` to another letter.)

hv's account of where dependence begins: the first case is
f(10, k) = 2.f(5, k) for k >= 3, and for n = p.q with p < q it can
occur for k > p.(p - 1). The rules of 4.5 agree: for n in {10, 15,
21, 35, 55, 77, 91} the smaller prime fixes n from k = 3, 7, 7, 21,
21, 43, 43, which is p.(p - 1) + 1 in each. For n = p.q.r it is
later: 30 and 42 are fixed by 2 from k = 7 and by 3 from k = 16, and
105 by 3 from k = 16 and by 5 from k = 46. In all of these n' fixes
p as well. So in these each prime s of p.q.r fixes n from
k = s.(2s - 1) + 1. (hv gives g(p.q.r) = max(p.(2p - 1), q.(q - 1), r)
and guesses that dependence needs k > max(p.(2p - 1), q.(q - 1)).
For 105 that would be k > 20, where his report and the rules both
have it from k = 16, so the guess looks too strong.)

A test for `-jd`: at a dependent (n, k), the search under `-jd` finds
p^e times what the search of (n', k) finds. By the sieve of appendix
A the solutions of (10, 3) up to 200 are 12 24 36 48 84 96 108 132
and two more, and those of (5, 3) up to 100 are 6 12 18 24 42 48 54
66 and two more; likewise (10, 4) to 2000 and (5, 4) to 1000, with
23 each.

Dependence can chain (n' may itself be fixed by another prime); pctul
reports one step, and the run on n' reports the next.


## 5. The code, site by site

On master `TYPE_OFFSET()` is used at 40 places in coul.c. They fall
into five kinds. A site not listed here that adds an offset to a
value, or forms aq / q, belongs to one of them.

**The greatest v_i** (zmax + offset becomes `dtov(.., vi, zmax)`):
`updated_zmax()`, `apply_allocv()`, `limit_p()` (twice; the second
is TYPE_o only), `prep_midp()`, `square_endr()`,
`run_flip_pqsq()` (twice), and the root limit `wv_endr` in
`walk_v()`.

**The least v_i** (zmin + offset): `walk_v()` (Pell, where x must
exceed a bound) and `walk_1_set()` (the least p).

**o_i and qq_i** (4.3): `walk_v()` where it fills `wv_o[]` and
`wv_qq[]`; `alloc_square()`; `walk_1_set()` where it forms the class
that p^{x-1} must lie in (`w1_m`, `w1_mr`): with qq in place of
aq / q that class also makes d an integer, and `need_mod` is then
true whenever a_i > 1.

**d from a value** (`vtod()`, reject if not exact, after any test
against a bound): `walk_1()`,
`walk_1_set()` and the Pell branch of `walk_v()` (its test against
zmax) where they turn a completed v_i into v_0; `apply_batch()`
where it tests a terminal value against zmin. Then each other v_j
comes from `dtov()`. The three places in `walk_v()` that rebuild
the candidate as (o_0 + t.qq_0).q_0 use rq + aq.t under any type, and
so do its failure handlers `walk_v_failure()` and `walk_zv_failure()`
(from `g_node`, which replaced `g_q0`).

All of these are done (stage 1), with two more helpers for the third
kind, `calc_o()` and `calc_qq()`, that form o_i and qq_i, asserting I1 and
I2 when a_i > 1. There is no build flag for debug-only checks, and an
assertion where a_i = 1 would cost pc[oar]ul a division per position
per walk, so they are not checked there.

**The resultant** (`TYPE_RES()`): `walk_v()` (Pell, 4.9),
`update_residues()`, `reject_prep_square()`, `walk_midp()` (4.8).
`apply_batch()` also forms one, where a secondary of a batch hits
the square; that path is pc[oar]ul's only (4.8), and stage 1 left it
alone. Note that it writes `TYPE_OFFSET(sq0 - vi)` with unsigned
arithmetic, which wraps when sq0 < vi; the result is right only
because a fold arises only for p = 2.

Sites that need more than a substitution:

- `gate_walk()`. Its estimate of a walk starts from zmax + offset and
  divides by aq. Without a square that counts the steps of the walk,
  which are steps of d: it should be zmax / aq, with no multiplier.
  With one square it is the count of roots: the root of the greatest
  v_s over q_s, times the residues, over qq_s. Today it takes the
  offset of the loop's position, not the square's; for pcoul the
  difference is nothing, for pctul it is a factor of a_i. Write both
  in the terms of 4.3. This must leave pc[oar]ul's decisions as they
  are (the offset is negligible against zmax, but check: 8.1).
  Done in stage 1 as two commits: one in terms of `gate_span()`, the
  span of a position, still taking the loop's position for the square
  case, with estimates exactly as before; then one that takes the
  square's position, which can change a decision only in a case
  vanishingly rare.
- `update_chinese()`, `reject_single()`: 4.7.
- `test_forcep()`, `list_forcep()`, `max_forcep()`, `prep_forcep()`:
  unchanged for pc[oar]ul. Under TYPE_t `list_forcep()` gives the
  primes dividing n and then the others up to true_k (not k), in the
  order it uses for TYPE_a,
  and `prep_forcep()` calls the builder of 4.5 for each. The modfix
  test at the head of `test_forcep()` has a simpler form for a batch
  that knows its class: drop the batch only if no d of its class can
  satisfy the modfix. **[verify]** how a negated modfix is enforced
  in the walks, since the builder may keep batches it could drop.
- `relative_valuation()`, used by `insert_forced()` to take a batch's
  powers off the recovery stack. It recomputes from offsets what
  `bp->x[]` already holds. Use `bp->x[]`, for every type, and remove
  it. Done in stage 0. Checked: equal by construction (both come
  from the valuations `test_forcep()` takes), and a temporary
  assertion comparing the two held over `make dtest`.
- `prep_target()`, `know_target()`, `target_t()`, `target_lcm`: type t
  is type r with every target equal to tau(n). Use the TYPE_r code
  (`target_tau[]`, `target_lcm`) for both.
- `init_levels()`: `np->maxp` starts at the greatest prime of n, as
  for TYPE_a (there `divisors[n].high`; here from `nf`, since
  `divisors[]` runs only to tau(n)).
- `init_post()`: the default strategy is chosen from `nf.count`, the
  distinct primes of n. For types o and a that is the target tau. For
  type t it must be the distinct primes of tau(n). (Type r has the
  same oddity today and is not this design's business.)
- `prep_maxforce()`: true_k at every position (4.4).
- `candidate()`: no change. `exceptions[]`: add `{ 't', 243, 4 }` and
  `{ 't', 2401, 3 }` from `TauSeq.pm`, compared with `true_k`.
- `typename()`: 't'.
- coulvec.c (`-c`): `apply_m()` suppresses, in three places, a class
  of v_0 that would give v_i a residue w mod m that cannot occur. For
  type t the d with a_i.d == w - n (mod m) form a class mod
  m / gcd(a_i, m), or none: `suppress_k()` in `TauSeq.pm` is the
  model. Put the translation in one helper used by all three. The
  test against `cx->min` in the first of them is for the one value
  v_i = m; under type t that is d = (m - n) / a_i if it is an integer.

Not affected, as far as I can see, and so to be exercised and not
rewritten (stage 8): `walk_midp()` beyond the call above, `-k` and
the `kern_` code (TYPE_o only where it tests n), the flip, the
strategies (`best_v0()` to `best_v4()`; STRATEGY_6X is TYPE_o only),
`mintau()`, the caps, `-a` and `-b`, `-o`.


## 6. Options, lines, recovery

- `pctul [options] n k`, k as in f(n, k), 2 <= k <= MAXK + 1.
  **[verify]** which of the two bounds on positions (`MAXK`, the
  `t_dis` words) is the tighter once k is one less.
- n is a uint, as now. c_i = n and the resultant fit the types of
  4.2 for any such n.
- `-x<min>:<max>` bounds d.
- `-f`, `-F`: refused (4.6).
- `-c`, `-m`: refused until stage 6.
- `-y t` accepted, as each program accepts its own letter.
- Lines: as pcoul, with `true_k` where k is echoed (4.1), `p^0` in
  patterns (4.6), and `pctul` in the 001 line through `typename()`.
- `-I`: a pattern of k entries; `p^0` at the first entry selects the
  batch that allocates nothing.
- No new line code is needed. If a refusal wants its own code,
  propose one and flag it.


## 7. Tests

Build: `pctul dpctul: DEFINES += -DTYPE_t`, added to `all`, `test`
and `dtest`. The Windows workflows build what they build now, but
they run `make test`, so pctul must compile there.

Main tests (fast; added to the existing files, by what they test):

- t40known: for a handful of the cases in appendix A, the solutions
  of a full search under `-X` are exactly those listed. Pick ones
  that finish in well under a second and between them have: prime n;
  n = p.q with a prime below k dividing n; n a prime cube; tau(n) = 6
  (a square arises); n a square with k = 3 (Pell); a range with no
  solution. Add the two exceptions, as the pcrul test does.
- t10init: recovery from a log of one or two lines, at a batch whose
  pattern is all `p^0`; at one with an extra power; inside a walk;
  and `-I` with and without `p^0`.
- t30batch **[verify]** what it covers: `-a` for one small case,
  against the list of appendix B.

Soak test (skips itself unless `TEST_TSEQ` is set; hv may not keep
it once the development is done): for a grid of (n, k) and a range,
sieve tau in Perl and compare the set of solutions with `pctul -X`.
The grid of 4.11 is a starting point; take ranges long enough that
most cases have solutions. This is the check that would have caught
any mistake in 4.5, and it is to be shown able to fail: a build with
one kind of batch left out must fail it.

For the refactoring stages, 8.1.


## 8. Stages

Each stage is a short series of commits, each working, each
explainable in its message, ending with `make dtest` clean. Commit
subjects name the programs affected: "pc?ul:" for shared code,
"pctul:" once it exists.

### 8.1 "Identical" for pc[oar]ul

Before the stage, with the build it starts from, record for a set of
runs the log under `-dL` (every progress line) with times removed, or
where that is too long the 367 counts and the candidates under `-X`.
After the stage they must be the same. The set: the runs of the test
suite, and beside them at least

- pcoul: n in {6, 8, 12, 18, 24, 30, 36, 48, 50, 60}, k from 2 to the
  greatest with a known value that runs in seconds; `-j4` on the
  n = 8 and 48 cases; `-W` and `-k` on two of them; one recovery.
- pcaul: n in {2, 4, 6, 8, 12}.
- pcrul: a dozen n including 484 and 1760 (squares at an end).

State the set and the result in the stage's report.

### Stage 0: tidy-ups on master, each its own commit

- `insert_forced()` takes the powers from `bp->x[]`;
  `relative_valuation()` goes.
- `TYPE_OFFSET()` defined once.
- `report_211()` adds `vi` to the best value where it should add
  `TYPE_OFFSET(vi)`. For pcaul its 211 lines then show the wrong
  values. (From reading; pcaul is not run by the harness, which is
  probably why it has not been seen.) A bug, in its own commit.

Done when: identical (8.1), bar the 211 lines of pcaul.

### Stage 1: the three relations

- `TYPE_MULT()`, `TYPE_RES()`, `dtov()`, `vtod()`.
- Every site of section 5 converted, by kind. `TYPE_MULT()` is 1 for
  all three programs, so nothing changes.
- I1 and I2 asserted in the debug builds.

Done when: identical (8.1), and `make test` shows no change in CPU
time beyond noise on two production-size batches (give the commands).
No pctul target yet.

### Stage 2: a batch gives its residue class

- `batch_resclass()`, used by `apply_primary()` and the recovery
  helpers in place of (primary, x, fold).
- The fields of 4.5 added to `t_forcebatch`.

Done when: identical (8.1).

### As done: stages 0 to 2 (2026-11-16/17)

On master, over 5a553ae, ending f98cbb5, in order:

- pc?ul: insert_forced() takes powers from the batch
- pc?ul: each type's characteristics in one place, in coul.h (name,
  TYPE_MULT(), TYPE_OFFSET(), target_t(), target_lcm as one-liners per
  type under the comment stating what each type searches for;
  coulvec.c's context loses its n, coulmint.c its copy of target_lcm;
  ftest, speed and sq12 are built with -DTYPE_o, as test_pell and
  test_tau were)
- pcaul: (bugfix) 211 lines showed the wrong values
- pc?ul: (bugfix) Pell walk missed v_0 near the maximum (found while
  reading for stage 1; see 4.9)
- pc?ul: walk failure handlers take d from the node
- pc?ul: v_i as a linear combination of d, TYPE_MULT, TYPE_OFFSET
- pc?ul: TYPE_RES(), the resultant of two positions
- pc?ul: allow for TYPE_MULT() in the CRT and reject_single()
- pc?ul: gate_walk() in terms of the span of v_i
- pc?ul: estimate a square walk from the square's span
- pc?ul: a batch gives the residue class of d it fixes
- pc?ul: say that least_is_best() writes to cur
- skills: pcoul-internals on v_i as a function of d

Names settled in review, used throughout this document: `dtov()` and
`vtod()` (d to v_i and back; `vtod()` gives the greatest d with
v_i <= v and says whether it is exact), `calc_o()` and `calc_qq()`,
`TYPE_RES()` (an int: see 4.2), `batch_resclass()` and
`apply_resclass()`. "Class" in this document means a residue class.

Identical (8.1): 108 runs of the optimised builds, logs under `-dL`
where short enough (else candidates, 367 counts and the log), with
times and paths removed: pcoul n in {6, 8, 12, 18, 24, 30, 36, 48, 50,
60} at small k, some under `-X`; `-j4`, `-W`, `-Wx`, `-k`, `-f`, `-F`,
`-jp`, `-a`, `-g/-G`, `-m`, `-c`, `-I`; three recoveries; pcaul n in
{2, 4, 6, 8, 12}; pcrul n in {10, 12, 20, 30, 36, 60, 100, 121, 144,
210, 484, 1760}. Each of stage 0 (with the Pell fix), stage 1 before
and after the square-span commit, and stage 2 gives the same output.
Against master the one difference is from the Pell fix: pcoul 6 4
makes one more Pell step (walkc +1, no candidate). `make dtest` passes
after every commit; ftest, sq12, test_pell, test_tau and speed build.

Timing (stage 1 condition), CPU seconds from the 367 line, master vs
stage 2, three runs each, alternated:

    pcoul -b0 -x22911293821947932 -j2 -f7 -g30 48 10
        master 10.33 10.77 10.66    stage 2 10.72 10.74 10.30
    pcoul -b3 -x1e19 36 4           (one square: 2^2.3^3 . 2 3)
        master  8.65  9.35  8.14    stage 2  8.40  8.67  8.20

No change beyond noise. (Run in the Claude sandbox, not on hv's
machine.)

Further, from review: `update_chinese()` keeps its fold parameter
(a fold for odd p is still being considered); its comment says it is
for unforced allocations, that p must not divide a_i (for an unforced
p guaranteed only while TYPE_t has no tails), and why it does not use
`apply_resclass()`. `batch_resclass()` asserts a_i = 1 at the primary;
stage 3 replaces its derivation for TYPE_t. The square case of
`gate_walk()` uses `calc_qq()`.

Departures from the text above: the `dv`/`cls` fields wait for stage
3; I1 and I2 are asserted only where a_i > 1 (section 5).

### Stage 3: pctul for tau(n) a power of 2

Covers prime n, n = p.q, p^3, p.q.r and so on: no position can reach
an odd tau above 1.

- `fail()` at startup if n.(k - 1) exceeds INT_MAX, so that
  `TYPE_RES()` fits its int (4.2).
- `batch_resclass()` returns the residue class the builder recorded
  (`dv`/`cls`), in place of its a_i = 1 derivation.
- Targets; `true_k`; the target and forced-prime preparation of
  section 5; the builder of 4.5; `p^0` in patterns, parsed and
  recovered; the exclusion of 4.6; the reports; the exceptions.
- The comment at tail generation required by 4.6 (tails would break
  `update_chinese()`'s assumption that p does not divide a_i).
- `fail()` if tau(n) is not a power of 2, and for `-c`, `-m`, `-f`,
  `-F`.
- Tests: t40known and t10init entries for these n; the soak test,
  restricted to them.

- The test for dependent n (4.12), its 201 line, its warning, and
  `-jd`.

Needs **[hv]** on the warning of 4.12.

Done when: the tests pass, the soak test passes and is shown to
fail on a broken build, and `inject -yt -n` agrees on each value
found (**[verify]** that inject takes type t without a database).

### As done: stage 3 (2026-11-17)

Over f98cbb5, in order:

- pc?ul: a batch may record its residue class
- pctul: tau(n + id) = tau(n), for tau(n) a power of 2
- pctul: stop at a dependent (n, k)
- tests: pctul
- skills: pcoul-internals on pctul batches

How it differs from the text above:

- `t_forcebatch` has `dv` and `cls`, with `cls` one of a class r,
  `CLS_ANY` (d == 0 (mod p^dv)) or `CLS_PRIMARY`. Every pc[oar]ul batch
  is `CLS_PRIMARY`, and so is every pctul batch with an extra power:
  `batch_resclass()` derives their class from primary, power and fold
  as before, then divides p^g out of the class and the modulus (g the
  power of p in a_i) and multiplies by the inverse of a_i / p^g. That
  is the class of 4.5 for an extra-power batch, so it needs no field.
  Only plain batches record a class.
- A batch that allocates nothing has x[0] = 1 (p^0 at v_0), which
  keeps `is_tail()` false; `apply_unalloc()` applies it and marks its
  prime used for mintau(). `unapply_batch()` and the secondaries loop
  treat x <= 1 as no allocation (the same for pc[oar]ul, where x is
  never 1). The batch of a forced level is found by `level_batch()`:
  a level is forced just when it clears a bit of `fp_need`.
- `target_t()` returns a scalar `target_lcm` = tau(n), not TYPE_r's
  array (hv: fine as a precomputed variable).
- The exclusion of 4.6 is added in `walk_v()` for each level whose
  batch has x[0] = 1, `CLS_ANY` and p | n: that is exactly the case
  where no allocation of p exists to exclude d divisible by p.
- `-fr` is supported (hv): the builder applies the same test to the
  primary's power as `prep_forcep()` does.
- New codes: 313 for the warning of 4.12 (hv to validate the wording):
  `313 Partly dependent: each solution is P.d with d a solution for
  f(N', k) divisible by p, so f(n, k) >= P.f(N', k)`; and 524 for p^0
  of a number that is not prime in a pattern. `recover()` passes over
  313 lines.
- The completing batches of 4.12 are tested by `is_taux()` at every
  position, which can be slow when p and tau(n) are large; flagged
  FIXME in the code (hv: accept).
- The exceptions are checked before the refusal of tau(n) not a power
  of 2, so that f(243, 5) reports 403.
- `-df` shows a recorded class beside each batch.

Tested: the soak test (n 2..250, k to 10, and n 300..400, k to 12, d to
5000; 3058 tests) passes, and fails on three builds each lacking one
kind of batch (extra powers above c = 1; plain batches with a class;
extra-power batches with a w = c exclusion). Recovery from every
progress line of -X runs gave every solution for (323, 6), (13, 4), (30,
6), (105, 6), (15, 5), (27, 4) and (202, 5), the last run before the
dependence check existed. `inject -yt -n` agrees with values found and
with the 211 lines (it needs Math::GMP, Math::Prime::Util and
Math::Prime::Util::GMP). Identical (8.1): 41 runs of pc[oar]ul before
and after the series (and after the first commit alone), logs under -dL
with times removed; `make dtest` passes after each commit.

### Stage 4: one square

- 4.8 in full. `fail()` only where a second square would be fixed.
- Tests: tau(n) = 6 and 12 cases from appendix A; the soak test
  widened to every n that is not a square.

Done when: as stage 3, for the wider set.

### Stage 5: Pell

- 4.9: `new_pell()` finds its divisors from factors;
  `test_pell` extended; `TEST_PELL=1 make dtest`.
- n a square (`prep_presquare()`).
- Tests: 49 3 and 36 2 from appendix A; the soak test on every n.

Done when: as stage 3, with no refusal left for any n. pctul then
supports every (n, k), and by hv's decision `TauSeq.pm` can point at
it: add `cul => './pctul'` there, as its own commit.

### As done: stages 4 and 5 (2026-11-17)

Over stage 3, in order:

- pc?ul: Pell walk checks o_i reduced mod qq_i
- pell: shared factors of x and y from the divisors of N
- pctul: one fixed square
- pctul: Pell
- tests: pctul with squares and Pell
- TauSeq: point cul at pctul
- skills: pcoul-internals on pctul squares

(and a fixup of stage 3's pctul commit adding pctul and dpctul to
.gitignore).

Found on the way: the Pell walk compared x^2 mod qq_i with o_i
unreduced. Under pctul o_i holds n and is usually above qq_i, and every
solution was lost (f(49, 3) found none). For pc[oar]ul I believe o_i is
always reduced (offsets below k, and a p = 2 fold keeps it below qq_i);
the identical-output set and a further twelve Pell-heavy pcoul runs
agree.

4.8 as written: `square_afresh()` calls `allzrootmod()` on o_s, g and
qq_s from the node, for a batch applied below the first square (from
`apply_batch()` and `apply_unalloc()`). [verify] resolved:
`allzrootmod()` overwrites the level's array, so it is safe to call
again. Unforced allocations keep `update_residues()`, converted in
stage 1.

4.9 as written: `new_pell()` enumerates the divisors of |N| from its
factors (`pell_divisors()`, ascending, as before), and t50pell gains
large N of pctul's shape.

Timing test of 4.8 (hv named no cases, so these are mine). On pcoul,
`-a` over all batches, with the batch path of `update_residues()` and
with `roots_afresh()` forced on; output identical in every case (1.1M
lines for the first), CPU seconds from the 367 line, three runs each,
alternated, in the sandbox:

    pcoul -a -x1e60 48 10    batch 5.06 4.69 4.84    afresh 6.12 5.93 5.67
    pcoul -a -x1e60 60 10    batch 1.32 1.01 0.91    afresh 1.18 0.95 1.02

So about 20 percent more over the forced part of (48, 10), and nothing
measurable for (60, 10). pctul has no other path; whether pc[oar]ul
should take it is for hv.

Tested: the soak test now on every n (n 2..250 with k to 10, n 300..400
with k to 12, d to 5000; 4382 tests); Appendix A's larger rows match
their counts, among them (96, 4) to 2e7 (3523), (60, 4) to 2e6 (5069),
(175, 4) and (98, 4) to 1e6, and (49, 3) to 2e7; TEST_PELL passes.
Identical (8.1) for pc[oar]ul as at stage 3, plus the Pell runs above.

Then, from hv's runs against known values for n <= 10:

- pctul: drop a batch whose completed position holds no d. Such a batch
  has v_i = p^E at the completed position, so holds at most one d; if
  that is not a positive integer with the batch's powers at every
  position, the batch goes. So f(9, 4) reports 406 up front: its only
  batch of 3 puts 3^2 at every position (d = 0). No quadratic residue
  argument was needed: for 3 not dividing d, or exactly dividing it,
  some position has exactly 3^1 (9 + 3d, or 9 + d), and tau 3 rules
  that out.
- pctul: no arrangement for the base of a dependent n. A dependent
  f(n, k) whose f(n / p^e, k) has a forced prime with no batch reports
  406 naming the smaller case, not 201: f(6, 4) = 2.f(3, 4).

- pctul: a square needs a residue mod each forced prime. A position left
  with odd tau by a batch of p must be a square times its exact power of
  p, so its cofactor must be a nonzero residue mod p. For odd p up to
  TSEQ_QRMAX (2^20) the builder scans the classes of d' (plain batches;
  only whether 0, 1 or more are left matters) or of u (extra-power
  batches; only whether any is left), with the cofactor a'.c (low),
  n' + a'.c (critical), n' (high), u or u + dm.rho (critical with
  w >= c in an extra batch), or a fixed value (w < c). f(25, 3) now
  reports 406 up front. Not done: conditions mod 8 for odd squares at
  p = 2; f(p^2, k) for k >= 4 with 2 .. k-1 all residues (such as
  f(529, 4)) still searches, since only Fermat's four-squares theorem
  rules it out, and hv wants a proof he can follow before adding that.
- pctul: batches in pcoul's order. Each prime's batches are sorted as
  prep_forcep() lists them for the other types (by primary, then its
  power in divisors[].div order, the likelier early solutions first),
  with a batch that allocates nothing last; hv: that helps while still
  searching for the minimum, and is neutral for a proof.

### Stage 6: -c and -m

- The helper of section 5 in coulvec.c; modfix against a batch's
  class.
- Tests: a search under `-c` finds what it finds without; `-m`
  restricts to the class given.

### Stage 7: the constraints gtauseq knows

hv (2026-11-18): gtauseq spots that f(9, 3) is impossible only with at
least -c27, and f(18, 4) only with at least -c36. So: analyse the
constraints gtauseq knows, check that coulvec.c has the same, check that
pctul takes advantage of them where it can (at the batch stage above
all), and decide which checks to make automatically rather than only
under -c. Needs stage 6, which teaches coulvec.c a_i > 1.

Inventory, Perl side (lib/Type/Tauish.pm unless noted), each rule to be
stated as a claim about tau and checked:

- `apply_m()`, for each modulus m up to -c: if tau(n) = 2, avoid
  v_i == 0 (mod m) for prime m; `test_series()` (beyond some bound,
  v_i == 0 (mod m) is impossible when tau(m), or that of the least
  m_2 or m_3 the exponents can grow to, exceeds tau(n) or divides it
  badly); `test_m_rad_m()` (xp^y (mod p^{y+1}) with y + 1 not dividing
  tau(n); where tau(n) / tau(m) is odd, the cofactor must be a residue
  mod each prime of m and of m.rad(m); for p = 2 the further
  non-residues mod 2^{y+1}, such as 3 (mod 4)).
- `check_fixed()` / `find_fixed()` / `fix_power()` (311): a position
  whose unknown part must be a square or higher power fixes the form of
  d; with two, the Pell equation (317).
- `fix_fact` (-fact, lib/Constraint/Fact.pm); `check_mult()` (dependent
  n, done in 4.12); `check_exceptions()`; -b, -cp, and the -m, -mq, -mm
  overrides.

C side: coulvec.c's `apply_m()` has four rules: v_i == 0 (mod m) when
t_i < tau(m) (or equal, above a minimum); m/rad(m) times a unit
(mod m) when tau(m/rad(m)) does not divide t_i; non-residues mod m for
odd t_i; the p^6 + 1 factorization for t_i = 7. Compare rule by rule
with the Perl, and list each gap both ways (for example the Perl's
mod 2^{y+1} residues and `test_series()`'s m_2 and m_3 bounds).

What pctul's batches already capture, for forced primes only: every
rule about the exact power of p at each v_i (the levels of 4.4 are
those rules, in full), and since 0017 the residue mod an odd forced p
of a cofactor that must be a square. That is why pctul reports f(9, 3)
as 406 at startup with no -c. Not captured:

- p = 2: an odd square is 1 (mod 8), and the cofactor of an even
  square is restricted mod 8 likewise. This would go in the builder
  next to the odd-p residue check.
- Across primes: one prime's batch fixes d mod p^j, and another's
  leaves a square whose residue mod p^j that then decides. Today this
  is found only when the square's roots are computed at apply time
  (`square_afresh()`), and the batch fails there.
- Unforced moduli: residues mod a small q (q > true_k, not dividing
  n) for a position that must be a square. Neither the batches nor
  the walks use these until q is allocated: the square walk works mod
  qq_i, and the Pell walk only checks solutions against qq_i.

Worked case, f(18, 4) (tau 6): pctul ends at once even with -x1e30 but
cannot say 406, and reports only that it found nothing. The batch of 2
with exactly 2^2 at v_1 = 18 + 2d needs d == 1 (mod 4); the batch of 3
with 3^1 at v_2 = 18 + 3d leaves v_2 = 3z^2, so z^2 = 6 + d == 3
(mod 4), which has no root: that combination dies in `square_afresh()`.
The only walks are of the two completing batches (d = 7 and d = 14),
and those count as valid batches, so the final "no valid arrangement"
is not reported. (To verify against -dB once the stage starts.)

Decisions (hv, 2026-11-18):

1. Which checks run automatically: ideally, everything pc?ul can find
   that would make a material difference, with no need to ask; -c
   should then have little reason to exist. "Material" is decided case
   by case with a timing test against a case it applies to. Candidates
   so far: the p = 2 residue rules in the builder (cheap, per prime);
   residues mod small unforced q as a filter in the square and Pell
   walks; the cross-prime case at batch-combination time, if cheaper
   than root-finding.
2. 406 claims that no solution is possible, at any -x; 500 that there
   is none up to zmax, though there may be one beyond. Where all but a
   finite set of d are ruled out, check those members of the set that
   lie below zmax, as for any d. If none is a solution, report 406 when
   every member lies below zmax, and 500 when some lie above it. For
   f(18, 4) the finite set is the d of the completing batches.
   (The dependence check of 4.12 tests such d whatever zmax is; that
   is a separate claim, and stays as it is unless hv says otherwise.)
3. -c in pctul: kept as it is for now; as checks become automatic it
   should matter less, and whether to retire it is decided afterwards.

Tests: f(9, 3) and f(18, 4) report 406 with no -c; each check made
automatic is shown by a case it decides and by a broken build the soak
test catches; under -c, pctul finds the same solutions as without.

### Stage 8: the rest, exercised

Nothing new is written unless something fails. Each of `-W`, `-k`,
`-j4`, the flip, `-a`, `-b`, `-o` and `-X` with a lowered maximum is
run on a pctul case where it does something, and compared with the
sieve. Report which were exercised on what, and which could not be
(no case found where it applies) and so remain only argued.

Then a section on type t in the pcoul-internals skill, which hv
wants: the affine form and the one idea of 4.3, the levels and
batches of a forced prime, `p^0`, `true_k`, dependent n. Durable
knowledge only, as that file asks.


## 9. The planner

The planner design (branch `planner`, over calibrate) and this one
touch each other in few places. None of them blocks either.

### 9.1 Order, and what each must leave alone

- Stages 0 to 2 here change shared code that calibrate has changed
  heavily (`walk_v()`, `gate_walk()`, `limit_p()`, `update_chinese()`,
  `reject_single()`, `apply_batch()`). They are mechanical, and hv
  rebases calibrate over master. Decided: stages 0 to 2 go to master
  before the planner work starts, so that no planner code is written
  against bare offsets.
- Done: calibrate rebased over f98cbb5 (2026-11-17, tip e5efc12), each
  conversion made in the commit that brings in its site. coulint.h
  lost its own `TYPE_OFFSET()`, `target_t()` and `target_lcm` to
  coul.h. Resultants by `TYPE_RES()`: `ke_root_node()` in coulplan.c,
  `cm_generic()` and its cache key in coulcost.c. The greatest v_i by
  `dtov()` in `kern_xtop()` (coul.c), and in doubles by a new
  `dtov_d()` in coulint.h for `cm_root_price()` and `mock_walk_v()`.
  The modulus TYPE_MULT(i).aq / q_i in place of aq / q_i in the
  walk_1_set() estimates of `ja_cost()` and -Wa, and in the root
  counts of `gq_roots()`, `ke_root_node()` and `ke_plain()`. Each is
  written to give pcoul the same doubles as before, and a set of 22
  calibrate runs gave the same logs before and after (bar the Pell
  fix). Left for 9.2: the sizes of values (zmax / q_i).
  hv is wary of estimates in doubles at all, since some cases will
  want values beyond 10^308.
- Stages 0 to 2 also changed some interfaces that calibrate code may
  call: `reject_square()` and `reject_mod()` take the position,
  `least_is_best()` no longer takes a fold (`batch_is_best()` is its
  batch form), `apply_primary()` takes (fpi, bi), `g_q0` became
  `g_node`, `relative_valuation()` is gone, each type's
  `TYPE_OFFSET()`, `TYPE_MULT()`, `target_t()` and `target_lcm` are in
  coul.h (with `TYPE_RES()`), `prep_mintau()` and `cvec_init()` no
  longer take the lcm and n, and `gate_walk()` forms its estimate
  through `gate_span()`.
- Stages 3 to 7 are almost all under TYPE_t or in the batch builder,
  which the planner does not price (its 5.5: `-f` is chosen with no
  cost involved). They can proceed beside planner stages 0 to 5.
- This design adds no option (planner section 6: no new option for
  what the planner could choose) and no action kind: every pctul
  batch is an `A_FORCED` act.

### 9.2 What the planner's prices must not assume

The planner prices subtrees for pcoul. For those prices to be right
for pctul as well, three assumptions must be absent from them. It
costs nothing to leave them out now.

- **The modulus at a position is a_i.aq.** A closed form that divides
  aq by q_i (the cost of a walk per step, the count of roots of a
  square) must use qq_i. On calibrate the functions that form sizes
  from zmax or aq are, in coulplan.c, the `gr_`, `gq_`, `ke_`, `wa_`
  and `wf_` estimators and `ja_cost()`; in coulcost.c `cm_trial()`
  and `cm_tail()`; in mock.c `mock_walk_v()`. The moduli of these
  were converted in the rebase (9.1); **[verify]** the rest as the
  price hooks of planner stage 1 are made from them.
- **A walk's length is in d; a value's size is not.** The steps of a
  walk are zmax / aq whatever the type. The values tested at position
  i are near a_i.zmax / q_i, up to six bits more than at the first
  position for k near 66, so the size class a test is priced at
  differs by position.
- **A Pell equation is not always nearly free.** `KE_PELL` and the
  near-zero walk price for two squares assume a small right side.
  Under type t it is n.(i - j) (4.9). After stage 5 here, price it
  from the size of N if that proves to matter.

### 9.3 Choices this design fixes by rule, for the planner later

Each is a choice between complete ways of covering a node, so each
would enter the planner as a tactic of the TC_FORCED kind, with a
price, and not as an option:

- Tails. Leaving the single-position batches of a prime to a tail
  (4.6). The planner design already has this as a later step of its
  5.5 ("expand this prime's singles" against "take the tail"); pctul
  would join it there. With `p^0` in patterns a tail and "p divides
  d" no longer look alike in the log, so the obstacle of 4.6 is gone
  by then. Such primes would also need their class from the builder
  rather than `update_chinese()`, where p can divide a_i (4.6).
- Splitting a plain batch that has several classes left. It can be
  split into one batch per class, each with aq larger by p. For p = 3
  dividing n that is two batches; for p near n it is absurd.
- Folding for odd p when one class is left for an extra power (4.5
  keeps pc[oar]ul's rule: p = 2 only).

A stride sieve, when it exists, is not a tactic: it covers the same
node the same way. It belongs inside the TC_WALK price, as the
cheaper of two ways of doing one walk (planner P4).

### 9.4 The run level and the scoreboard

- `plan_run()` (planner 5.7) prices a run as the sum over its batches
  and chooses `-f`, highpow and the fallback strategy. For pctul the
  `-f` dimension is pinned; the rest applies unchanged.
- Recovery replays (planner P3): pctul's batches are read back from
  the pattern, so no new record is needed.
- The random-plan test (planner 4.9, `-dJr`) should run for pctul
  too once both exist: it tests coverage by the tactics, as the soak
  test of section 7 tests coverage by the batches.
- The shard file of `evalplan` (planner 7.2) lists n, k and
  arguments. Give it the program as a field from the start, so that
  pctul shards can be added without a change of format.
- The cost table is measured by pcoul's benches and keyed by the kind
  and size of a test, not by type. pctul should be able to use it as
  it stands. **[verify]** once pctul runs under a calibrate build.

### 9.5 Later speed-ups

- Inverting a_i in `update_chinese()`. Its large path calls
  `mpz_invert()` on the modulus p^x, and its single-limb path
  `ppow_invert()`. Both ignore that a_i < MAXK is tiny: for a prime
  to m, a^{-1} mod m = (1 + t.m) / a with t = -m^{-1} mod a, which
  needs one `mpz_fdiv_ui(m, a)`, a single-word inverse mod a, and one
  each of `mpz_mul_ui`, add and `mpz_divexact_ui`, with no gcd on
  the large number and no use of m being a prime power. Consider a
  helper (say `invert_small(r, a, m)`) for both paths. How often the
  large path is reached depends on which (n, k) are attempted, so
  judge it by profiling pctul, not by assumption.


## 10. Risks

1. **A missed case in the batches.** The one new piece of
   mathematics, and a miss is a false proof. Mitigation: the rules
   are stated constructively and were checked (4.11); the soak test
   repeats the check against the real program, and must be shown
   able to fail.
2. **Stages 1 and 2 change pc[oar]ul's hot paths.** A slip changes
   existing proofs. Mitigation: 8.1, and the changes are
   substitutions that vanish when the multiplier is 1.
3. **Recovery of a batch that allocates nothing.** New syntax, and
   the typical pctul line depends on it. It needs hv's decision
   before stage 3, and t10init cases for each kind of line.
4. **Large primes among the forced primes.** n prime puts a prime of
   up to 32 bits in `forcep[]`. `ptoi[]`, `sprimes[]`, `pfreev` and
   the `fp_need` bit vector were sized for primes up to k.
   `apply_pfreev()` already passes over p > `lastprime`; `fp_need`
   fails loudly at 32 forced primes. **[verify]** every index by a
   forced prime.
5. **Squares below a forced batch.** Finding the roots afresh (4.8)
   is simple but its cost at production size is unmeasured.
6. **The gate.** `gate_walk()` is rewritten in the terms of 4.3 and
   must still decide as before for pcoul.
7. **The bigger wins are elsewhere.** For prime and semiprime n this
   design gives a correct pctul whose time is all in one walk. Do not
   judge it by its speed on those until the sieve exists.


## 11. Open questions for hv

Settled in the first review, and recorded above: the name `true_k`
(4.1); `p^0` for a batch that allocates nothing (4.6); `-f` and `-F`
refused (4.6); roots found afresh under a forced batch, subject to a
timing test (4.8); dependent n stops the run, `-jd` forces the
search, and a case that is fixed but not dependent gets a warning
(4.12); `TEST_TSEQ` (section 7); stages 0 to 2 to master before the
planner work starts (9.1); `TauSeq.pm` pointed at pctul after stage
5, and a section in the pcoul-internals skill (section 8).

Still open:

1. The wording of the 313 warning of 4.12 (code settled in stage 3).
2. Whether pc[oar]ul should also find a square's roots afresh below a
   forced batch: figures in the record of stages 4 and 5.
3. Stage 7 (decided in principle, 2026-11-18): automatic checks
   wherever they make a material difference; 406 after checking a
   finite remaining set only when all of it lies below zmax (else
   check those below zmax, and report 500).


## Appendix A: reference values

Every d in the range with tau(n + i.d) = tau(n) for 0 < i < k, found
by sieving tau over the whole of [0, n + (k - 1).max]. Where more
than eight exist the first eight are given, with the count.

| n | k | tau(n) | max | d |
|---|---|---|---|---|
| 13 | 4 | 2 | 600 | 30 48 90 150 198 210 360 408 (10) |
| 13 | 6 | 2 | 40000 | 90 210 3660 15000 16170 38940 |
| 97 | 7 | 2 | 2000000 | 33390 99960 120750 390390 631260 813120 1363950 |
| 2 | 5 | 2 | 2000 | none |
| 15 | 5 | 4 | 3000 | 6 18 36 126 144 188 194 288 (26) |
| 15 | 7 | 4 | 400000 | none |
| 202 | 5 | 4 | 300000 | 360 7980 11220 21000 22620 26040 33540 52800 (35) |
| 323 | 6 | 4 | 60000 | 130 546 616 666 2610 2724 2830 2874 (208) |
| 323 | 8 | 4 | 3000000 | 546 666 3864 5858 6048 6948 9450 9666 (1010) |
| 8 | 5 | 4 | 60000 | none |
| 27 | 4 | 4 | 200000 | 58 64 88 158 182 188 190 338 (2985) |
| 30 | 6 | 8 | 2000000 | 376 388 1132 1228 2596 5176 5596 5932 (1067) |
| 24 | 5 | 8 | 100000 | none |
| 12 | 3 | 6 | 3000 | 8 16 20 32 40 56 80 112 (64) |
| 12 | 4 | 6 | 20000 | none |
| 18 | 3 | 6 | 3000 | 157 457 557 757 829 913 1165 1457 (14) |
| 18 | 4 | 6 | 100000 | none |
| 20 | 4 | 6 | 300000 | 24 48 72 168 192 216 336 384 (382) |
| 45 | 4 | 6 | 300000 | 54 108 162 378 432 486 756 864 (224) |
| 98 | 4 | 6 | 1000000 | 109 409 1369 10369 11065 11449 13609 20109 (76) |
| 175 | 4 | 6 | 1000000 | 300 750 1800 2550 3750 7500 8550 9000 (183) |
| 50 | 5 | 6 | 20000000 | none |
| 243 | 4 | 6 | 20000000 | none |
| 60 | 4 | 12 | 2000000 | 12 24 48 72 144 216 504 576 (5069) |
| 96 | 4 | 12 | 20000000 | 210 394 1054 1114 1650 2746 3922 4510 (3523) |
| 36 | 2 | 9 | 2000 | 64 160 189 220 405 448 640 1053 (12) |
| 36 | 3 | 9 | 5000000 | none |
| 100 | 3 | 9 | 5000000 | none |
| 49 | 3 | 3 | 20000000 | 120 240 5280 9360 |
| 9 | 3 | 3 | 100000 | none |
| 2401 | 3 | 5 | 20000000 | none |
| 64 | 3 | 7 | 200000 | none |


## Appendix B: batches of small cases

As the rules of 4.5 give them. Positions are 0 to k - 2, position i
being n + (i + 1).d; "." is no power of p there.

n = 13, k = 5 (tau 2), four positions.

    p = 2    . . . .           d == 0 (mod 2)
    p = 3    . . . .           d == 0 (mod 3)
             3 . . 3           d == 2 (mod 3)
             . 3 . .           d == 1 (mod 3)
    p = 5    . . . .           d == 0 (mod 5)
             5 . . .           d == 2 (mod 5)
             . 5 . .           d == 1 (mod 5)
             . . 5 .           d == 4 (mod 5)
             . . . 5           d == 3 (mod 5)
    p = 13   . . . .           no constraint (level 0)
             13 13 13 13       d == 0 (mod 13)

p = 2 has no batch with d odd: positions 0 and 2 would both be even,
and one of them divisible by 4. Every batch but the first of each
prime completes a position, and is tested at once.

n = 323 = 17.19, k = 6 (tau 4), five positions, p = 17.

    level 0   . . . . .                    no constraint
    level 1   17 17 17 17 17               d == 0 (mod 17)
              17^3 17 17 17 17             d == 4590 (mod 4913)
              17 17^3 17 17 17             d == 2295 (mod 4913)
              17 17 17^3 17 17             d == 1530 (mod 4913)
              17 17 17 17^3 17             d == 3604 (mod 4913)
              17 17 17 17 17^3             d == 918 (mod 4913)

The second is tauseq(19) in the multiples of 17.

n = 12, k = 5 (tau 6), four positions.

    p = 2, level 0   . 2 . 2^5             d == 5 (mod 16)
           level 1   2 2^5 2 2^2           d == 10 (mod 32)
           level 2   2^2 2^2 2^2 2^2       d == 0 (mod 8)
    p = 3, level 0   . . 3 .               d == 1 (mod 3)
                     . . 3^2 .             d == 2 (mod 3)
                     . . 3^5 .             d == 77 (mod 81)
           level 1   3 3 3 3               d == 0 (mod 9)
                     3^2 3 3 3^2           d == 6 (mod 9)
                     3^5 3 3 3^2           d == 231 (mod 243)
                     3 3^2 3 3             d == 3 (mod 9)
                     3 3^5 3 3             d == 237 (mod 243)
                     3^2 3 3 3^5           d == 240 (mod 243)

For p = 2 at level 0, position 3 (n + 4d) is critical and 3 + d is
even for every odd d, so there is no plain batch. At level 2 the one
class left is d / 4 even, which is why the modulus is 8 and not 4.
For p = 3 at level 1 the plain batch has d == 0 (mod 9): the classes
3 and 6 mod 9 belong to the batches with 3^2.
