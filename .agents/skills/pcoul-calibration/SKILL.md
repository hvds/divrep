---
name: pcoul-calibration
description: How pcoul costs its own work - the brief this began from and its aims
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
