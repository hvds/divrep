# pcoul batch harness - design v0.1

## Motivation

pcoul's search over [1, v_max] decomposes into independent batches
(one -f-determined listing, each batch runnable as its own process via
-b/-r). Today's normal usage runs the full listing in one pass with a
single (j, g[, G][, W]) choice for the whole run - necessarily a
compromise, since different batches have very different cost profiles
(confirmed repeatedly in the calibration work: batch cost within one
(n, k, f) listing can span many orders of magnitude).

A harness that dispatches individual batches (or contiguous ranges)
with per-batch settings, and tracks completeness across the aggregate,
would let each batch use settings tailored to its own expected cost,
and would open the door to prioritizing batches by estimated
likelihood of yielding an improved candidate (not itself part of this
harness - likelihood estimation is external, e.g. a modified mintau
considering the smallest way to satisfy tau(prod v_i) = n^k, per
hvds - but the harness needs to be able to consume such a priority
ordering when one is supplied, and to behave sensibly without one).

This also decouples the calibration problem from "find one setting
good for an entire run" (hard - the compromise problem) to "find a
setting good enough for one batch, given its expected cost class"
(smaller, more tractable - see the companion calibration status doc).

## Requirements

1. **Invoke pcoul per batch or per contiguous batch range**, each as
   its own process (matches existing -b/-r support; -R always, per
   the existing calibration tool's convention - no resume semantics
   needed at the harness's process-management level, only at its own
   ledger level).
2. **Persistent per-batch ledger**, surviving across harness restarts,
   holding at minimum:
   - batch id
   - largest v_max this batch has been exhaustively confirmed against
     (or "not yet run", or "found candidate v_0" - see completeness
     below)
   - settings used (j, g/G, W/Wx) for the run(s) that produced that
     confirmation
   - wall-clock time spent on this batch so far (cumulative across
     any restarts/re-runs)
   - status: exhausted-to-X / found-candidate-X / in-progress /
     not-started
3. **A single, authoritative "current best v_max"**, updated whenever
   any batch reports a candidate strictly smaller than the current
   value. Because pcoul batches are listed deterministically for a
   fixed (n, k, f, modulus), and because a batch exhaustively confirmed
   against a LARGER v_max automatically proves the SMALLER one too
   (exhausting up to X proves nothing below X, which implies nothing
   below any Y < X) - tightening the bound never invalidates a
   completed batch's confirmation, it can only reduce or eliminate the
   remaining work for batches not yet caught up to it. This is a
   materially simpler situation than a live monolithic process
   discovering a tighter bound mid-run (where the original design
   doc's calibration work deliberately avoided auto-restarting
   anything, given the complexity of a single continuously-running
   process's internal state) - for the harness, since batches are
   independent, dispatched, restartable units, it is both safe and
   natural to have every new batch dispatch (or continuation) target
   the CURRENT best v_max, not whatever value was current when that
   batch was first queued. **Recommendation: auto-propagate.** No
   restart risk analogous to the monolithic case, since each batch
   dispatch is already a fresh process invocation.
4. **Completeness proof / verification pass**: given the ledger and
   the final best v_max, confirm that every batch in the full (n, k,
   f, modulus) listing has ledger status "exhausted-to-X" for some
   X >= final v_max (or has itself been superseded, i.e. found the
   final candidate). Any batch not meeting this - not started, only
   partially exhausted below the final bound, or timed out - is a gap
   that must be reported, not silently ignored. This verification pass
   is the deliverable hvds specifically flagged as essential: "any
   such approach needs to come with tools to help confirm that an
   aggregated run is truly a complete run."
   - Should be runnable independently of the harness's own dispatch
     loop (i.e. as an audit tool against the ledger file, so a human
     can verify a claimed-complete run without re-trusting the
     harness's own bookkeeping blindly).
   - Should distinguish "gap because not yet attempted" from "gap
     because attempted and timed out" (the latter needs a bigger
     budget or different settings, not just more wall-clock of the
     same kind).
5. **Per-batch settings selection**: given a batch (its -a listing
   pattern, and whatever cost signal is available - the analytic
   estimator in Calibrate::Recursion, a quick empirical trial via
   Calibrate::Search's existing racing machinery, or a hybrid), choose
   (j, g[, G][, W]) for that batch's dispatch. See the calibration
   status doc for what's usable today vs still open.
6. **Priority queue for dispatch order**: when wall-clock budget is
   finite and not every batch can run to exhaustion immediately, the
   harness needs an ordering. Two independent orderings matter and
   should be kept separate:
   - **cost-based** (minimize total wall-clock to reach full
     completeness) - this is what the calibration/estimator work
     feeds.
   - **likelihood-based** (maximize chance of finding an improved
     candidate soon) - external input, not computed by the harness
     itself, but the harness's queue needs to accept and honor an
     externally-supplied priority when present, falling back to
     cost-based (e.g. cheapest-first, to bank easy completions) when
     not.
7. **Handling in-flight work when the bound tightens**: per point 3,
   propagate the new bound to future dispatches automatically. For a
   batch *currently running* against the old (looser) bound: allowing
   it to finish is simplest and safe (it still produces a valid
   exhausted-to-X confirmation, just against a larger X than strictly
   needed - wasted work, not wrong work). Killing and restarting it
   against the tighter bound is a possible refinement but not required
   for correctness; recommend deferring until real usage shows the
   wasted work is material.

## Open questions (for hvds)

- Exact mechanics of resuming/continuing a batch that was previously
  run to a smaller v_max than currently needed: does pcoul support
  "confirm you've already exhausted this batch to X, extend to Y"
  directly (something like a variant of the recovery/-R log
  mechanism), or does it always mean a fresh run over [1, Y] for that
  batch? This materially affects the ledger design and how much
  re-work "bound tightened after batch already confirmed" actually
  costs.
- Does -m/-p/-c (partial-search options) interact with batch
  boundaries in a way the harness needs to know about, or are they
  fully orthogonal (a batch is a batch regardless of whether the run
  is a full or partial search)?
- Format/location for the priority-ordering input the harness should
  accept from external likelihood-estimation tools - TBD once such a
  tool exists (out of scope for the harness itself).

## Explicitly out of scope for v1

- The likelihood-estimation heuristic itself (mintau-based or
  otherwise) - external input only.
- Auto-tuning settings via live feedback within a single batch's run
  (i.e. mid-run adaptive j/g changes) - out of scope; settings are
  chosen once per dispatch.
- A pcoul library/API refactor (discussed and estimated separately -
  see chat, 2026-08 session) - the harness can be built against
  today's process-per-batch, log-file-parsing interface; a cleaner API
  would reduce overhead and brittleness but isn't a prerequisite.
