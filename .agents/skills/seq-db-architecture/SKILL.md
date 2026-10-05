---
name: seq-db-architecture
description: Architecture of the Seq::* results-database layer (run harness, tauf/taug tables) and how it links to pcoul/pcaul/pcrul log files
---
## Seq::* results-database / harness architecture

This is the Perl/DBIx::Class layer (`lib/Seq/*.pm`, `lib/Type.pm`,
`lib/Type/*.pm`) that capures results from invocations of the C
(`pcoul`/`pcaul`/`pcrul`) and perl (gtauseq, harness, oul) search
programs, and manually injected results via 'inject'.  Durable notes
for anyone working on result-provenance, backfill, or auditing tasks.

### Access pattern

- `Seq::Db->new($type, $recreate)` opens a MySQL connection (DBIx::Class
  `Seq::Db::Schema`) and `deploy()`s the schema for `$type`
  (idempotent - it rewrites `CREATE TABLE` to `CREATE TABLE IF NOT
  EXISTS`). `$type` is a `Type::*` object (e.g. `Type::OneSeq`, dbtype
  `"o"`) which supplies `dbname`/`dbuser`/`dbpass`/`owner`/`logpath`.
- Never construct SQL by hand against table names directly without
  checking `lib/Seq/Table.pm`'s `define()` - it's a thin DSL over
  DBIx::Class column specs (`'key uint n'`, `'flags(...) status'` for
  bitfield-style flags stored in one `status` column, `'maybe ...'` for
  nullable, `'modlist ...'` for a serialized list column). The literal
  table/column names it produces are what raw SQL must target.

### Table hierarchy (for `Type::OneSeq`, dbtype `"o"`)

- **`taug`** (`Seq::TauG`, keyed by `n`): tracks `g(n)` = largest `k`
  with `f(n,k)` known to exist. `ming`/`maxg` bound it; `status` flag
  `complete` means `ming==maxg` AND every `f(n, 2..maxg)` is proven
  minimal.
- **`tauf`** (`Seq::TauF`, keyed by `n,k`): tracks `f(n,k)`, the
  smallest known difference `d`. Column `f` is the current best value;
  `status` flag `complete` means `f` is *proven* minimal (this is the
  "final" state); flag `impossible` means this `(n,k)` was proven to
  have no solution at all (an "ugly" result). A `tauf` row can have
  `f` set (non-final, upper bound only) without `complete` being set.
- **`run`** (`Seq::Run`, keyed by `runid`, FK to `tauf` via `n,k`): one
  actual invocation of the search binary. Key columns: `n`, `k`,
  `owner`, `optn`/`optx` (the `-n`/`-x` search range), `optc`, `optcp`,
  `optm` (modlist), `status` flags including `complete`, `running`,
  `optimizing`, `fix_power`, `old`, `partial`, `cul`.
  - **`status.partial`** is the flag that distinguishes a "final" claim
    from a mere upper-bound improvement: a `partial` run's `good()`
    path (`Seq::TauF::partial`) only ever sets `f(n,k) <= good`
    (`tauf.complete` is NOT set). A non-partial run's `good()` path
    (`Seq::TauF::good`) sets `tauf.complete(1)` - a proven-minimal,
    "final" claim. `Seq::Run::BisectG`/`BisectFP`/`ShardTest` are the
    subclasses that produce `partial` runs (see their `finalize()`).
  - **`status.cul`** runs pass `-f$k` (force_all == k) to the search
    binary via `command()`, which - for `TYPE_o` - suppresses the
    forced-prime "tail" entirely (see pcoul-internals skill's "Forced
    primes, batches, and the tail" section). Non-`cul` runs never pass
    `-f` at all - though see the "gotchas" section below, since this
    only holds for automated/harness-driven runs.

### Run <-> log file linkage

- `Seq::Run::logpath($type)` returns
  `"$type->logpath/$n.$k-$runid"` - i.e. one log file per run row,
  named `<n>.<k>-<runid>` under the type's configured log directory.
  This is the only linkage; there is no log path column in the DB.
- `Seq::Run::finalize()` is the sole parser of these logs. It reads
  every line, buckets them by the 3-digit code prefix (`^(\d{3}) `),
  and interprets specific codes (some of which are generated only
  by the perl programs):
  - `001`: intro line from `coul.c:report_init()` - full effective
    command line / parameters (see pcoul-internals skill). Always the
    first line; not parsed by `finalize()` itself but is the
    authoritative record of what parameters that run actually used
    (more reliable than reconstructing from the `run` row alone, since
    e.g. `-I` recovery patterns, `-a`/`-b` batch selection, and other
    binary-only flags aren't stored in the DB).
  - `200`: `f(n,k) = d (Ts)` - success, `$good = d`. Combined with
    `run.partial`, this is what produces either a final (`complete`)
    or partial `tauf` update.
  - `500`: `f(n,k) > d (Ts)` - exhausted the requested range without
    success; only ever improves a *lower* bound on `f`, via `bad()`;
    never "final" in the sense this project cares about.
  - `402`/`403`/`404`/`405`/`406`: "ugly"/error terminations - `402`
    all values (mod m) disallowed, `403` known impossible by
    exception, `404` a divisibility requirement fails, `405` a fixed
    power is a non-residue (mod m), `406` no valid arrangement of
    powers. All five are static/modular impossibility proofs - they
    never touch the recursive prime-allocation search machinery
    (`mintau()`/`limit_p()`/the tail/`apply_null()` mechanism, see
    pcoul-internals skill) at all, so bugs confined to that machinery
    can't affect them. They set `tauf.impossible` (and `complete`) via
    `Seq::TauF::ugly()` - a "final" (exhaustiveness) claim, just one
    reached by a completely different code path than a `200` result.
  - `211`: per-position confirmation line from `coul.c:report_211()`,
    format `211 Sequence <i>: <tau> = tau(<value> = <factorisation>)`.
  - `301`: progress/test-order-tuning line, parsed for `optimizing`
    runs and for the last-fail depth.
  - `309`: prep-time line.
  - `201`: dependency line (`f(n,k)` derived from another sequence).
- A run's parameters as actually run are therefore fully captured by
  the `001` line of its log file; the `run` table's `optn`/`optx`/etc.
  columns record what was *requested*, which should normally agree but
  the log is ground truth for anything the DB schema doesn't carry.
- `run.runtime`/`run.preptime` are populated by `finalize()` itself
  from whichever `200`/`500`/`40x` line's own reported elapsed time it
  parsed (minus `preptime`, from a `309` line) - not independently
  measured. There is no run-level timestamp/date column at all.

### The non-`pcoul` programs, and their own init-line formats

`finalize()`'s numeric-code parsing is shared across every program
that writes these logs, but each program's `001`/`100` *init* line
(the very first line, recording what was actually run) has its own
format, and only some embed `n,k` directly in a way worth relying on:

- **`pcoul`**/`pcaul`/`pcrul`: `001 [recover ]pc?ul(n k)[ -flags...]`
  (see pcoul-internals for the flags). `n,k` always present.
- **`oul`** (the older, independent Perl forerunner of `pcoul` - NOT a
  wrapper that invokes it - same algorithm, different language):
  overwrites `$0` to `"oul($n $k)"` before logging, so its `001` line
  reads `001 oul(n k) -flags...` too - `n,k` recoverable the same way
  as `pcoul`'s. Uses `times() - $t0` (real elapsed time) for its own
  `200`/`500` lines, so its reported runtime is legitimate.
- **`gtauseq`**: a third, independent Perl implementation with a very
  different algorithm (checks a contiguous chunk of the search space
  linearly from 0 until it finds a solution, rather than the
  prime-allocation recursion `pcoul`/`oul` share - hence the `checked`
  concept it records, now mostly obsolete). Its init line is
  `100 ./gtauseq -y<type> ... n k` (code `100`, not `001` - `n,k` are
  the last two whitespace-separated tokens). Also uses real elapsed
  time.
- **`inject`**: records an already-known candidate directly, without
  searching. Init line `100 ./inject -y<type> n k d` (code `100`,
  `n,k,d` all literal). Self-`finalize()`s. Its reported runtime comes
  from a bare `times()` call taken right after a single candidate
  check - NOT real search time, and not a legitimate signal for how
  long a real search would take. `run.partial` is set unless its `-f`
  ("full") option was given - used mostly for recording upper bounds,
  occasionally with `-f` to inject a complete/proven result, and nothing
  in the log distinguishes those two cases after the fact.
- **`harness`**: only invokes the other programs - never itself
  generates a log or a `run`/`tauf` row.

### Gotchas when reconstructing a run's history from the DB alone

- **`tauf` doesn't record which `run` completed it.**
  `Seq::TauF::good()`/`ugly()`/`bad()` are all handed the `$run` object
  by `Seq::Run::finalize()`, but none of them persist it anywhere - no
  `runid`/`last_run` column exists on `tauf`. To find out which
  specific run (if any) produced a given `tauf.complete`, you have to
  go to the logs themselves.
- **`tauf.status.complete` is set by three unrelated paths**, not just
  `good()`: also by `ugly()` (proven impossible - see above) and by
  `Seq::TauF::depends()`/`update_depends()` (this `n,k`'s value was
  *inherited* from a different `n` via a `201` dependency line - no
  run for this `n,k` itself ever claimed anything; check
  `status.depend` to catch this case before trusting `complete` alone).
- **`run.status.cul` is only meaningful for automated, harness-driven
  runs.** `Seq::Run::command()` is what makes `cul=1` runs pass `-f$k`
  to `pcoul` (and `cul=0` ones dispatch to `gtauseq` instead of `pcoul`
  entirely) - but a manually-reserved run (`./oul -I -yo n k`, which
  just calls `prep_run()` to create the DB row and log path without
  running any search) never sets `cul` at all; it's `0` regardless of
  what was actually typed by hand afterwards.
- **`run.status.partial` for a manual `oul -I` reservation is
  controlled by `oul`'s own `-p<cap>` option at reservation time** -
  an entirely different concept from `pcoul`'s `-p` (prime-range
  restriction) despite the shared letter. Passing `-p` to `oul -I`
  marks the reservation as intentionally partial; omitting it leaves
  `partial` at its default (0, ie "intended as a complete search").
