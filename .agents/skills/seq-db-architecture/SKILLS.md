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
    forced-prime "tail" entirely (see pcoul-internals skill's
    apply_null section). Non-`cul` runs never pass `-f` at all.

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
  - `402`/`403`/`404`/`405`/`406`: various "ugly"/error terminations
    (e.g. `402` = "all values ... disallowed") - some of these
    correspond to a *proven impossible* claim (`tauf.impossible`,
    `taug` bound update), which is also a "final" (exhaustiveness)
    claim and worth treating with the same suspicion as a `200` if
    auditing this bug.
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
