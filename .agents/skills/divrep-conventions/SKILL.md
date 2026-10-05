---
name: divrep-conventions
description: hv's coding conventions, review record and delivery rules for divrep; read before writing code or commit messages
---
# Conventions for a coding agent working on divrep

Compiled by Claude from hv's review comments and decisions in earlier
sessions on divrep (August to October 2026), and from a reading of master
at ce8f669 (built against Math-Prime-Util-GMP v0.54, 39982f872b).

Tags:
- [firm]: hv stated it, or enforced it in review.
- [inferred]: my reading. "[inferred, code]" means a convention visible
  in the code that I have no statement for.

Text in double quotes is hv's own wording, unless the sentence says it is
mine. Where I had only a summary of the exchange I paraphrase without
quote marks.

Coverage is uneven. C is well covered. Perl, shell and Makefiles are
thin: there are few review comments on record, and I say so rather than
fill the gap. All earlier delivery was as format-patch series that hv
applied himself, so nothing here was ever stated about pull requests.

---

# Part A: general rules

## A1. C

### Types, limits, names

- [firm] In much of his code hv typedefs the signed integer types too, so
  that "slong" stands out opposite "ulong" better than a bare "long".
  (divrep's types.h has only uchar, uint, ulong and bool so far.)
- [firm] "I have never been in the habit of unthinkingly adding casts, so
  they are usually reliable." A cast in this code is a claim that the
  range was checked. [inferred] Never add one to quiet a warning.
- [firm] Code that relies on an unstated bound gets: a named limit; a
  fatal error at startup if it is exceeded; a brief comment at each site
  that relies on it. Example: MAXK, and `/* needs MAXK < 67 */` at the
  two shifts.
- [firm] The limit is derived from the real constraint, not picked to
  look safe. I first set MAXK to 36 from the wrong constraint; the real
  one was a ulong bit vector in test_forcep(), giving 66.
- [firm] No magic numbers for type widths: the 32 in an assert became
  `8 * sizeof(uint)`.
- [firm] A helper keeps the domain it was written for. I proposed making
  simple_fact() take a ulong; hv: "I'm dubious about letting simple_fact()
  take a ulong: it is really intended for small numbers like tau values."
  The fix went into the caller instead.
- [firm] Name a value by what it tells the caller to do, in parallel with
  the existing families: BV_WALK (no good slot, so perform a walk) and
  BV_NEXTX, matching IS_NEXTX, replaced my BV_NONE and BV_DONE.
- [inferred, code] uint, ulong, uchar, bool from types.h; struct typedefs
  are t_foo with tag s_foo; enum typedefs are e_foo; enumerators and
  macros are upper case with a family prefix (IS_, BV_, TFP_, PUX_);
  small hot helpers are `static inline`.

### Layout

- [firm] One statement per line.
- [inferred, code] 4 spaces, no tabs. 80 columns (4 lines over in about
  11,000). Opening brace on the same line, functions included. A long
  signature breaks after `(`, parameters indented once, `) {` on a line
  of its own. No braces round a single statement. `case` is indented two
  spaces inside `switch`.

### Comments

- [firm] Terse. On why: "the intent is to minimize overall cognitive
  load (roughly a human equivalent of your tokens) involved in
  understanding both the what and the why of a chunk of code, and how
  much fits in a screenful is an important aspect of that." hv described
  his preference to Sonnet as "comments much terser than you usually like
  to write"; that holds for any model.
- [firm] A multi-line comment has its closing `*/` on a line of its own
  (a leading `*` on a text line can be mistaken for part of an
  expression) and is usually written as full sentences.
- [firm] A single-line comment can be a fragment: no capital, no full
  stop.
- [firm] No multi-line trailing comments.
- [firm] A comment says exactly what is meant; hv reads them word by
  word. On my "Show the allocations into diag_buf": "the original could
  be read as '... that are in diag_buf', 'write' is similarly ambiguous,
  'print' might work better". He also asked what one word in a comment
  of mine meant, and the comment had to be corrected.
- [firm] A comment gives the constraint, not the history of the code.
- [firm] A label or an early return can say what a comment would, and
  cannot go stale. On `goto do_process` in process_batch(): "I don't
  usually add goto's for the sake of it, but in this case the label is a
  useful indication to the reader - at this point we are committed to
  processing this batch".
- [firm] An idea that is set aside goes in TODO-coul or hv's own todo
  list. An agent lists it in its report as a parked idea.
- [inferred, code] TODO, FIXME and CHECKME are the markers in use.

### Functions and structure

- [firm] No extraction for its own sake. hv asked for an apply_6x()
  refactor "to bring the difference more clearly to light", looked at
  the result, and kept the inline code with better comments.
- [firm] DRY ("don't repeat yourself"). Two copies of logic that must
  agree become one function:
  new_best(), called by candidate() and apply_202(), after apply_202()
  was found to have copied only part of candidate().
- [firm] Rebuild derived state through the function that normally builds
  it. I restored a hidden level by copying fields; it had to be recreated
  with apply_single() so that .ti and .di were right.
- [firm] Use what the tables already hold. flip_valid_tau() is
  `return (t == 2*h*h) ? h : 0` with h = divisors[t].high; my version
  called mpz_sqrt().
- [inferred] One enum-dispatched state in place of parallel flags:
  have_rwalk became IS_RWALK, hv merged IS_MIDP into IS_BATCH and
  reordered insert_stack() to avoid repeated IS_DEEPER tests.
- [inferred, code] Long functions and goto-driven loops are normal in
  coul.c. Do not restructure them unasked.

### Errors

- (Failing loudly through fail() is already in pcoul-internals
  SKILL.md.)
- [firm] longjmp() is acceptable but rarely used. It was preferred to a
  stop flag and plain returns for ending a search early: "I think it
  makes the intent clearer, and it becomes a mechanism we can use in
  other places."
- [firm] Freeing what was acquired before exit (in the test programs, at
  least done_tau() and _GMP_destroy()) is a good habit to aim for, but
  not the top priority, and not at any cost.
- [firm] Log lines must start with a three-digit code, so that logs can
  be parsed automatically. [inferred, code] Every line a user sees starts
  with one. A new kind of failure gets a new code (517 was added for an
  unfactored -I entry that is too large). fail() accepts leaks but closes
  the log file.

### Preprocessor and build variants

- [firm] No large near-identical blocks under #ifdef and #else: they at
  least double the maintenance cost. My first
  cheb_factor patch duplicated the tmf functions and two tables; the
  accepted one defines everything once and enables it in the data (one
  bit of tmfb[], set in init_tmfbl() under MPUG_054).
- [firm] Where the duplication is small, an #ifdef in the tree is
  preferred to a separate branch: "that will also be far more
  informative in the git history at some future point when the ifdefs
  are removed in favour of the new code."
- [firm] Build flags only ever used together become one flag (MOCK_WALK
  and MOCK_LEAF, on calibrate). [inferred] Dead experimental flags are
  removed.
- [firm] Mock and instrumentation code is kept out of coul.c: the aim is
  a couple of lines per entry point there.

### Portability

- [firm] The GitHub Actions builds for Windows must keep working. A perl
  snippet in a Makefile rule of mine wrote a C string table that broke
  under CRLF line endings.
- [firm] PORTABLE=1 is for distribution binaries only. Build without it
  (so with -march=native) for timing and profiling.

### Performance

- (No malloc in hot paths is already in pcoul-internals SKILL.md.)
- [firm] Be wary of a native-integer fast path beside a bigint one. On
  my proposal for update_chinese(): "I've always worked on the basis that
  while I often run testcases on small numbers, most of the real compute
  will be done on much larger numbers - MPU and MPUG themselves have a
  lot of duplicated code paths (for bigints and for native ints), and a
  lot of discriminating tests and conversions, which I've often felt
  slowed down the pathways that really need to be as fast as possible."
  It went to TODO-coul. hv has since agreed that two fast paths
  (single-limb rejection of primes, one-limb primality) can go to
  master, after they were measured on production-like batches.
- [firm] Measure; do not assert. I said an #ifdef approach would need
  heavy duplication; hv asked for "a finger-in-the-air estimate of the
  proportion of lines", and it was 10 to 13 percent. An unmeasured remark
  of mine about the cost of prime_iterator_setprime() was also called
  out.
- [firm] Time with process CPU time, not wall clock: the load on hv's
  machine varies.
- [firm] Some settings are deliberate though they look wrong: the QS
  threshold of 90 bits; tmfb[], kept as a mirror of MPUG's own cascade.
  I also blamed hv's fork for a trial-division threshold that upstream
  introduced in 2014. Check the history and ask before "fixing" tuning.
- [firm] Getting proven results faster is the priority. Reproducible
  decisions are wanted too, but are "not the holy grail".

### What counts as bloat

- [firm] Long comments and long commit messages (A5 has the cases).
- [firm] A separate tool where an option would do: on calibrate, kplan
  is to become `pcoul -ap` and rungbench gives way to the VERBOSE build.
- [firm] A program for one case. hv much prefers enhancing pcoul to
  maintaining custom code for a specific case, even when it takes
  longer, provided other cases can be shown to benefit. Code used for
  many tasks gets far more exposure, so its bugs are far more likely to
  be noticed.
- [firm] A large working document in the top directory (calibration.md),
  and documents that record bugs already fixed.
- [firm] Any file in a delivery beyond what was asked for.
- [firm] Non-ASCII characters anywhere: code, comments, commit messages,
  documents.
- [firm] hv prefers Perl, C and assembler. [inferred, code] Every script
  in the repo is Perl, git-data included; there is no Python and no
  shell script. Do not add either, and do not add dependencies.

## A2. Perl

- [firm] `use warnings`, not -w on the shebang line.
- [firm] A new script follows the existing ones (find-shard and its
  neighbours). (Paraphrase.)
- [inferred, code] What those do: `#!/usr/bin/env perl`; then
  `BEGIN { do "./lib/reexec" for grep $_, $ENV{MATHPERL} }` unless the
  script has no maths content, in which case a comment says so; `use
  strict; use warnings;`; a hand-written option loop
  (`while (@ARGV && $ARGV[0] =~ /^-/)` with `$x = $1, next if ...` and a
  final `die "Unknown option '$arg'"`); usage as POD (`=head1`) in the
  script; `my($a, $b) = @_;` with no space after `my`; `qw{ }`; output
  lines carry the same three-digit codes as pcoul.
- [inferred] Values of -x routinely exceed 64 bits. Never do native
  arithmetic on them.
- Nothing else is on record.

## A3. Shell

- No stated rules on record.
- [inferred, code] The repo has no shell scripts; helpers that might have
  been shell (git-data) are Perl.

## A4. Makefiles

- [firm] A recipe that generates source must work on Windows (see
  Portability).
- [inferred] A change leaves every target building. A patch of mine for
  master broke `make ftest` and `make sq12` and had to be redone.
- [inferred, code] Each target lists its sources and headers and
  compiles the whole program with one gcc command. An optional feature is
  `ifdef X` / `DEFINES += -DX` / `endif` under a one-line comment.
  Variables are written `${VAR}`.

## A5. Review record: what I proposed, what hv said

Commit messages:

1. A long message for a new option. hv: "commit message is way too long,
   something like this would suffice:"

       pc?ul: new option -dL to force every diag to logs

       Get a 305/315 progress line written to logs at every opportunity,
       as with -d[wW], permitting fine control for automated testing.

2. "the commit message header line is illegally long, causing wrapping"
   and, of the same patch, "nothing in the commit message body is
   needed".
3. "commit message is way too long; first and last paragraph are
   unneeded, the rest can just describe the impact of the two one-line
   bugs".
4. For a test commit: it "should essentially say 'improve test coverage
   of recovery; 4 failing tests marked TODO' with just a brief summary
   of the failing tests (eg their legend)".
5. Subjects of mine ran past 80 characters, for example "under highpow,
   mark in 315 lines only the levels best_v() would not reproduce". The
   rule given: 50 or fewer preferred, 72 a hard limit.
6. An unsupported phrase in a message gets questioned: "it isn't clear
   why -dw's counting/expiry is 'orthogonal to what we want here'".
7. A word that undersells a bug gets corrected. I wrote that
   prime_iterator_setprime() "sieved" a byte past its segment; it wrote
   there, and the message was to be used in an upstream report.
8. I described a ushort to uint change as a fix. hv pointed out that the
   values hold "the primes dividing a target's _tau_ - I don't think
   we're close to breaching 64K for that." It stayed, described as a
   tidy-up.

Tests:

9. "these are functional tests, not unit tests. They should be described
   in terms of user experience - options used, or mathematical
   structures - rather than code internals." A STRATEGY_6X case is
   described by its structure, "... 2^{3+} . 2x^2 ...". A TODO legend may
   name the internals that characterize the bug.
10. "*what we test* should similarly be rooted in the user's experience.
    Thus 'recover midp does not retrigger process_batch' would be a
    better test if it set up a case that would quickly move on to a new
    batch, and verified that the new batch was described with the correct
    id."
11. A test of mine waited for a solution in a 6X batch. Candidates there
    are extremely rare and the point of the search is to cover the range.
    Clamp -x just past a known point and check a count that reproduces.

Design:

12. Stop flag against longjmp(). I argued that longjmp() jumps over
    unapply_batch(), is fragile and is "misleading under valgrind". hv:
    "How is it misleading under valgrind()?" I ran both paths under
    valgrind and switched to longjmp().
13. A sampling walk hidden from the log, to price a batch. hv: "I'm
    disturbed at the idea of a walk kept out of the log." Replaced by
    pricing from the cost table with no walk at all.
14. Compiled-in constants for mocked costs. They must come from tables
    measured on the machine.
15. Wall-clock timings feeding decisions. They became counts of work
    done, so identical runs decide identically.
16. hv on a per-level flag in the log: "if BV_6X i think we can set
    unsorted=0 to reduce logs clutter, since we don't rely on it anyway".
    Log lines are kept free of what nothing uses.
17. My separate choice_vlevel[] array was replaced by a level stored in
    each allocation: "it still feels sadly expensive, but I think it is
    necessary". Cost is weighed, but always loses to correctness.

Names:

18. File names cost-table and costtab.c, and later cost.c and pricing.c,
    were rejected for clashing under tab completion (rule in B1).
19. Option -gr1 became -ja1 and -ja2. kplan's job is to become `-ap`: a
    variant of -a, not a bit in -a's number and not a debug option, and
    -ap implies -a. (Items 13 to 15, 18 and 19 are calibrate work, not
    yet on master.)

Series and delivery:

20. Order of a series: "the core realization that we may be trying to
    recover from a point mid-way through process_batch(), motivating the
    is_recover flag, should be the first patch; the cleanups ... can
    follow, and require less explanation."
21. "the skills file should be forward-looking, it does not need to
    include details of fixed (or about-to-be-fixed) bugs".
22. A notes file I added to a patch tarball overwrote a file in the
    repo. Patches only; their file names are explanation enough.
23. Git bundles are not accepted.

Where hv accepted a "no": he asked for is_prime_ul() to come from
coulfact.h; it could not be a static inline there because of its mpz_t
temporary, I said so, and he left it. A reasoned refusal is fine; a
silent one is not.

---

# Part B: divrep

## B1. Rules and design principles not in pcoul-internals SKILL.md

[firm] The standard (CLAUDE.md): a pc?ul run, or a set of partial runs
combined, is meant to be a mathematical proof that every value in the
range it claims to have covered was checked. Any change that can affect
what a run reports, or what it claims to have covered, is held to that
standard.

Search and logs:

- [firm] pcoul logs whatever is needed to recover its state. Bias new
  state towards the log until there is a reason not to.
- [firm] No real work is kept out of the log (A5 item 13).
- [inferred] Every progress line is a usable recovery point (b0e17fc
  made t/t20log check this).
- [firm] Decisions made from costs should reproduce: identical runs make
  identical decisions, which makes bugs easier to see. This ranks below
  speed.
- [firm] Well over 90 percent of hv's compute is runs that try to prove
  an upper bound minimal, and he expects them to succeed. The common case
  is a full search that finds nothing. Optimize and calibrate for that,
  on the requested zmax (as under -X).
- [firm] Changing options across a recovery is not generally supported.
- [firm] Run with a range, `-x<min>:<max>`, not only a maximum.
- [firm] 10^43 is not a large number here.
- [firm] n = 2^x matters only as an extreme case; do not optimize for it
  alone. n = 2^x.p is far more common.
- [firm] The largest k with any known solution is about 23. pcoul may
  hard-limit k (MAXK is 66).

Direction:

- [firm] Enhance pcoul in preference to special programs. Two stages:
  first a proof by a combination of pcoul runs, then pcoul knowing enough
  to do it in one run and to know that the run is a proof.
- [firm] Calibration is headed into pcoul: per batch, then per decision.
  An external calibrator is an interim step. Cost data should be
  importable for a machine or MPUG version without writing new C.
- [firm] The global gain (-g) is a compromise. The hope is to replace it
  with the cost model at each gate once that is fast enough.

Tests:

- [firm] hv mostly runs `make dtest`. A new test file must be run by
  dtest and must honour DEBUG=1.
- [firm] test and dtest check, through pc[oar]ul, that primary
  functionality works and that fixed bugs stay fixed. They must be fast:
  they run all the time. (Each takes about 4 seconds here.)
- [firm] Soak tests are for when their area has knowingly changed. They
  live in t/ with higher numbers, test and dtest list every t/ file, and
  each soak test skips itself unless its variable is set (TEST_PELL,
  TEST_TAU), which also adds its program to the dependencies. Run as
  `TEST_TAU=1 make test`.
- [firm] Tests make temporary files properly; no hard-coded /tmp.
- [firm] The tests target the Makefile's current default MPUGMP_VER
  (39982f872b at present), not a fixed sha.
- [inferred] Two tests are expected failures marked TODO ("recover flip
  with trailing candidate", "recover midp with trailing candidate"). They
  record recovery gaps left when CHECK_OVERFLOW became the default. Leave
  them unless you are fixing the gap.

Code and files:

- [firm] A new file name shares at most a 0 or 1 character prefix, or
  else a complete syllable, with the other files. This protects tab
  completion for the coul* files. coulcost.c was accepted; cost.c and
  pricing.c were not.
- [firm] "pc?ul" is the standard short form for pcoul, pcaul and pcrul.
  A commit subject names the executables affected, which "is more
  important than which source file, since the latter is easily
  discovered in other ways."
- [firm] CHECK_OVERFLOW is a default build flag. Assume it is on.
- [firm] simple_fact() is for small numbers such as tau values.
- [firm] prime_iterator.c is a copy of upstream code. Fixes of general
  use are reported upstream (hv does this, to Dana Jacobsen) and upstream
  fixes are ported back. [inferred] Note any deliberate difference from
  upstream in the commit message.
- [firm] General fixes and pure optimizations go to master. calibrate is
  rebased over them.
- [firm] hv did not want calibration.md in the top directory, and wants
  skills files to hold durable knowledge and look forward. [inferred] A
  new document goes under .agents/skills or stays out of git.
- [firm] Only pcoul (TYPE_o) is distributed to outside users, as Windows
  builds. Unfactored -I entries are used only by a couple of them.
- [firm] `./inject -yo -n <n> <k> <value>` checks a value independently.
  -n means no database access. Its final 200 or 500 line means only that
  the value is or is not a solution for (n, k).

The calibrate branch has its own calibration.md at the top level. hv
intends it to become a skills file when the branch is rewritten.

---

# Part C: how changes are delivered

Delivery is now a draft PR from a job branch (see CLAUDE.md, Delivery).
The rules below date from format-patch delivery and still apply where
they fit.

Commits:

- [firm] Each commit achieves something that its message can explain
  clearly and, as far as can be told, works. Exceptions are rare.
- [firm] Concerns are separated. A bug found while updating tests is
  fixed in its own commit ahead of the test commit.
- [firm] There is no fixed order of idea and clean-ups: preparatory
  refactors first can be right. A5 item 20 is an example of a series
  that should lead with the idea.
- [firm] Before merge, history is rewritten so that the merged series is
  what is useful and follows the first rule above. Failed experiments,
  bugs found before merge and so on are removed as if they never
  happened. During review, corrections are fixup! commits (see
  CLAUDE.md, Delivery).
- [inferred] A style change is never mixed silently into a functional
  one: its own commit, or a note.
- [firm] If hv has pushed to the branch, his version wins: build on it,
  and never bring back your own version of something he edited. No
  rebasing.

Messages:

- [firm] Subject of 50 characters or fewer if possible, 72 at most. Body
  lines within 72.
- [firm] The subject starts with the executables affected: "pc?ul:",
  "pcoul:", "pcaul:". [inferred, code] Other prefixes in the log name an
  area (`coultau:`, `tests:`, `Makefile:`, `inject:`), and a tag may
  follow (`(bugfix)`, `(limits)`).
- [firm] The body is short. For a bug: what was wrong and what it
  affected. [inferred, code] hv's own messages say whether earlier
  results could be wrong ("As far as I can tell this bug could only cause
  unnecessary work, not wrong results") and which runs in his database
  are affected ("This affects previous runs for n=2p, 37 <= p <= 59").
- [inferred] Leave out how the fix was found, long lists of what was
  tested, and anything the diff already says. One line of measurement or
  of what was checked is fine.
- [firm] Attribution: hv cares little about it for himself ("it's not
  something I care terribly about"), but is happy to honour it for
  anyone, human or AI, who wants it. He often edits a commit without
  changing its author. Agent commits use author
  `Claude <noreply@anthropic.com>`, which records that; no trailers are
  needed. The Co-Authored-By and Claude-Session trailers on earlier
  commits were claude.ai's addition, not requested.

Before saying it works:

- [firm] Run the code. hv repeatedly asked for behaviour to be checked
  against real binaries, not argued from reading.
- [firm] `make dtest` (-O0 build) or `make test` (optimized), each of
  which covers all three programs. One of them is usually enough; dtest
  is the default. Add the soak test for the area changed (`TEST_TAU=1`,
  `TEST_PELL=1`).
- [firm] The other targets (ftest, sq12, test_pell, test_tau, speed)
  need checking only if their dependencies changed, and then only that
  they build: they have no tests of their own.
- [inferred] A regression test is shown to fail without the fix.
- [inferred] A refactor is shown to give identical output to the build
  before it, over several (n, k).
- [firm] valgrind or the address sanitizer is useful now and then, after
  a substantial change to memory handling; it found real overruns that
  review had missed. It is slow, so not routine.
- [inferred] A speed claim comes with numbers from a build without
  PORTABLE, in CPU time, on inputs of production size, with the command
  line.
- [inferred] A change that could alter results is checked against known
  values, and `inject -yo -n` is the independent check of a value.

Reporting:

- [firm] Say what was tested and what is only argued. A form of mine
  that was accepted: "This is a limit by construction, not a tested
  one: above 36 I only checked that `pcoul 840 40` and `pcoul 5040 66`
  start".
- [firm] Call a tidy-up a tidy-up, not a fix.
- [firm] Put a time limit on any investigation and ask before going down
  a side track. hv would rather be asked than have you go on alone on
  uncertain ground.
- [firm] Commit working stages as you go, so that a job ending on budget
  or timeout leaves usable commits. State what is unverified.
- [firm] Show the diff or the result itself, not a description of it.
- [firm] hv says "I am not always right, my ideas are not always good
  ideas." Disagree when you have evidence, and bring the evidence.
- [firm] If an instruction looks cut off in mid-sentence, stop and wait
  for the rest.

---

# Part D: never, in this repo

- [firm] Push to master, or merge your own work. hv reviews first.
- [firm] Do search work that the log does not show.
- [firm] Add files to a delivery that were not asked for, or a file
  whose name clashes under tab completion. [inferred] Add a document to
  the top directory.
- [firm] Use non-ASCII characters.
- [firm] Call something tested when it was only reasoned about.
- [firm] Slow the main tests, or make a soak test run by default.
- [firm] Deliver a git bundle.
- [firm] Break the Windows builds.
- [inferred] Change a test's expected output to make it pass, or remove
  a TODO, without having understood why it differs.
- [inferred] Replace or weaken a fail() so that a run carries on. A run
  that carries on wrongly can claim a range was searched when it was not,
  which breaks the proof standard (B1).
- [inferred] Change CC_OPT, the default DEFINES, the MPUGMP pin, tmfb[],
  or a factoring threshold, without asking.
- [inferred] Add a native-integer fast path without measurements at
  production size.
- [inferred] Add a cast, or widen a helper's argument, to quiet a
  compiler warning.
- [inferred] Add Python, shell scripts, or a new dependency.
- [firm] Set up or use a database: inject -n is the only allowed form.
  hv keeps sole responsibility for his real database.
- [firm] Work from anything but master, or touch the calibrate branch:
  it is being rebuilt elsewhere.
- [firm] Put the story of a fixed bug into a skills file.
