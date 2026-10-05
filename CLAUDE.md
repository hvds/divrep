# divrep: notes for claude-worker (github: hvds-worker)

This is the short version. Before writing code or commit messages, read
.agents/skills/divrep-conventions/SKILL.md; before changing the search
code, read .agents/skills/pcoul-internals/SKILL.md.

## The standard
A pc?ul run, or a set of partial runs combined, is meant to be a
mathematical proof: every value in the range it claims to have covered
was checked, so a reported solution is the least, and "none found"
means none exists there. Hold any change that can affect what a run
reports, or what it claims to have covered, to that standard. A run
that stops loudly costs time; a run that wrongly claims coverage is a
false result.

## Environment
- You run unattended in a container on hv's machine, on a branch
  worker/<id> made for this job. Nobody can answer questions mid-run.
- MPUGMP is set in the environment to a Math-Prime-Util-GMP checkout
  matching the Makefile's default MPUGMP_VER. Leave both alone.
- The machine is also running hv's long searches. Build only what you
  need, no parallel make, keep runs short.

## Build and test
    make dtest                  # normal check: fast -O0 build, DEBUG=1
    make test                   # optimised build: use when timing or
                                # optimised behaviour matters
    TEST_TAU=1 make dtest       # soak test: only if tau code changed
    TEST_PELL=1 make dtest      # soak test: only if Pell code changed
Expected: all ok apart from the 2 TODO tests ("recover flip with
trailing candidate", "recover midp with trailing candidate").
- If a change touches their dependencies, check that ftest, sq12,
  test_pell, test_tau and speed still build; they have no tests of
  their own.
- Check behaviour by running the binaries, not by arguing from the code.
- valgrind or the address sanitizer is worth running after a
  substantial change to memory handling, but not routinely: it is slow.
- Speed claims: build without PORTABLE, measure CPU time on inputs of
  production size, give the command line. The machine is loaded, so
  compare only runs made side by side.

## Delivery
- Commit on the current branch only. Never push, switch branches,
  rebase, reset or amend. The job runner pushes and opens a draft PR;
  hv reviews and merges.
- Work from master. Leave the calibrate branch alone: it is being
  rebuilt elsewhere.
- Each commit does one thing its message can explain, and works. A bug
  found on the way gets its own commit. Never slip a style change into
  a functional one.
- Commit each stage as soon as it works, so that a job which runs out
  of budget or time still leaves usable commits.
- In review, add commits only: a small correction to an earlier commit
  is a `git commit --fixup=<sha>`. Before merge hv rewrites the series
  so that it reads as if it was right first time. A big rework is a new
  job with a fresh series.
- If hv has pushed to this branch, his version wins: build on it, and
  never restore your own version of something he changed.
- No trailers are needed (Co-Authored-By and the like): the author
  field says who wrote the commit.

## Commit messages
- Subject 50 characters or fewer if possible, 72 at most; body lines
  within 72.
- Subject starts with the executables affected ("pc?ul:", "pcoul:"),
  otherwise the area ("coultau:", "tests:", "Makefile:").
- Body short. For a bug: what was wrong, what it affected (which runs,
  where that matters), and whether earlier results could be wrong. Not
  how it was found.
- A tidy-up is called a tidy-up, not a fix.

## Your final report
- What changed (commits), what was tested and how, what is only argued.
- Open questions. If you reach a decision hv should make, or a side
  track that would use much of the budget, stop and ask in the report.
- Ideas you set aside: list them as parked ideas. Do not add them to
  TODO-coul unasked.
- If the brief looks cut off mid-sentence, do nothing and say so.
- If you disagree with the brief and have evidence, say so and give it.

## Never
- Weaken or bypass fail() so that a run carries on. Change a test's
  expected output, or remove a TODO, without understanding why.
- Change CC_OPT, the default DEFINES, the MPUGMP pin, tmfb[] or a
  factoring threshold unasked.
- Add a native-integer fast path without measurements at production
  size. Add a cast, or widen a helper's argument, to quiet a warning.
- Add Python, shell scripts, dependencies, files not asked for, or
  documents in the top directory. Give a new file a name sharing more
  than a 1-character prefix (or a whole syllable) with an existing one.
- Use non-ASCII characters anywhere.
- Break the Windows builds (GitHub Actions). Slow the main tests
  noticeably: a new main test should add little to the run time; slow
  tests are soak tests, which never run by default.
- Do search work that the log does not show.
- Set up or use a database. There is none here; inject -n is the only
  allowed form.
- Call something tested that was only reasoned about.
