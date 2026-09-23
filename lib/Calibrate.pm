package Calibrate;

# Runs individual pcoul batches with given settings and parses the
# resulting log file. Named generically (not "Pcoul...") since this
# may grow to cover other divrep targets (pcaul, pcrul) later.

use strict;
use warnings;
use File::Temp qw(tempfile);
use Carp qw(croak);

# ---------------------------------------------------------------------
# Log line codes, confirmed against two sample logs (one timing out,
# one completing with a solution):
#   001  header, restates the invocation
#   202  "Candidate <v> (Es)" - a running best-so-far, not final
#   305  per-batch progress line (see parse_progress_line)
#   301  "Timeout after Es" - cutoff reached, run aborted, no 367/200
#   367  final true totals for the run: recurse/walk/walkc counts and
#        elapsed time. This is the real cost metric. Printed once, at
#        the end, only on normal completion (not on timeout).
#   200  "f(n, k) = <v> (Es)" - only printed if a solution was found;
#        absent means the batch was exhausted with no solution.
#
# The per-position bracketed numbers on 305 lines (one per k-position)
# are factorization-progress diagnostics, not relevant to calibration,
# and are parsed but otherwise ignored here.
#
# Parsing convention: each parse_*_line() sub first checks cheaply
# whether the line carries the code it handles; if not, it returns
# undef so callers can try the next parser in a dispatch loop. If the
# code matches but the rest of the line doesn't fit the expected
# shape, it croaks with the offending line rather than returning
# undef - a line with a known code that fails to parse is a real
# surprise (a pcoul format change, a new sub-case we haven't seen,
# a truncated write) and should stop us loudly rather than be
# silently treated as "not this kind of line".
# ---------------------------------------------------------------------

use constant {
    CODE_HEADER    => '001',
    CODE_BATCHLIST => '203',
    CODE_PROGRESS  => '305',
    CODE_TIMEOUT   => '301',
    CODE_FINAL     => '367',
    CODE_SOLUTION  => '200',
    CODE_CANDIDATE => '202',
};

# ---------------------------------------------------------------------
# Gain encoding: pcoul's "-g<a>:<b>" sets gain = b/a. The optional
# second gain, -G<a>:<b>, overrides -g specifically for known-square
# sub-cases encountered during recursion - it is meaningless (and
# unnecessary) for a batch that is entirely square throughout, since
# then plain -g already applies to everything. gain_opt() takes a
# target gain as a rational p/q (both positive integers, q defaults
# to 1) and an optional flag letter, and returns the correct option
# string.
# ---------------------------------------------------------------------

sub gain_opt {
    my($p, $q, $flag) = @_;
    $q //= 1;
    $flag //= 'g';
    croak "gain_opt: p and q must be positive integers" unless $p > 0 && $q > 0;
    return $q == 1 ? "-$flag$p" : "-$flag$q:$p";
}

# ---------------------------------------------------------------------
# Build the command line for a single-batch run.
#
# %opt keys:
#   pcoul     => path to pcoul binary (default './pcoul')
#   n, k      => required
#   batch     => required, batch index (passed as -b)
#   force_all => -f value
#   strategy  => -j value
#   gain_p, gain_q     => primary gain rational (gain_q defaults 1)
#   gain2_p, gain2_q   => optional -G rational, overriding -g for
#                         known-square sub-cases hit during recursion.
#                         Only meaningful for batches that are NOT
#                         wholly square (see parse_batch_line) - for a
#                         wholly-square batch, omit this and just set
#                         gain_p/gain_q to the desired value.
#   xmax      => -x value (v_max); xmin optional
#   modulus   => optional arrayref of "modulus=residue" strings for -m
#   log_freq  => seconds between logfile progress updates (-Lf)
#   deadline  => seconds before cutoff (-Ld)
#   screen_freq => seconds between on-screen progress updates (-Ls);
#                  defaults to 0 (disabled) since the harness only
#                  ever parses the logfile - pass a positive value
#                  explicitly if you want to watch a run interactively
#   logfile   => path to write the log to (required; we parse this)
# ---------------------------------------------------------------------

sub build_cmd {
    my(%opt) = @_;
    for my $req (qw(n k batch xmax logfile)) {
        croak "build_cmd: missing required option '$req'"
            unless defined $opt{$req};
    }

    my $pcoul = $opt{pcoul} // './pcoul';
    my @cmd = ($pcoul);

    push @cmd, "-r$opt{logfile}";
    push @cmd, '-R';  # never resume - each calibration run starts fresh
    push @cmd, "-b$opt{batch}";

    if (defined $opt{force_all}) {
        push @cmd, "-f$opt{force_all}";
    }
    if (defined $opt{strategy}) {
        push @cmd, "-j$opt{strategy}";
    }
    if (defined $opt{gain_p}) {
        push @cmd, gain_opt($opt{gain_p}, $opt{gain_q});
    }
    if (defined $opt{gain2_p}) {
        push @cmd, gain_opt($opt{gain2_p}, $opt{gain2_q}, 'G');
    }

    my $xspec = defined $opt{xmin} ? "$opt{xmin}:$opt{xmax}" : "$opt{xmax}";
    push @cmd, "-x$xspec";

    if ($opt{modulus}) {
        push @cmd, "-m$_" for @{ $opt{modulus} };
    }

    if (defined $opt{log_freq}) {
        push @cmd, "-Lf$opt{log_freq}";
    }
    if (defined $opt{deadline}) {
        push @cmd, "-Ld$opt{deadline}";
    }
    push @cmd, '-Ls' . ($opt{screen_freq} // 0);

    push @cmd, $opt{n}, $opt{k};
    return @cmd;
}

# ---------------------------------------------------------------------
# Build the command line for a batch-listing run (-a): enumerates the
# batches that a given (n, k, f[, modulus]) would generate, at
# essentially zero cost - no -b, no -g/-j/-x needed since no search is
# performed, no -Ld needed since this always finishes almost instantly
# (confirmed: the trailing 367 line's own recurse/walk/walkc counts
# are tiny and reflect batch generation, not any real search - they
# are not a cost figure and should not be treated as one).
#
# %opt keys: pcoul, n, k, force_all, xmax, modulus, logfile (required
# except pcoul/modulus, as in build_cmd).
# ---------------------------------------------------------------------

sub build_list_cmd {
    my(%opt) = @_;
    for my $req (qw(n k xmax logfile)) {
        croak "build_list_cmd: missing required option '$req'"
            unless defined $opt{$req};
    }

    my $pcoul = $opt{pcoul} // './pcoul';
    my @cmd = ($pcoul);

    push @cmd, "-r$opt{logfile}";
    push @cmd, '-R';
    push @cmd, '-a';

    if (defined $opt{force_all}) {
        push @cmd, "-f$opt{force_all}";
    }

    my $xspec = defined $opt{xmin} ? "$opt{xmin}:$opt{xmax}" : "$opt{xmax}";
    push @cmd, "-x$xspec";

    if ($opt{modulus}) {
        push @cmd, "-m$_" for @{ $opt{modulus} };
    }
    push @cmd, '-Ls0';

    push @cmd, $opt{n}, $opt{k};
    return @cmd;
}

# ---------------------------------------------------------------------
# Parse a single batch-listing line (code 203) from an -a run. The
# trailing "[sq=1]" tag marks a batch whose unallocated part is known
# to always be square. -G overrides -g specifically for known-square
# sub-cases encountered during recursion; when a batch is *entirely*
# square from the start (tagged [sq=1] here), there is no non-square
# sub-case for -G to override anything against, so -g alone (set to
# whatever value would otherwise go to -G) is sufficient - no separate
# -G search is needed for these batches. -G only matters for batches
# NOT tagged [sq=1] here, where some deeper recursion path may still
# turn up a square sub-case partway through an otherwise non-square
# batch - those are the batches whose -G (if any) needs calibrating
# separately from -g.
#
# Format (from sample):
#   203 b18: 2^3 3^2 2.5^2 . 2^2.3 . 2 [sq=1]
#   203 b0: 2^5 3^2 2.5^2 . 2^2.3 . 2
# Also seen in practice: a real pcoul build may emit a trailing
# elapsed-time stamp on 203 lines too (as -dB's live-processing
# variant does), even for a pure -a listing pass, e.g.:
#   203 b0: 2^2 5 2.3^2 . 2^3 3 2.5^2 [sq=1] (0.00s)
# so both the pattern and the square-flag check below must tolerate
# an optional trailing "(N.NNs)" rather than assuming end-of-line
# comes right after the pattern or the [sq=1] tag.
# ---------------------------------------------------------------------

my $BATCHLIST_RE = qr{
    ^ 203 \s+
    b(\d+) : \s+
    (.+?)
    (?: \s+ \[ sq = 1 \] )?
    (?: \s+ \( [\d.]+ s \) )?
    \s* $
}x;

sub parse_batch_line {
    my($line) = @_;
    return undef unless $line =~ /^203\b/;
    $line =~ $BATCHLIST_RE
        or croak "Calibrate: malformed code-203 batch-list line: $line";
    my($batch, $pattern) = ($1, $2);  # save before next match clobbers them
    my $square = ($line =~ /\[sq=1\]/) ? 1 : 0;
    return { batch => $batch, pattern => $pattern, square => $square };
}

# ---------------------------------------------------------------------
# Parse a whole -a (batch-listing) log file. Returns:
#   { batches => [ { batch, pattern, square }, ... ],  # in file order
#     n_square => count of batches with square => 1 }
#
# 'square' batches (see parse_batch_line above) never need a -G
# search - only plain -g. The complement (square => 0) are the
# batches whose -G, if it matters at all for them, needs its own
# calibration pass separate from -g.
#
# The trailing 367 line present in -a output is deliberately ignored
# here (its counts reflect batch generation, not search cost - see
# build_list_cmd). Any other unrecognised line croaks, per the usual
# convention, since a batch-list run should contain only 001/203/367.
# ---------------------------------------------------------------------

sub parse_batch_list {
    my($path) = @_;
    open my $fh, '<', $path or croak "cannot open $path: $!";
    my @lines = <$fh>;
    close $fh;
    chomp @lines;

    my @batches;
    for my $line (@lines) {
        next if $line =~ /^001\b/;
        next if $line =~ /^367\b/;
        if (my $b = parse_batch_line($line)) {
            push @batches, $b;
            next;
        }
        croak "Calibrate: unrecognised line in batch-list log: $line";
    }

    my $n_square = grep { $_->{square} } @batches;
    return { batches => \@batches, n_square => $n_square };
}

# ---------------------------------------------------------------------
# Run an -a batch-listing pass for a given (n, k, f[, modulus, xmax])
# and return the same structure as parse_batch_list().
# ---------------------------------------------------------------------

sub list_batches {
    my(%opt) = @_;

    my $logfile = $opt{logfile};
    my $tmp_fh;
    unless (defined $logfile) {
        ($tmp_fh, $logfile) = tempfile(
            'pcoul-calib-list-XXXXXX', TMPDIR => 1, SUFFIX => '.log',
        );
        close $tmp_fh;
        unlink $logfile;
    }

    my @cmd = build_list_cmd(%opt, logfile => $logfile);
    my $rc = system(@cmd);
    croak "failed to execute pcoul: $!" if $rc == -1;

    my $result = parse_batch_list($logfile);
    $result->{cmd} = \@cmd;
    $result->{logfile} = $logfile;

    unlink $logfile unless $opt{keep_logfile};

    return $result;
}

# ---------------------------------------------------------------------
# Parse a single progress line (code 305). Returns undef if the line
# is not a 305 line at all; croaks if it is a 305 line but doesn't fit
# the expected shape. The bracketed numbers are per-k-position
# factorization-progress diagnostics (confirmed not relevant to
# calibration) - captured as 'position_diag' only in case they're
# useful for troubleshooting, never used in cost decisions.
#
# Format (from samples):
#   305 b5: 3^2.5^2.17^2 2^2.11^2.51437^2 . (1.00s) [18083 1237 1692]
#   305 b69: 2 3.59^2 2^5 5^2 2.3^2 . 2^2: 3665 / 4511 (8.00s) [...]
# ---------------------------------------------------------------------

my $PROGRESS_RE = qr{
    ^ 305 \s+
    b(\d+) : \s+
    (.+?)                              # allocation pattern
    (?: : \s* (\d+) \s* / \s* (\d+) )? # optional walk progress "W / M"
    \s+ \( ([\d.]+) s \) \s+
    \[ ([\d\s]+) \]
    \s* $
}x;

sub parse_progress_line {
    my($line) = @_;
    return undef unless $line =~ /^305\b/;
    $line =~ $PROGRESS_RE
        or croak "Calibrate: malformed code-305 progress line: $line";
    return {
        batch          => $1,
        pattern        => $2,
        walk_progress  => (defined $3 ? [$3, $4] : undef),
        elapsed        => $5 + 0,
        position_diag  => [ split ' ', $6 ],
    };
}

# ---------------------------------------------------------------------
# Parse the final-totals line (code 367), the true cost metric for a
# completed (non-timed-out) run:
#   367 coul(12, 7): recurse 30248375, walk 30307489, walkc 17849958
#       (35.33s) [...]
# ---------------------------------------------------------------------

my $FINAL_RE = qr{
    ^ 367 \s+ coul\( (\d+) , \s* (\d+) \) : \s+
    recurse \s+ (\d+) , \s+
    walk \s+ (\d+) , \s+
    walkc \s+ (\d+) \s+
    \( ([\d.]+) s \)
}x;

sub parse_final_line {
    my($line) = @_;
    return undef unless $line =~ /^367\b/;
    $line =~ $FINAL_RE
        or croak "Calibrate: malformed code-367 final line: $line";
    return {
        n => $1, k => $2,
        recurse => $3, walk => $4, walkc => $5,
        elapsed => $6 + 0,
    };
}

# ---------------------------------------------------------------------
# Parse the solution line (code 200), only present if a solution was
# found:  200 f(12, 7) = 155385466971 (35.33s)
# ---------------------------------------------------------------------

my $SOLUTION_RE = qr{
    ^ 200 \s+ f\( (\d+) , \s* (\d+) \) \s* = \s* (\d+) \s+ \( ([\d.]+) s \)
}x;

sub parse_solution_line {
    my($line) = @_;
    return undef unless $line =~ /^200\b/;
    $line =~ $SOLUTION_RE
        or croak "Calibrate: malformed code-200 solution line: $line";
    return { n => $1, k => $2, v => $3, elapsed => $4 + 0 };
}

# ---------------------------------------------------------------------
# Parse a running-candidate line (code 202), informational only - the
# true answer, if any, is the last 200 line, not this.
#   202 Candidate 464249221876448 (0.01s)
# ---------------------------------------------------------------------

my $CANDIDATE_RE = qr{ ^ 202 \s+ Candidate \s+ (\d+) \s+ \( ([\d.]+) s \) }x;

sub parse_candidate_line {
    my($line) = @_;
    return undef unless $line =~ /^202\b/;
    $line =~ $CANDIDATE_RE
        or croak "Calibrate: malformed code-202 candidate line: $line";
    return { v => $1, elapsed => $2 + 0 };
}

# ---------------------------------------------------------------------
# Parse the timeout line (code 301): "301 Timeout after 10.99s"
# ---------------------------------------------------------------------

my $TIMEOUT_RE = qr{ ^ 301 \s+ Timeout \s+ after \s+ ([\d.]+) s }x;

sub parse_timeout_line {
    my($line) = @_;
    return undef unless $line =~ /^301\b/;
    $line =~ $TIMEOUT_RE
        or croak "Calibrate: malformed code-301 timeout line: $line";
    return { elapsed => $1 + 0 };
}

# ---------------------------------------------------------------------
# Parse a whole log file, returning a summary of the run:
#
#   { status   => 'timeout' | 'exhausted' | 'solution' | 'incomplete',
#     elapsed  => elapsed seconds at the terminal line (the cost figure
#                 to use: exact for 'exhausted'/'solution', a lower
#                 bound (== the deadline) for 'timeout'),
#     final    => parsed 367 line, or undef (undef on timeout),
#     solution => parsed 200 line, or undef (undef unless found),
#     candidates => arrayref of all parsed 202 lines, best-so-far trail,
#     raw_tail => last few raw lines, for diagnostics }
#
# 'incomplete' means the log ended without a recognised terminal line
# (no 301, no 367) - treat as untrustworthy: almost certainly the
# process was killed some other way, or log_freq/deadline weren't
# passed correctly, rather than a real pcoul outcome. Any known-code
# line that fails to parse will croak rather than silently falling
# through to 'incomplete', so a genuine 'incomplete' here really does
# mean "no terminal line was seen at all".
# ---------------------------------------------------------------------

sub parse_log_file {
    my($path) = @_;
    open my $fh, '<', $path or croak "cannot open $path: $!";
    my @lines = <$fh>;
    close $fh;
    chomp @lines;

    my($final, $solution, $timeout_elapsed);
    my @candidates;

    for my $line (@lines) {
        if (my $c = parse_candidate_line($line)) {
            push @candidates, $c;
            next;
        }
        if (my $f = parse_final_line($line)) {
            $final = $f;
            next;
        }
        if (my $s = parse_solution_line($line)) {
            $solution = $s;
            next;
        }
        if (my $t = parse_timeout_line($line)) {
            $timeout_elapsed = $t->{elapsed};
            next;
        }
        # 001 header and 305 progress lines are intentionally not
        # inspected further here; parse_progress_line() is available
        # separately for diagnostics if needed.
    }

    my $status
        = defined $timeout_elapsed ? 'timeout'
        : $solution                ? 'solution'
        : $final                   ? 'exhausted'
        :                             'incomplete';

    my $elapsed
        = $status eq 'timeout'  ? $timeout_elapsed
        : $status eq 'solution' ? $solution->{elapsed}
        : $status eq 'exhausted'? $final->{elapsed}
        :                          undef;

    return {
        status     => $status,
        elapsed    => $elapsed,
        final      => $final,
        solution   => $solution,
        candidates => \@candidates,
        raw_tail   => [ @lines[ -3 < -@lines ? 0 : -3 .. -1 ] ],
    };
}

# ---------------------------------------------------------------------
# Run one batch with the given settings and a hard deadline, returning
# the parsed summary. Uses a private temp logfile unless one is given.
# ---------------------------------------------------------------------

sub run_batch {
    my(%opt) = @_;

    my $logfile = $opt{logfile};
    my $tmp_fh;
    unless (defined $logfile) {
        ($tmp_fh, $logfile) = tempfile(
            'pcoul-calib-XXXXXX', TMPDIR => 1, SUFFIX => '.log',
        );
        close $tmp_fh;
        unlink $logfile;  # pcoul must create it fresh with -R
    }

    my @cmd = build_cmd(%opt, logfile => $logfile);

    # system(LIST) form avoids the shell entirely.
    my $rc = system(@cmd);
    if ($rc == -1) {
        croak "failed to execute pcoul: $!";
    }

    my $summary = parse_log_file($logfile);
    $summary->{cmd} = \@cmd;
    $summary->{logfile} = $logfile;

    unlink $logfile unless $opt{keep_logfile};

    return $summary;
}

# ---------------------------------------------------------------------
# Run many batches concurrently, up to $max_jobs children at a time,
# via a simple fork/waitpid worker pool - no CPAN dependency.
#
# $jobs is an arrayref of %opt hashes as accepted by run_batch(); each
# gets its own private logfile (unless it specifies one) which is
# parsed and removed exactly as run_batch() would do. Returns a list
# of summaries in the *same order* as @$jobs (not completion order).
#
# A child that fails to exec reports that failure back as a summary
# with status 'exec_failed' rather than silently vanishing, so a
# caller iterating over results doesn't mistake "pcoul not found" for
# "pcoul ran and produced an empty/incomplete log".
# ---------------------------------------------------------------------

sub run_batches_parallel {
    my($jobs, $max_jobs) = @_;
    $max_jobs = 1 unless $max_jobs && $max_jobs > 0;

    my @results;
    $#results = $#$jobs;  # preallocate, same length/order as @$jobs

    my %pid_to_idx;
    my $next    = 0;
    my $running = 0;

    my $launch = sub {
        my($idx) = @_;
        my %opt = %{ $jobs->[$idx] };

        my $logfile = $opt{logfile};
        unless (defined $logfile) {
            my(undef, $lf) = tempfile(
                'pcoul-calib-par-XXXXXX', TMPDIR => 1, SUFFIX => '.log',
            );
            unlink $lf;
            $logfile = $lf;
        }
        # remember for the parent to parse later
        $jobs->[$idx]{_logfile} = $logfile;

        my @cmd = build_cmd(%opt, logfile => $logfile);

        my $pid = fork();
        croak "fork failed: $!" unless defined $pid;

        if ($pid == 0) {
            # Child: exec pcoul directly, never returns on success.
            exec { $cmd[0] } @cmd
                or do {
                    # exec failed (e.g. binary not found) - report via a
                    # sentinel exit code the parent recognises, rather
                    # than falling through into shared parent state.
                    require POSIX;
                    POSIX::_exit(127);
                };
        }

        $pid_to_idx{$pid} = $idx;
        $running++;
    };

    while ($next < @$jobs || $running > 0) {
        while ($running < $max_jobs && $next < @$jobs) {
            $launch->($next);
            $next++;
        }

        my $pid = waitpid(-1, 0);
        # no children left to reap - shouldn't happen given the loop
        # guard above
        last if $pid <= 0;
        my $status = $?;

        next unless exists $pid_to_idx{$pid};
        my $idx = delete $pid_to_idx{$pid};
        $running--;

        my $logfile   = $jobs->[$idx]{_logfile};
        my $keep_log  = $jobs->[$idx]{keep_logfile};

        if (($status >> 8) == 127) {
            $results[$idx] = { status => 'exec_failed', logfile => $logfile };
        } else {
            my $summary = parse_log_file($logfile);
            $summary->{logfile} = $logfile;
            $results[$idx] = $summary;
        }

        unlink $logfile unless $keep_log;
    }

    return @results;
}

1;

__END__

=head1 NAME

Calibrate - run individual pcoul (and, eventually, sibling target)
batches for calibration purposes

=head1 STATUS

Log format confirmed against two real sample logs (one timing out, one
completing with a solution): codes 001/202/305/301/367/200 are all
handled. -Ls/-Lf/-Ld semantics confirmed; -Ls defaults to 0 (disabled)
since only the logfile is ever parsed. Known-code lines that fail to
parse now croak with the offending line rather than being silently
treated as a non-match. Not yet exercised against a real pcoul binary
- next step is a smoke test against the actual executable to confirm
build_cmd() produces a command line pcoul accepts as intended,
particularly -b, -Lf/-Ld/-Ls, and -G.

=cut
