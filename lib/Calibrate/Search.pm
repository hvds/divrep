package Calibrate::Search;

# Orchestration layer on top of Calibrate.pm: turns "run one batch and
# parse its log" into "find a good (j, f, g) for this (n, k, v_max)".
#
# Cost model: wall time from Calibrate's parsed summaries. A batch run
# under a given -Ld deadline is either 'resolved' (it finished - the
# elapsed time in the summary is the TRUE cost, and will never change
# no matter how large a deadline we ask for in future, since pcoul's
# search is deterministic) or 'timeout' (a censored observation - the
# true cost is only known to be >= the deadline used). This lets us
# cache aggressively: a resolved batch is done forever; a timed-out
# batch only needs rerunning if we later want to try a strictly larger
# deadline than any we've already tried on it.
#
# If any batch, at any point, reports status 'solution', that means a
# real solution v <= v_max was found. Per the agreed policy this is
# unconditionally good news and stops calibration outright rather than
# folding it into the cost comparison - see $Calibrate::Search::ABORT.

use strict;
use warnings;
use Carp qw(croak);
use Fcntl qw(O_WRONLY O_APPEND O_CREAT);
use POSIX qw(floor);
use List::Util qw(min max);

use Calibrate;

# Set to a hashref describing the solution as soon as one is seen by
# any evaluation, anywhere. Callers (the calibrate.pl driver) should
# check this after every call into this module and stop immediately
# if it's set - we don't stop internally because the caller may want
# to log/report the state of the search so far first.
our $ABORT;

# ---------------------------------------------------------------------
# Exact-rational helpers. A "rational" is always a 2-element arrayref
# [p, q] meaning p/q, both positive integers. We work in exact
# integers throughout the mediant search - floats only ever appear
# when picking where to *probe* during the coarse scan, never as the
# gain value actually sent to pcoul.
# ---------------------------------------------------------------------

sub _gcd {
    my($a, $b) = @_;
    ($a, $b) = ($b, $a % $b) while $b;
    return $a || 1;
}

sub rat_reduce {
    my($r) = @_;
    my $g = _gcd($r->[0], $r->[1]);
    return [ $r->[0] / $g, $r->[1] / $g ];
}

sub rat_float { return $_[0][0] / $_[0][1] }

sub rat_str   { return "$_[0][0]/$_[0][1]" }

sub rat_eq {
    my($a, $b) = @_;
    return $a->[0] * $b->[1] == $b->[0] * $a->[1];
}

sub mediant {
    my($a, $b) = @_;
    return [ $a->[0] + $b->[0], $a->[1] + $b->[1] ];
}

# Best rational approximation to a positive float, with denominator
# capped at $max_den, via continued fractions.
sub float_to_rational {
    my($x, $max_den) = @_;
    $max_den //= 1000;
    croak "float_to_rational: x must be positive" unless $x > 0;

    my($h1, $h2, $k1, $k2) = (1, 0, 0, 1);
    my $b = $x;
    my($num, $den) = (floor($x + 0.5), 1);
    $num = 1 if $num < 1;

    for (1 .. 40) {
        my $a  = floor($b);
        my $hh = $a * $h1 + $h2;
        my $kk = $a * $k1 + $k2;
        last if $kk > $max_den || $kk <= 0;
        ($num, $den) = ($hh, $kk);
        ($h2, $h1) = ($h1, $hh);
        ($k2, $k1) = ($k1, $kk);
        my $frac = $b - $a;
        last if $frac < 1e-9;
        $b = 1 / $frac;
    }
    $num = 1 if $num < 1;
    return [ $num, $den ];
}

# ---------------------------------------------------------------------
# Result cache: key is "n:k:f:batch:j:gp:gq[:Gp:Gq]" (the [:Gp:Gq]
# suffix only present when a second gain is in play). Value is either
#   { status => 'resolved', elapsed => E }
# or
#   { status => 'timeout', best_timeout_tried => D }
# A fresh cache is created per Calibrate::Search process; pass
# cache_file to persist across runs (appended to as we go, loaded
# up front if it already exists).
# ---------------------------------------------------------------------

my %CACHE;
my $CACHE_FH;

sub _cache_key {
    my(%o) = @_;
    my @parts = @o{qw(n k f batch j gp gq)};
    push @parts, $o{Gp}, $o{Gq} if defined $o{Gp};
    return join(':', @parts);
}

sub load_cache {
    my($path) = @_;
    return unless -e $path;
    open my $fh, '<', $path or croak "cannot open cache $path: $!";
    while (my $line = <$fh>) {
        chomp $line;
        next unless length $line;
        my($key, $status, $a, $b) = split /\t/, $line;
        if ($status eq 'resolved') {
            $CACHE{$key} = { status => 'resolved', elapsed => $a + 0 };
        } elsif ($status eq 'timeout') {
            $CACHE{$key} = {
                status => 'timeout', best_timeout_tried => $a + 0,
            };
        }
        # unrecognised status: ignore the line rather than croak - a
        # cache file is disposable, not a correctness-critical input.
    }
    close $fh;
}

sub open_cache_for_append {
    my($path) = @_;
    # sysopen + syswrite rather than open()/print()/autoflush: this
    # bypasses Perl's buffered PerlIO layer entirely, so every write is
    # a single unbuffered write(2) syscall with O_APPEND's atomic
    # seek-to-end-and-write semantics. Cache writes happen from a
    # process that's also forking heavily (run_batches_parallel); a
    # buffered handle proved unreliable under that load in testing
    # here (writes went missing with no error and no fd corruption
    # visible via fileno()), whereas syswrite is immune to whatever
    # buffering-layer interaction caused that.
    sysopen($CACHE_FH, $path, O_WRONLY | O_APPEND | O_CREAT, 0644)
        or croak "cannot open cache $path for append: $!";
}

sub _cache_put {
    my($key, $entry) = @_;
    $CACHE{$key} = $entry;
    return unless $CACHE_FH;
    my $line
        = $entry->{status} eq 'resolved'
        ? join("\t", $key, 'resolved', $entry->{elapsed}) . "\n"
        : join("\t", $key, 'timeout', $entry->{best_timeout_tried}) . "\n";
    my $n = syswrite($CACHE_FH, $line);
    croak "cache write failed: $!" unless defined $n && $n == length $line;
}

# ---------------------------------------------------------------------
# Batch-shape classification: two batches with the same allocation
# *shape* tend to take about the same time for given settings, where
# "shape" here means the actual primes and exponents assigned, without
# regard to *which* of the k positions each one landed in - the k
# positions are structurally interchangeable slots in the arithmetic
# progression, so a batch and the same batch with two of its position
# assignments swapped cost the same. The primes themselves are NOT
# discarded (unlike exponent-only shape): batch_shape() canonicalises
# each position's factor list (sorted "prime^exp" tokens) and then
# sorts the k per-position strings against each other, collapsing only
# permutations of which position got which allocation - never
# collapsing two batches that differ in which actual primes they fix.
# ---------------------------------------------------------------------

sub batch_shape {
    my($pattern) = @_;
    my @positions = split ' ', $pattern;
    my @shapes;
    for my $pos (@positions) {
        if ($pos eq '.') { push @shapes, ''; next; }
        my @factors = split /\./, $pos;
        my @norm;
        for my $factor (@factors) {
            my($base, $exp) = split /\^/, $factor;
            push @norm, defined $exp ? "$base^$exp" : "$base^1";
        }
        push @shapes, join('.', sort @norm);
    }
    # Which of the k positions gets which allocation doesn't change the
    # search cost - the positions are structurally interchangeable
    # slots - so sort the per-position strings too, collapsing shapes
    # that only differ by a permutation of which position got which
    # allocation. The primes/exponents themselves are preserved as-is.
    return join('|', sort @shapes);
}

sub classify_batches {
    my($batches) = @_;
    my %groups;
    for my $b (@$batches) {
        my $key = batch_shape($b->{pattern}) . ';sq=' . ($b->{square} ? 1 : 0);
        push @{ $groups{$key} }, $b;
    }
    return \%groups;
}

# Pick $per_group representative batches from each shape group (default
# 1), each carrying a 'weight' equal to the number of real batches it
# stands in for (split evenly if per_group > 1, remainder absorbed by
# the first representative so weights always sum exactly to the group
# size). Batches without a 'pattern' field (e.g. hand-constructed for
# tests) are treated as their own singleton group, keyed by batch id,
# so this degrades gracefully to "one representative per real batch"
# rather than crashing or mis-grouping unrelated data.
sub representative_batches {
    my($batches, %opt) = @_;
    my $per_group = $opt{per_group} // 1;

    my %groups;
    for my $b (@$batches) {
        my $key = defined $b->{pattern}
            ? (batch_shape($b->{pattern}) . ';sq=' . ($b->{square} ? 1 : 0))
            : "singleton:$b->{batch}";
        push @{ $groups{$key} }, $b;
    }

    my @reps;
    for my $key (sort keys %groups) {
        my @members = @{ $groups{$key} };
        my $take = min($per_group, scalar @members);
        for my $i (0 .. $take - 1) {
            my $b = $members[$i];
            my $w = ($i == $take - 1) ? (@members - $i) : 1;
            push @reps, { %$b, weight => $w };
        }
    }
    return \@reps;
}

# ---------------------------------------------------------------------
# Restrictiveness score, derived from the validated (against real
# -dB logs) result that a completed allocation's walk size M scales
# EXACTLY as M_new = M_old * (p_old/p_new)^e when a single fixed
# prime power is swapped for another at the same exponent e - which
# means M is, up to a batch-independent constant, exactly proportional
# to 1/LCM(fixed prime powers). Lower LCM (smaller restrictiveness
# score here, since we return log(LCM)) means a larger residual walk
# range, i.e. a slower batch. This costs nothing to compute - it only
# needs the pattern string from an -a listing, no pcoul run at all.
#
# Returns log(LCM) so scores are comparable via simple subtraction/
# addition rather than needing bignum arithmetic for batches with
# large prime powers.
# ---------------------------------------------------------------------

sub restrictiveness_score {
    my($pattern) = @_;
    my %max_exp_for_prime;
    for my $pos (split ' ', $pattern) {
        next if $pos eq '.';
        for my $factor (split /\./, $pos) {
            my($base, $exp) = split /\^/, $factor;
            $exp = defined $exp ? $exp + 0 : 1;
            my $cur = $max_exp_for_prime{$base};
            $max_exp_for_prime{$base} = $exp
                if !defined($cur) || $exp > $cur;
        }
    }
    my $loglcm = 0;
    $loglcm += $max_exp_for_prime{$_} * log($_) for keys %max_exp_for_prime;
    return $loglcm;
}

# ---------------------------------------------------------------------
# Select the batches to actually spend (j, g) search effort on: dedup
# by shape first (see representative_batches), then keep only the
# top fraction by predicted restrictiveness (lowest LCM = predicted
# slowest = highest priority), since these are the batches that
# dominate total run time and are therefore the ones worth
# discriminating between candidate settings on. The remaining batches
# still get included in the final full-batch confirmation run - this
# only shrinks the SEARCH phase, not the confirmation.
#
# %opt: per_group (passed through to representative_batches, default
# 1), top_frac (fraction of shape-groups to keep by priority, default
# 0.10), min_n (floor on how many to keep regardless of top_frac,
# default 10, so small batch sets still get reasonable coverage).
# ---------------------------------------------------------------------

sub priority_batches {
    my($batches, %opt) = @_;
    my $top_frac = $opt{top_frac} // 0.10;
    my $min_n    = $opt{min_n} // 10;

    my $reps = representative_batches(
        $batches, per_group => $opt{per_group} // 1,
    );
    for my $r (@$reps) {
        $r->{restrictiveness} = defined $r->{pattern}
            ? restrictiveness_score($r->{pattern}) : 0;
    }

    # ascending restrictiveness (smallest LCM first) = predicted
    # slowest first
    my @sorted =
        sort { $a->{restrictiveness} <=> $b->{restrictiveness} } @$reps;

    my $n_take = max($min_n, int(@sorted * $top_frac));
    $n_take = min($n_take, scalar @sorted);

    return [ @sorted[0 .. $n_take - 1] ];
}

# ---------------------------------------------------------------------
# Extrapolate a full-batch-set total from only the priority_batches()
# subset that search_gain() actually raced, rather than reporting that
# subset's raw sum as if it were the whole run (which under-reports,
# since priority_batches deliberately excludes the less-restrictive -
# predicted faster, but still real - batches).
#
# Uses the validated M ~ 1/LCM(fixed prime powers) scaling law:
# restrictiveness_score() (log LCM) correlates strongly (rho -0.85 to
# -0.98 in real data) with log(elapsed), so a simple least-squares fit
# of ln(elapsed) against restrictiveness over the batches we actually
# measured lets us predict the unmeasured ones without running them.
#
# %opt: n, k, f, j, gp, gq, [Gp, Gq,] all_batches (full list from
# Calibrate::list_batches), searched (the priority_batches()-selected
# reps that were actually raced for this (f, j, g)).
#
# Returns { total, fitted, n_fit }. fitted is false (and total falls
# back to scaling the searched batches' own average per-batch rate
# across the rest, cruder but still better than the unscaled subset
# sum) whenever there are fewer than 2 distinct restrictiveness values
# among the resolved searched batches - a line can't be fit through
# fewer than 2 distinct x-values - or when every batch was already
# searched (small batch sets, or search_top_frac=1).
# ---------------------------------------------------------------------

sub estimate_full_total {
    my(%opt) = @_;
    my $all      = $opt{all_batches} // [];
    my $searched = $opt{searched}    // [];
    my($n, $k, $f, $j, $gp, $gq, $Gp, $Gq)
        = @opt{qw(n k f j gp gq Gp Gq)};

    my %searched_batch = map { $_->{batch} => 1 } @$searched;
    my @unsearched = grep { !$searched_batch{$_->{batch}} } @$all;

    my(@xs, @ys);          # restrictiveness, ln(elapsed) - one point
                            # per representative, unweighted: the fit
                            # wants real per-batch cost, not group
                            # totals
    my $measured_total       = 0;
    my $searched_batch_count = 0;
    for my $b (@$searched) {
        my $w = $b->{weight} // 1;
        $searched_batch_count += $w;

        my $use_G = (defined $Gp && !$b->{square});
        my $key = _cache_key(
            n => $n, k => $k, f => $f, batch => $b->{batch}, j => $j,
            gp => $gp, gq => $gq,
            ($use_G ? (Gp => $Gp, Gq => $Gq) : ()),
        );
        my $entry = $CACHE{$key};
        next unless $entry && $entry->{status} eq 'resolved';
        $measured_total += $w * $entry->{elapsed};

        next unless defined $b->{pattern};
        push @xs, restrictiveness_score($b->{pattern});
        push @ys, log(max($entry->{elapsed}, 1e-6));
    }

    my %distinct_x = map { $_ => 1 } @xs;
    if (keys(%distinct_x) < 2 || !@unsearched) {
        my $avg = $searched_batch_count
            ? $measured_total / $searched_batch_count : 0;
        return {
            total  => $measured_total + $avg * scalar(@unsearched),
            fitted => 0, n_fit => scalar(@xs),
        };
    }

    # Ordinary least squares: ln(elapsed) = a + b * restrictiveness.
    my($sx, $sy, $sxx, $sxy) = (0, 0, 0, 0);
    my $nfit = @xs;
    for my $i (0 .. $#xs) {
        $sx  += $xs[$i];
        $sy  += $ys[$i];
        $sxx += $xs[$i] ** 2;
        $sxy += $xs[$i] * $ys[$i];
    }
    my $denom = $nfit * $sxx - $sx * $sx;
    my($a, $b);
    if ($denom == 0) {
        ($a, $b) = ($sy / $nfit, 0);
    } else {
        $b = ($nfit * $sxy - $sx * $sy) / $denom;
        $a = ($sy - $b * $sx) / $nfit;
    }

    my $predicted_total = 0;
    for my $ub (@unsearched) {
        next unless defined $ub->{pattern};
        my $x = restrictiveness_score($ub->{pattern});
        $predicted_total += exp($a + $b * $x);
    }

    return {
        total  => $measured_total + $predicted_total,
        fitted => 1, n_fit => $nfit,
    };
}

# ---------------------------------------------------------------------
# Evaluate one (j, f, g[, G]) candidate against a set of batches under
# a given per-batch deadline, using the cache to skip anything already
# resolved or already known not to finish within this deadline.
#
# %opt: n, k, f, j, gp, gq, [Gp, Gq,] batches (arrayref from
# Calibrate::list_batches, optionally passed through
# representative_batches() first for a weighted subset), deadline,
# pcoul, jobs, xmax, modulus.
#
# When Gp/Gq are given, they are only applied to batches with
# square => 0 in the batch list, per the -G semantics: a wholly-square
# batch has nothing for -G to override, so it's run with plain -g
# regardless of whether a second gain was requested for this search.
#
# Returns { total, resolved_count, batch_count, all_resolved }. total
# is weighted by each batch's 'weight' field (default 1), so a caller
# using representative_batches() gets an extrapolated total directly.
# Sets $ABORT and returns immediately (without finishing the rest of
# this round) if any batch reports a solution.
# ---------------------------------------------------------------------

sub evaluate_candidate {
    my(%opt) = @_;
    my($n, $k, $f, $j, $gp, $gq, $batches, $deadline)
        = @opt{qw(n k f j gp gq batches deadline)};
    my($Gp, $Gq) = @opt{qw(Gp Gq)};

    my @need_run;
    for my $b (@$batches) {
        my $use_G = (defined $Gp && !$b->{square});
        my $key = _cache_key(
            n => $n, k => $k, f => $f, batch => $b->{batch}, j => $j,
            gp => $gp, gq => $gq,
            ($use_G ? (Gp => $Gp, Gq => $Gq) : ()),
        );
        my $entry = $CACHE{$key};
        next if $entry && $entry->{status} eq 'resolved';
        next if $entry && $entry->{status} eq 'timeout'
            && $entry->{best_timeout_tried} >= $deadline;

        push @need_run, {
            _key      => $key,
            n         => $n, k => $k, batch => $b->{batch},
            force_all => $f, strategy => $j,
            gain_p    => $gp, gain_q => $gq,
            ($use_G ? (gain2_p => $Gp, gain2_q => $Gq) : ()),
            xmax      => $opt{xmax},
            modulus   => $opt{modulus},
            deadline  => $deadline,
            pcoul     => $opt{pcoul},
        };
    }

    if (@need_run) {
        my @results = Calibrate::run_batches_parallel(\@need_run, $opt{jobs});
        for my $i (0 .. $#need_run) {
            my $job = $need_run[$i];
            my $res = $results[$i];
            croak "batch $job->{batch} run failed (exec_failed)"
                . " - is 'pcoul' the right path?"
                if $res->{status} eq 'exec_failed';

            if ($res->{status} eq 'timeout') {
                _cache_put($job->{_key}, {
                    status => 'timeout', best_timeout_tried => $deadline,
                });
            } elsif ($res->{status} eq 'exhausted') {
                _cache_put($job->{_key}, {
                    status => 'resolved',
                    elapsed => $res->{final}{elapsed},
                });
            } elsif ($res->{status} eq 'solution') {
                _cache_put($job->{_key}, {
                    status => 'resolved',
                    elapsed => $res->{solution}{elapsed},
                });
                $ABORT = {
                    n => $n, k => $k, f => $f, j => $j,
                    gp => $gp, gq => $gq, batch => $job->{batch},
                    v => $res->{solution}{v},
                };
                return {
                    total => 0, resolved_count => 0,
                    batch_count => scalar(@$batches), all_resolved => 0,
                };
            } else {
                croak "unexpected batch status '$res->{status}'"
                    . " for batch $job->{batch}";
            }
        }
    }

    my($total, $resolved_count) = (0, 0);
    for my $b (@$batches) {
        my $w = $b->{weight} // 1;
        my $use_G = (defined $Gp && !$b->{square});
        my $key = _cache_key(
            n => $n, k => $k, f => $f, batch => $b->{batch}, j => $j,
            gp => $gp, gq => $gq,
            ($use_G ? (Gp => $Gp, Gq => $Gq) : ()),
        );
        my $entry = $CACHE{$key};
        if ($entry && $entry->{status} eq 'resolved') {
            $total += $w * $entry->{elapsed};
            $resolved_count++;
        } else {
            $total += $w * $deadline;
        }
    }

    return {
        total          => $total,
        resolved_count => $resolved_count,
        batch_count    => scalar(@$batches),
        all_resolved   => ($resolved_count == @$batches),
    };
}

# ---------------------------------------------------------------------
# Race a set of gain candidates (rationals) against each other for a
# fixed (n, k, f, j), using a growing budget schedule and successive
# halving: each round, evaluate all not-yet-resolved survivors at the
# round's deadline, then keep only the better half (by resolved_count
# desc, then total asc), always keeping every fully-resolved candidate
# regardless of rank. Stops when at most one unresolved candidate
# remains, or the budget schedule is exhausted.
#
# %opt as for evaluate_candidate, plus:
#   candidates      => arrayref of [p,q] rationals
#   budget_schedule => arrayref of deadlines to try, increasing
#
# Returns an arrayref of { g => [p,q], total, resolved_count,
# all_resolved }, sorted best-first (resolved before unresolved, then
# by total ascending) - the caller typically only wants element 0, but
# the rest are kept for choosing a bracket for mediant refinement.
# ---------------------------------------------------------------------

sub race {
    my(%opt) = @_;
    my $candidates      = $opt{candidates};
    my $budget_schedule = $opt{budget_schedule};

    # @state is the master list: every candidate ever passed in stays
    # in it, and every candidate is evaluated at least once (round 1
    # always races the full set), so the final return always has a
    # real total for each of them - callers may need to look up a
    # *specific* candidate's result afterwards (e.g. the mediant
    # search matching lo/m/hi back up), and a silently-dropped
    # candidate would break that. @pool is the separate, shrinking
    # "still being actively raced" subset that successive halving
    # narrows down each round; dropping out of @pool just means we
    # stop spending further budget on it, not that it disappears.
    my @state = map {
        { g => $_, total => undef, resolved_count => 0, all_resolved => 0 }
    } @$candidates;
    my @pool = @state;

    for my $deadline (@$budget_schedule) {
        my @active = grep { !$_->{all_resolved} } @pool;
        last unless @active;

        for my $c (@active) {
            my $r = evaluate_candidate(
                %opt, gp => $c->{g}[0], gq => $c->{g}[1], deadline => $deadline,
            );
            my @fields = qw(total resolved_count batch_count all_resolved);
            @{$c}{@fields} = @{$r}{@fields};
            return [ sort { _race_cmp($a, $b) } @state ] if $ABORT;
        }

        @pool = sort { _race_cmp($a, $b) } @pool;
        last if @{[ grep { !$_->{all_resolved} } @pool ]} <= 1;

        # successive halving: keep every resolved candidate in the
        # pool, plus the better half of the unresolved ones (minimum
        # 2, so there's always something to keep racing next round).
        # This only shrinks @pool - @state (and thus the eventual
        # return value) is untouched.
        #
        # Never cut in the middle of a tie: if this round was wholly
        # or partly uninformative (e.g. every candidate timed out on
        # every batch, which happens whenever the round's deadline is
        # smaller than any candidate's true per-batch cost), several
        # candidates can be exactly tied on (resolved_count, total)
        # with no real information yet to separate them. Cutting there
        # would eliminate a possibly-excellent candidate based purely
        # on array order. Instead extend the keep boundary through any
        # tie straddling it, deferring the decision to a later,
        # larger-budget round where real differentiation shows up.
        my @resolved   = grep {  $_->{all_resolved} } @pool;
        my @unresolved = grep { !$_->{all_resolved} } @pool;
        my $keep = max(2, int(@unresolved / 2));
        $keep = min($keep, scalar @unresolved);
        $keep++
            while $keep < @unresolved
            && _race_cmp($unresolved[$keep - 1], $unresolved[$keep]) == 0;
        @unresolved = @unresolved[0 .. $keep - 1];
        @pool = (@resolved, @unresolved);
    }

    return [ sort { _race_cmp($a, $b) } @state ];
}

sub _race_cmp {
    my($a, $b) = @_;
    # Defensive: a mid-round abort (see race()) can return a snapshot
    # where some candidates were never evaluated. Callers discard such
    # snapshots once $ABORT is set, but the sort that builds them
    # should never warn regardless - treat "never evaluated" as worst.
    return  0 if !defined($a->{total}) && !defined($b->{total});
    return  1 if !defined $a->{total};
    return -1 if !defined $b->{total};
    return -1 if  $a->{all_resolved} && !$b->{all_resolved};
    return  1 if !$a->{all_resolved} &&  $b->{all_resolved};
    return $a->{resolved_count} <=> $b->{resolved_count}
        ? $b->{resolved_count} <=> $a->{resolved_count}
        : $a->{total} <=> $b->{total};
}

# ---------------------------------------------------------------------
# Full gain search for one (n, k, f, j): coarse log-spaced scan across
# [lo, hi] to find the right neighbourhood, then Stern-Brocot mediant
# refinement within the bracket formed by the winner's neighbours in
# the coarse scan.
#
# %opt as for evaluate_candidate (minus gp/gq/deadline), plus:
#   gain_lo, gain_hi  => float bracket for the coarse scan
#   n_coarse          => number of coarse points (default 7)
#   budget_schedule   => deadlines to race with (default (2,8,32,128))
#   refine_iters      => max mediant-refinement steps (default 12)
#   max_den_coarse    => denominator cap for coarse points (default 60)
#   refine_noise_frac => relative-improvement floor (default 0.02); see
#                        "plateau early-stop" below
#   refine_plateau_limit => consecutive sub-floor steps before stopping
#                        early (default 2)
#
# Returns { best => [p,q], total, coarse => [...], refine_trace => [...] }
# or undef if $ABORT got set along the way (check $ABORT).
#
# Plateau early-stop: a real run showed the mediant search spending
# most of its budget chasing g=4.58 over an earlier g=3.51 for a ~3.6%
# difference in total (19.9s vs ~19.2s) - well within run-to-run
# measurement jitter, not real signal. Each refinement step below
# tracks the incumbent's relative improvement over the step before it
# (0 whenever the incumbent isn't replaced); once refine_plateau_limit
# consecutive steps fall under refine_noise_frac, we stop rather than
# keep spending budget discriminating between candidates whose
# real-world difference doesn't matter. This can only stop the search
# EARLY relative to refine_iters - it never overrides which candidate
# currently sits in $incumbent, so the returned answer is always at
# least as good as the coarse scan's winner.
# ---------------------------------------------------------------------

sub search_gain {
    my(%opt) = @_;
    my $lo = $opt{gain_lo} // croak "search_gain: gain_lo required";
    my $hi = $opt{gain_hi} // croak "search_gain: gain_hi required";
    my $n_coarse   = $opt{n_coarse}   // 7;
    my $schedule   = $opt{budget_schedule} // [2, 8, 32, 128];
    my $max_den    = $opt{max_den_coarse} // 60;

    # log-spaced coarse points between lo and hi inclusive
    my @coarse_floats;
    if ($n_coarse <= 1) {
        @coarse_floats = ( sqrt($lo * $hi) );
    } else {
        my($llo, $lhi) = (log($lo), log($hi));
        for my $i (0 .. $n_coarse - 1) {
            push @coarse_floats,
                exp($llo + ($lhi - $llo) * $i / ($n_coarse - 1));
        }
    }
    my @coarse_rats = map { float_to_rational($_, $max_den) } @coarse_floats;

    my $ranked = race(
        %opt, candidates => \@coarse_rats, budget_schedule => $schedule,
    );
    return undef if $ABORT;

    my $best_coarse = $ranked->[0];

    # locate the winner's neighbours in float-sorted order, to use as
    # a refinement bracket - not simply $ranked (which is rank order)
    my @by_value = sort { rat_float($a) <=> rat_float($b) } @coarse_rats;
    my($win_idx) =
        grep { rat_eq($by_value[$_], $best_coarse->{g}) } 0 .. $#by_value;
    my $b_lo = $by_value[ max(0, $win_idx - 1) ];
    my $b_hi = $by_value[ min($#by_value, $win_idx + 1) ];
    $b_lo = $best_coarse->{g}
        if rat_eq($b_lo, $best_coarse->{g}) && $win_idx == 0;
    $b_hi = $best_coarse->{g}
        if rat_eq($b_hi, $best_coarse->{g}) && $win_idx == $#by_value;

    my @trace;
    my $refine_iters = $opt{refine_iters} // 12;

    # Incumbent-centred mediant search: $incumbent is always the best
    # candidate found so far and is NEVER discarded - each round probes
    # mediant(lo, incumbent) and mediant(incumbent, hi), i.e. the two
    # points immediately adjacent to the incumbent on the Stern-Brocot
    # tree within the current bracket, and only moves the bracket edge
    # (and swaps in a new incumbent) when a probe actually beats it.
    # This guarantees the search can never end up worse than the coarse
    # scan's winner - unlike probing mediant(lo, hi) directly, which
    # ignores where the incumbent actually sits between them and can
    # wander arbitrarily far from it if the bracket is uneven.
    my $incumbent = $best_coarse;
    my($cur_lo, $cur_hi) = ($b_lo, $b_hi);

    my $noise_frac  = $opt{refine_noise_frac}    // 0.02;
    my $plateau_lim = $opt{refine_plateau_limit} // 2;
    my $plateau_run = 0;

    for (1 .. $refine_iters) {
        my $m1 = mediant($cur_lo, $incumbent->{g});
        my $m2 = mediant($incumbent->{g}, $cur_hi);
        my $probe_lo = !rat_eq($m1, $incumbent->{g}) && !rat_eq($m1, $cur_lo);
        my $probe_hi = !rat_eq($m2, $incumbent->{g}) && !rat_eq($m2, $cur_hi);
        # both sides are Stern-Brocot leaves - fully converged
        last unless $probe_lo || $probe_hi;

        my @candidates;
        push @candidates, $m1 if $probe_lo;
        push @candidates, $m2 if $probe_hi;

        my $ranked3 = race(
            %opt, candidates => \@candidates, budget_schedule => $schedule,
        );
        return undef if $ABORT;
        push @trace, {
            lo => $cur_lo, incumbent => $incumbent->{g}, hi => $cur_hi,
            ranked => $ranked3,
        };

        my($rm1) = $probe_lo ? (grep { rat_eq($_->{g}, $m1) } @$ranked3) : ();
        my($rm2) = $probe_hi ? (grep { rat_eq($_->{g}, $m2) } @$ranked3) : ();

        my $new_best = (sort { _race_cmp($a, $b) }
            grep { defined } ($incumbent, $rm1, $rm2))[0];

        my $prev_total = $incumbent->{total};

        if (rat_eq($new_best->{g}, $incumbent->{g})) {
            # incumbent still wins - tighten whichever side(s) we
            # actually probed, leave the other bound as-is
            $cur_lo = $m1 if $probe_lo;
            $cur_hi = $m2 if $probe_hi;
        } elsif ($probe_lo && rat_eq($new_best->{g}, $m1)) {
            # old incumbent becomes the new upper bound
            $cur_hi    = $incumbent->{g};
            $incumbent = $new_best;
        } else {
            # old incumbent becomes the new lower bound
            $cur_lo    = $incumbent->{g};
            $incumbent = $new_best;
        }

        # Plateau/noise early-stop - see comment above the loop.
        my $improve = ($prev_total && $prev_total > 0)
            ? ($prev_total - $incumbent->{total}) / $prev_total : 0;
        $plateau_run = ($improve < $noise_frac) ? $plateau_run + 1 : 0;
        if ($plateau_run >= $plateau_lim) {
            push @trace, { plateau_stop => 1, after_iter => $_ };
            last;
        }
    }

    my $best = $incumbent;

    return {
        best         => $best->{g},
        total        => $best->{total},
        all_resolved => $best->{all_resolved},
        coarse       => $ranked,
        refine_trace => \@trace,
    };
}

1;

__END__

=head1 NAME

Calibrate::Search - racing/mediant search harness for pcoul calibration

=head1 STATUS

First working draft. Verified against a mock pcoul stand-in (not real
pcoul) to confirm the orchestration logic itself - caching, racing/
successive-halving, mediant refinement convergence, and abort-on-
solution - behaves correctly. Not yet run against real pcoul.

=cut
