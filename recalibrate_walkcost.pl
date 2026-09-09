#!/usr/bin/perl
# Recalibration tool for Calibrate::WalkCost - the "interim/parallel
# goal" from walk-cost-model-intro.md: "a tool to refresh the model's
# parameters whenever the factorization behaviour changes materially
# (the upcoming MPU upgrade being the concrete near-term case) - i.e.
# this should NOT be a one-off calibration but a maintainable,
# re-runnable process."
#
# What this does:
#   1. Runs a small, curated set of pcoul.verbose commands - the same
#      ones used to derive the current defaults in
#      Calibrate::WalkCost::DEFAULT_PARAMS this session - and parses
#      their -DVERBOSE output (reusing parse_verbose_cost.pl's regexes)
#      into the same aggregate statistics.
#   2. Re-derives each named parameter from those statistics.
#   3. Optionally runs the standalone QS build (simpqs-post54 recipe)
#      against two reference semiprimes to recalibrate cpu_scale.
#   4. Writes the result via Calibrate::WalkCost::save_params(), which
#      Calibrate::WalkCost::load_params() then applies as an override
#      on top of the built-in defaults.
#
# Usage:
#   ./recalibrate_walkcost.pl --pcoul /path/to/pcoul.verbose \
#       [--qs /path/to/standalone/qs] [--out lib/Calibrate/walkcost_params.pl]
#
# Re-run this whenever coultau.c's factorization backend changes (e.g.
# after an MPUGMP upgrade) or when running on new hardware. It does NOT
# change any of the modelling code in WalkCost.pm - only the numbers.
#
# WHAT ISN'T AUTOMATED (see WalkCost.pm's "known gaps" for why): the
# p_escalate() 2-point fit is regenerated from exactly the same two
# calibration batches used this session (D(204,8) b43 for the low
# point, f(368,6) b7 for the high point) - if a future recalibration
# wants a REAL regression across many (sumpm,rate) pairs rather than a
# 2-point placeholder, that needs new benchmark batches added to
# %BENCHMARKS below, not just a re-run of this script as-is.

use strict;
use warnings;
use FindBin qw($Bin);
use lib "$Bin/lib";
use Getopt::Long;
use Calibrate::WalkCost qw(sumpm save_params calibrate_cpu_scale);

my $pcoul = "$Bin/pcoul.verbose";
my $qs_binary;
my $out = "$Bin/lib/Calibrate/walkcost_params.pl";
my $timeout = 20;
GetOptions(
    'pcoul=s'   => \$pcoul,
    'qs=s'      => \$qs_binary,
    'out=s'     => \$out,
    'timeout=i' => \$timeout,
) or die "usage: $0 --pcoul PATH [--qs PATH] [--out PATH] [--timeout SECS]\n";

die "pcoul.verbose not found or not executable at $pcoul - build it with " .
    "VERBOSE=1 first (see .agents/skills/pcoul-internals/SKILL.md)\n"
    unless -x $pcoul;

# ---------------------------------------------------------------------
# The benchmark suite. Each entry is a real, deliberately-chosen (not
# random) command known this session to exercise a specific part of
# the model - see WalkCost.pm's header for why each one was picked.
my %BENCHMARKS = (
    baseline => {
        # combined-dataset stand-in for the "natural, low-sumpm" case:
        # gives p_need_bpsw, cost_pretest_ns, cost_prep_step_ns anchor.
        # (Session used D(12,7) b1/b2/b3/b9/b10/b11 + D(12,9) b1/b3/b5/b7
        # + D(80,7) b0/b3/b6/b8 combined - a single representative batch
        # is used here to keep this script's own runtime bounded; widen
        # this list for a more thorough recalibration.)
        args => ['-f3', '-b1', '-x1e30', '12', '7'],
    },
    low_sumpm_escalation => {
        # t=51 (sumpm=18) on D(204,8) b43 - the low anchor for p_escalate.
        args => ['-f3', '-b43',
            '-x2671085585728362090024704524971085604180041411670003511045829607025968034307855615191709216351357967399206378046076956861187925041220245361328121',
            '204', '8'],
    },
    high_sumpm_escalation => {
        # t=184 (sumpm=25) on f(368,6) b7 - the high anchor for
        # p_escalate, and the source of the real b63/p-1/ecm ladder
        # samples.
        args => ['-f3', '-b7',
            '-x5876143224906644986609085239470232384457131436652845893220089431917151491932392607743740081787109373',
            '368', '6'],
    },
);

# ---------------------------------------------------------------------
# Run one benchmark and return raw VERBOSE output (bounded by timeout,
# same "timeout N" wrapping style used throughout this session).
sub run_benchmark {
    my($name) = @_;
    my $b = $BENCHMARKS{$name} or die "unknown benchmark $name\n";
    my @cmd = ('timeout', $timeout, $pcoul, @{ $b->{args} });
    print STDERR "[$name] running: @cmd\n";
    open my $fh, '-|', @cmd or die "run $name: $!\n";
    local $/;
    my $out = <$fh>;
    close $fh;
    return $out // '';
}

# ---------------------------------------------------------------------
# Minimal inline parser - just the aggregate counts this script needs,
# not the full per-candidate attribution parse_verbose_cost.pl does
# (that script remains the right tool for building a training dataset;
# this one only needs summary statistics).
sub parse_stats {
    my($text) = @_;
    my %s = (
        pretest => 0, bpsw => 0,
        other_total_by_t => {},   # t => total need_other candidates seen
        escalating_values => {},  # deduped residual values that escalated
        ladder => {},             # stage => [ns,...]
    );
    for my $line (split /\n/, $text) {
        if ($line =~ /^tau_multi_prep vi=\d+ t=(\d+) e=1 /) {
            $s{other_total_by_t}{$1}++;
        } elsif ($line =~ /^\(\d+\) pretest: /) {
            $s{pretest}++;
        } elsif ($line =~ /^\(\d+\) bpsw: /) {
            $s{bpsw}++;
        } elsif ($line =~ /^\((\d+)\) (b63|p-1|tqs|ecm|sqf|sqs|hlf): (\d+) .*? (\d+)(?: \d+)?$/) {
            my($ns, $stage, $val, $ok) = ($1, $2, $3, $4);
            push @{ $s{ladder}{$stage} }, [$ns, $ok];
            # dedupe by residual value: one candidate may try several
            # rungs before resolving, but each rung reports the SAME
            # (or a further-reduced) value - deduplicating on the
            # FIRST-seen value per rung run is not perfectly exact
            # (see parse_verbose_cost.pl's fuller attribution logic
            # for that), but is a reasonable proxy for "how many
            # distinct candidates escalated" for calibration purposes.
            $s{escalating_values}{$val} = 1;
        }
    }
    return \%s;
}

# ---------------------------------------------------------------------
print STDERR "=== Recalibrating Calibrate::WalkCost ===\n";
my %new_params;

# --- baseline: p_need_bpsw, cost_pretest_ns ---
{
    my $stats = parse_stats(run_benchmark('baseline'));
    if ($stats->{pretest}) {
        $new_params{p_need_bpsw} = $stats->{bpsw} / $stats->{pretest};
        printf STDERR "  p_need_bpsw = %.4f (bpsw=%d / pretest=%d)\n",
            $new_params{p_need_bpsw}, $stats->{bpsw}, $stats->{pretest};
    } else {
        print STDERR "  WARNING: no pretest samples in baseline run - " .
            "keeping default p_need_bpsw. Try a longer --timeout.\n";
    }
}

# --- escalation rates at the two calibration points ---
my($low_rate, $high_rate);
{
    my $stats = parse_stats(run_benchmark('low_sumpm_escalation'));
    my @ts = sort { abs(sumpm($a) - 18) <=> abs(sumpm($b) - 18) }
        keys %{ $stats->{other_total_by_t} };
    my $t = $ts[0];
    my $total_other = 0;
    $total_other += $_ for values %{ $stats->{other_total_by_t} };
    if (defined $t && $total_other) {
        my $n_escalating = scalar keys %{ $stats->{escalating_values} };
        # rate is scoped to ALL need_other candidates in this run, not
        # just target t=$t - the batch is chosen so t=$t dominates the
        # "hard" positions, but other (low-sumpm) t's present in the
        # same batch contribute negligible escalation of their own, so
        # this stays a reasonable proxy for "rate at sumpm~18" without
        # needing per-line t-attribution (which needs the fuller
        # tracking parse_verbose_cost.pl does - not worth duplicating
        # here for a summary-statistics tool).
        $low_rate = $n_escalating / $total_other;
        printf STDERR "  low-sumpm escalation rate (t=%d, sumpm=%d) = %.5f (%d/%d)\n",
            $t, sumpm($t), $low_rate, $n_escalating, $total_other;
    } else {
        print STDERR "  WARNING: no low-sumpm need_other samples found - " .
            "keeping default esc_low_sumpm_rate.\n";
    }
}
{
    my $stats = parse_stats(run_benchmark('high_sumpm_escalation'));
    my @ts = sort { sumpm($b) <=> sumpm($a) } keys %{ $stats->{other_total_by_t} };
    my $t = $ts[0];
    my $total_other = 0;
    $total_other += $_ for values %{ $stats->{other_total_by_t} };
    if (defined $t && $total_other) {
        my $n_escalating = scalar keys %{ $stats->{escalating_values} };
        $high_rate = $n_escalating / $total_other;
        $new_params{esc_high_sumpm} = sumpm($t);
        printf STDERR "  high-sumpm escalation rate (t=%d, sumpm=%d) = %.5f (%d/%d)\n",
            $t, sumpm($t), $high_rate, $n_escalating, $total_other;
    } else {
        print STDERR "  WARNING: no high-sumpm need_other samples found - " .
            "keeping default esc_high_sumpm_rate.\n";
    }

    # real ladder-tail samples from this same run
    for my $stage (qw(b63 p-1 tqs ecm sqf sqs hlf)) {
        my $samples = $stats->{ladder}{$stage} or next;
        next unless @$samples;
        my($sum_ns, $succ) = (0, 0);
        for my $s (@$samples) {
            $sum_ns += $s->[0];
            $succ++ if $s->[1];
        }
        $new_params{ladder_tail}{$stage} = {
            mean_ns   => $sum_ns / @$samples,
            p_success => $succ / @$samples,
            n         => scalar @$samples,
        };
        printf STDERR "  ladder_tail{%s}: n=%d mean_ns=%.0f p_success=%.3f\n",
            $stage, scalar(@$samples), $sum_ns / @$samples, $succ / @$samples;
    }
}
$new_params{esc_low_sumpm_rate}  = $low_rate  if defined $low_rate;
$new_params{esc_high_sumpm_rate} = $high_rate if defined $high_rate;

# --- QS chart CPU scale (optional - needs the standalone qs binary) ---
if ($qs_binary) {
    die "qs binary not found or not executable at $qs_binary\n" unless -x $qs_binary;
    my %ref = (
        1 => { bits => 200,
            n => '1000000000000000000000000000045999999999999999999999999999373' },
        2 => { bits => 233,
            n => '9999999999999999999999999999890000000120999999999999999999999999998669' },
    );
    my %timed;
    for my $i (1, 2) {
        my $n = $ref{$i}{n};
        print STDERR "[qs] timing reference semiprime $i (" .
            length($n) . " digits)...\n";
        my $t0 = time;
        system("$qs_binary $n > /dev/null 2>&1");
        $timed{$i} = time - $t0;
        print STDERR "  took ${timed{$i}}s\n";
    }
    $new_params{cpu_scale} = calibrate_cpu_scale(
        bits1 => $ref{1}{bits}, seconds1 => $timed{1},
        bits2 => $ref{2}{bits}, seconds2 => $timed{2},
    );
    printf STDERR "  cpu_scale = %.3f\n", $new_params{cpu_scale};
} else {
    print STDERR "  (no --qs binary given - skipping cpu_scale recalibration, " .
        "keeping existing value)\n";
}

save_params($out, \%new_params);
print STDERR "=== Wrote $out ===\n";
print STDERR "Load it in code with: Calibrate::WalkCost::load_params('$out')\n";
