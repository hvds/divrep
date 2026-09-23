package Calibrate::WalkCost;

use strict;
use warnings;

use base 'Exporter';
our @EXPORT_OK = qw(
    sumpm cost_prime_candidate cost_other_candidate
    estimate_walk_seconds calibrate_cpu_scale load_params save_params
    %PARAMS
);

# ---------------------------------------------------------------------
# Factorization-cost model for walk_v(), replacing the WALK_RATE
# placeholder constant in estimate_batch_cost()/_node_cost(). Companion
# to walk-cost-model-intro.md.
#
# DESIGN NOTE (this matters for recalibrate_walkcost.pl): every number
# that came from a real measurement lives in %DEFAULT_PARAMS below, not
# hardcoded inside the cost functions. That's deliberate - the intro
# doc's interim goal was a "maintainable, re-runnable" recalibration
# process, not a one-off fit, since the numbers here are expected to
# go stale the moment MPUGMP is upgraded (or the model runs on
# different hardware). All the actual MODELLING DECISIONS (which
# mixture, which shape, which variable to scale by) are structural
# code below and are NOT expected to need to change on recalibration -
# only the %DEFAULT_PARAMS values should. See recalibrate_walkcost.pl,
# which regenerates a params file by re-running the same benchmark
# commands this session used and re-deriving each of these numbers,
# then load_params() below applies it as an override.
#
# ===================================================================
# THE CENTRAL STRUCTURAL FINDING (unlikely to need recalibration - this
# is about which code paths exist, not their cost)
# ===================================================================
# walk_v() dispatches each of the k positions into one of three tests
# per candidate 'ati' (see coul.c's need_prime/need_square/need_other
# classification):
#   - need_prime (t==2): test_primes() -> tau_prime_prep()/tau_prime_run()
#     ("pretest" cheap-reject, then BPSW if pretest is inconclusive).
#   - need_square (t odd, first 2 such positions per ati): a completely
#     different, res_array()/Pell-based mechanism - NOT modelled here,
#     see calibration-estimator-status.md's have_square section for the
#     existing (crude) fallback. Calibrate::RootCount now provides an
#     exact g'th-root COUNT formula for the sq=1 case (validated for
#     g=2 and g=16 this session) - the missing half is the per-candidate
#     cost, which reuses cost_prime_candidate()/cost_other_candidate()
#     below directly (confirmed empirically on D(18,4) and D(68,6)
#     f(136,7)/f(368,6)-style batches), just called with the g'th ROOT's
#     own (smaller) bit-length rather than the full candidate's.
#   - need_other (everything else, including any 3rd+ simultaneous
#     square once the have_square<=2 cap is hit): test_multi() ->
#     tau_multi_prep()/tau_multi_run() - free trial division first,
#     THEN (rarely) an escalating ladder of b63/p-1/tinyqs/squfof/ecm/
#     simpqs.
#   - walk_1()/walk_1_set() (a position's tau reaches exactly 1): reuse
#     the SAME test_1primes()/test_1multi() -> tau_prime_prep()/
#     tau_multi_prep() machinery as the main loop, confirmed empirically
#     (D(18,4); D(68,6) f(136,7)/f(368,6)-scale batches b44/b89 with
#     -j2, 20 real completions observed). walk_1()'s total cost per
#     call is just the sum of cost_prime_candidate()/cost_other_
#     candidate() over the other k-1 positions - no candidate-count
#     estimation needed, always exactly one evaluation per call.
#     walk_1_set()'s candidate-count side (how many primes in
#     [plow,phigh] survive the residue filter) is structurally a
#     prime-counting question, same shape as Recursion.pm's existing
#     _li_diff() - NOT yet wired up. Its per-candidate cost is presumed
#     to reuse the same functions but has NOT been empirically
#     confirmed (exhaustive search of a full prime range on D(68,6)
#     b44/b89 with -j2, both before and after a 10x zmax widening,
#     found zero completions - plausibly a real structural property of
#     that specific case rather than insufficient search: a 10x zmax
#     widening only widens the prime range by 10^(1/16), so if the true
#     per-prime success probability is as small as ~2^-16, even our
#     combined ~13000-prime search across both attempts only had
#     perhaps a 1-in-3 chance of ever hitting a completion - a real
#     negative result, but a weak one. Flagged as unconfirmed, not
#     wrong.)
#
# Across every "natural" (un-forced-roughness) dataset gathered - D(12,7)
# b1/b2/b3/b9/b10/b11, D(12,9) b1/b3/b5/b7, D(80,7) b0/b3/b6/b8, spanning
# 9 to ~330 bits, ~580k logged stage-attempts total - the SAME two facts
# held everywhere:
#   1. need_prime: the cheap pretest (small-prime gcd) alone resolves
#      ~95% of candidates; only ~5% need a full BPSW check. No
#      escalation ladder at all on this path.
#   2. need_other: >99.5% of candidates resolve inside free trial
#      division (or one decisive primality/power check immediately
#      after it); genuine escalation into b63/p-1/ecm is RARE, and
#      simpqs was never once reached naturally at up to ~500 bits
#      across ~130,000 need_other candidates sampled (D(204,8) b43
#      included).
#
# WHY escalation is rare, and when it isn't (this is the load-bearing
# mechanism the model below leans on):
#   - Trial division kills a candidate the instant a found prime
#     factor's multiplicity is INCOMPATIBLE with the target tau t -
#     e.g. any multiplicity-1 factor gives a tau contribution of 2,
#     which is instant death whenever t is odd (real trace "div: 2 ~|
#     t=51" on D(204,8) b43 - confirmed, via hvds, to be the SECOND
#     occurrence of that dz() format string, in the odd-prime loop,
#     i.e. "the exponent-derived tau contribution doesn't divide the
#     remaining target" - NOT a parity-of-the-candidate-VALUE bug, an
#     earlier misreading of mine this session).
#   - A target t only genuinely RESISTS trial division when its
#     minimal factorization needs a prime with high multiplicity - the
#     precise trigger for -h<roughness>'s rough_assisted_tlim(). This
#     is what sumpm(t) (sum of (p-1) over t's prime factors WITH
#     multiplicity - matches divisors[].sumpm in coultau.c exactly)
#     measures.
#
# ===================================================================
# QS SUPPORT RANGE (structural - not a calibratable parameter)
# ===================================================================
# hvds (chat): coultau.c's tmfb[] bit-size brackets extend up to 511
# bits structurally, but simpqs's own internal size-tuned parameters
# are only sane up to ~91 decimal digits (~302 bits) - beyond that,
# even if tmfb[] bitmask includes it, a real simpqs call would misbehave
# or take impractically long, and in practice hvds runs -o200-style
# deferred/manual factorization (QS, GNFS, or parallel ECM) for
# anything past that. QS_MAX_BITS below encodes this: cost_simpqs_
# seconds() returns undef past it rather than an extrapolated (and per
# the intro doc's own chart, wildly unreliable well past its ~100-220
# bit measured range) number nobody would actually wait for.
# ---------------------------------------------------------------------

our %DEFAULT_PARAMS = (
    # need_prime mixture (see cost_prime_candidate)
    p_need_bpsw       => 22799 / 465048,  # combined D(12,7)/D(12,9)/D(80,7)
    cost_pretest_ns   => 50,              # near-clock-resolution placeholder
    bpsw_anchor_bits  => 60,
    bpsw_anchor_ns    => 2000,            # order-of-magnitude only - see
                                           # "known gaps": never bit-bucketed

    # need_other trial-division cost (see mean_prep_cost_ns)
    cost_prep_step_ns => 15,

    # need_other escalation probability, 2-point placeholder fit vs
    # sumpm(t) (see p_escalate - "known gaps": barely more than a
    # sketch, recalibrate_walkcost.pl should replace this with a real
    # regression once more (sumpm,rate) pairs exist)
    esc_low_sumpm_rate  => 0.003,   # sumpm<=18 (t=4,6,12,51)
    esc_high_sumpm      => 25,      # t=184's sumpm
    esc_high_sumpm_rate => 0.075,   # t=184's observed rate

    # ladder tail (see mean_ladder_cost_ns) - real samples,
    # f(368,6) b7, ~320-330 bits, target t=184
    ladder_tail => {
        b63    => { mean_ns => 0,          p_success => 1.00,     n =>   5 },
        'p-1'  => { mean_ns => 2_948_859,  p_success => 119/207,  n => 207 },
        ecm    => { mean_ns => 27_595_666, p_success =>  10/46,   n =>  46 },
    },
    p_reach_simpqs => 0.02,   # placeholder - never observed directly

    # QS chart (siqs-factor-benchmark.png, SIMPQS2 series), seconds per
    # input, Apple M1 Pro, digitised by eye (+-30%)
    simpqs_chart_s => {
        100 => 0.020, 110 => 0.014, 125 => 0.017, 140 => 0.035,
        160 => 0.090, 180 => 0.350, 200 => 1.500, 220 => 8.000,
    },
    qs_max_bits => 302,   # ~91 decimal digits (hvds, chat) - simpqs's
                           # own size-tuned internals aren't sane beyond
                           # this regardless of what tmfb[] permits

    cpu_scale => 1,        # set via calibrate_cpu_scale() per machine
);

our %PARAMS = %{ _deep_copy(\%DEFAULT_PARAMS) };

sub _deep_copy {
    my($v) = @_;
    if (ref $v eq 'HASH') {
        return { map { $_ => _deep_copy($v->{$_}) } keys %$v };
    }
    return $v;
}

# ---------------------------------------------------------------------
# load_params($path): merge a saved calibration (as written by
# recalibrate_walkcost.pl) over %DEFAULT_PARAMS into %PARAMS. The file
# is a bare Perl hashref literal (chosen over JSON so it needs no extra
# module - matches this codebase's existing no-nonstandard-deps style;
# NOT 'our %PARAMS = (...)', which would alias to this module's own
# %PARAMS global via do()'s caller-package semantics and silently
# break the merge below - see save_params()). Missing keys keep their
# default, so a params file only needs to contain what it actually
# recalibrated.
sub load_params {
    my($path) = @_;
    my $loaded = do $path;
    die "load_params($path): $@\n" if $@;
    die "load_params($path): $!\n" unless defined $loaded;
    die "load_params($path): expected a hashref\n" unless ref $loaded eq 'HASH';
    %PARAMS = %{ _deep_copy(\%DEFAULT_PARAMS) };
    for my $k (keys %$loaded) {
        if (ref $loaded->{$k} eq 'HASH' && ref $PARAMS{$k} eq 'HASH') {
            $PARAMS{$k} = { %{ $PARAMS{$k} }, %{ $loaded->{$k} } };
        } else {
            $PARAMS{$k} = $loaded->{$k};
        }
    }
    return \%PARAMS;
}

# ---------------------------------------------------------------------
# save_params($path, \%new_params): write a params file in the format
# load_params() expects. \%new_params need only contain the keys being
# recalibrated - recalibrate_walkcost.pl uses this after each benchmark.
sub save_params {
    my($path, $params) = @_;
    open my $fh, '>', $path or die "save_params($path): $!\n";
    print $fh "# Generated by recalibrate_walkcost.pl - see that script\n";
    print $fh "# for the benchmark commands each value came from, and\n";
    print $fh "# Calibrate::WalkCost::DEFAULT_PARAMS for what each key means.\n";
    print $fh "# NOTE: must be a bare hashref literal, not 'our %PARAMS = ...' -\n";
    print $fh "# the latter aliases to this module's own %PARAMS global (since\n";
    print $fh "# do() runs in the caller's package) and silently breaks\n";
    print $fh "# load_params()'s merge step. See load_params()'s comment.\n";
    print $fh "{\n";
    _dump_hash($fh, $params, 1);
    print $fh "};\n";
    close $fh;
}

sub _dump_hash {
    my($fh, $h, $indent) = @_;
    my $pad = '    ' x $indent;
    for my $k (sort keys %$h) {
        my $v = $h->{$k};
        if (ref $v eq 'HASH') {
            print $fh "$pad$k => {\n";
            for my $k2 (sort keys %$v) {
                my $v2 = $v->{$k2};
                if (ref $v2 eq 'HASH') {
                    print $fh "$pad    $k2 => {\n";
                    for my $k3 (sort keys %$v2) {
                        print $fh "$pad        $k3 => $v2->{$k3},\n";
                    }
                    print $fh "$pad    },\n";
                } else {
                    print $fh "$pad    $k2 => $v2,\n";
                }
            }
            print $fh "$pad},\n";
        } else {
            print $fh "$pad$k => $v,\n";
        }
    }
}

# ---------------------------------------------------------------------
# sumpm(t): sum of (p-1) over t's prime factors WITH multiplicity.
# Exactly matches coultau.c's divisors[].sumpm (coul.c:1646-1647) and
# drives rough_assisted_tlim()'s roughness threshold. Structural, not
# calibratable.
sub sumpm {
    my($t) = @_;
    my $s = 0;
    my $d = 2;
    my $n = $t;
    while ($d * $d <= $n) {
        while ($n % $d == 0) { $s += $d - 1; $n /= $d; }
        $d++;
    }
    $s += $n - 1 if $n > 1;
    return $s;
}

# ---------------------------------------------------------------------
# Log-linear interpolation/extrapolation through the chart's points -
# see save_params's note on QS_MAX_BITS for why this is capped.
sub _simpqs_chart_seconds {
    my($bits) = @_;
    my $chart = $PARAMS{simpqs_chart_s};
    my @b = sort { $a <=> $b } keys %$chart;
    if ($bits <= $b[0]) {
        return $chart->{$b[0]};
    }
    if ($bits >= $b[-1]) {
        my($b1, $b2) = @b[-2, -1];
        my $rate = log($chart->{$b2} / $chart->{$b1}) / ($b2 - $b1);
        return $chart->{$b2} * exp($rate * ($bits - $b2));
    }
    for my $i (0 .. $#b - 1) {
        my($b1, $b2) = @b[$i, $i + 1];
        next unless $bits >= $b1 && $bits <= $b2;
        my $frac = ($bits - $b1) / ($b2 - $b1);
        my $l1 = log($chart->{$b1});
        my $l2 = log($chart->{$b2});
        return exp($l1 + $frac * ($l2 - $l1));
    }
    die "unreachable";
}

# ---------------------------------------------------------------------
# calibrate_cpu_scale(): compare this machine's real wall time on the
# standalone QS build (simpqs-post54 recipe) against the chart, for
# hvds' two reference semiprimes, to get ONE scalar "this machine vs
# the chart's M1 Pro". %opt: bits1, seconds1, bits2, seconds2. Returns
# the geometric mean of the implied ratios (does NOT write to %PARAMS -
# caller decides, typically via save_params()).
sub calibrate_cpu_scale {
    my(%opt) = @_;
    my @ratios;
    for my $i (1, 2) {
        my $bits = $opt{"bits$i"} or next;
        my $secs = $opt{"seconds$i"} or next;
        push @ratios, $secs / _simpqs_chart_seconds($bits);
    }
    die "need at least one (bits,seconds) calibration pair\n" unless @ratios;
    my $logsum = 0;
    $logsum += log($_) for @ratios;
    return exp($logsum / @ratios);
}

# ---------------------------------------------------------------------
# cost_simpqs_seconds($bits): the chart curve, scaled by %PARAMS'
# cpu_scale. Returns undef past qs_max_bits (see design note above) -
# callers should treat undef as "not currently supported", not as
# zero or as license to guess.
sub cost_simpqs_seconds {
    my($bits) = @_;
    return undef if $bits > $PARAMS{qs_max_bits};
    return _simpqs_chart_seconds($bits) * $PARAMS{cpu_scale};
}

# ---------------------------------------------------------------------
# cost_prime_candidate($bits): expected seconds for ONE need_prime
# (t==2) candidate. Mixture of "pretest alone" and "pretest + full
# BPSW". cost_bpsw is a placeholder bits^2 shape relative to a single
# anchor point - see "known gaps" in the header.
sub cost_bpsw_ns {
    my($bits) = @_;
    return $PARAMS{bpsw_anchor_ns} * ($bits / $PARAMS{bpsw_anchor_bits}) ** 2;
}

sub cost_prime_candidate {
    my($bits) = @_;
    my $ns = $PARAMS{cost_pretest_ns}
        + $PARAMS{p_need_bpsw} * cost_bpsw_ns($bits);
    return $ns / 1e9;
}

# ---------------------------------------------------------------------
# p_escalate($t): probability a need_other candidate for target tau $t
# survives free trial division and needs the b63+ ladder. Placeholder
# 2-point linear ramp vs sumpm(t) - see "known gaps" in the header.
sub p_escalate {
    my($t) = @_;
    my $s = sumpm($t);
    my $lo_s = 18;   # t=51's sumpm - the calibration's low anchor
    return $PARAMS{esc_low_sumpm_rate} if $s <= $lo_s;
    return $PARAMS{esc_high_sumpm_rate} if $s >= $PARAMS{esc_high_sumpm};
    my $frac = ($s - $lo_s) / ($PARAMS{esc_high_sumpm} - $lo_s);
    return $PARAMS{esc_low_sumpm_rate}
        + $frac * ($PARAMS{esc_high_sumpm_rate} - $PARAMS{esc_low_sumpm_rate});
}

# ---------------------------------------------------------------------
# mean_prep_cost_ns($t): expected free-trial-division cost for a
# need_other candidate with target tau $t, before considering
# escalation. sumpm($t) compatible-factor-search steps at a fixed
# per-step cost.
sub mean_prep_cost_ns {
    my($t) = @_;
    return $PARAMS{cost_prep_step_ns} * (1 + sumpm($t));
}

# ---------------------------------------------------------------------
# mean_ladder_cost_ns($bits): expected cost GIVEN that a candidate has
# already escalated past trial division. Real b63/p-1/ecm sample means
# (not yet bit-scaled) plus the chart-based simpqs cost weighted by a
# placeholder reach-probability - both from %PARAMS. If cost_simpqs_
# seconds() reports unsupported (past qs_max_bits), that term is
# simply omitted (treated as 0) rather than guessed - see "known gaps":
# this UNDERSTATES cost for candidates that would need simpqs past
# that range, which in practice means "this branch would need manual/
# external factorization", not "it's free".
sub mean_ladder_cost_ns {
    my($bits) = @_;
    my $ns = 0;
    $ns += $PARAMS{ladder_tail}{$_}{mean_ns} for qw(b63 p-1 ecm);
    my $qs_s = cost_simpqs_seconds($bits);
    $ns += $PARAMS{p_reach_simpqs} * $qs_s * 1e9 if defined $qs_s;
    return $ns;
}

# ---------------------------------------------------------------------
# cost_other_candidate($t, $bits): expected seconds for ONE need_other
# candidate with target tau $t at $bits bits.
sub cost_other_candidate {
    my($t, $bits) = @_;
    my $ns = mean_prep_cost_ns($t)
        + p_escalate($t) * mean_ladder_cost_ns($bits);
    return $ns / 1e9;
}

# ---------------------------------------------------------------------
# estimate_walk_seconds(%opt): top-level entry point, meant to replace
# "$r_walk / WALK_RATE" in Recursion.pm's _node_cost(). NOT YET WIRED
# UP - Recursion.pm's r_walk has no visibility into the need_prime/
# need_square/need_other split for the positions being walked; that
# split would need to be exposed by top_level_gate() or recomputed here
# from the batch pattern before this can be called for real.
#
# %opt: r_walk (candidate count), need_prime_t (arrayref, always t=2),
# need_other_t (arrayref of t values), bits (candidate bit length).
sub estimate_walk_seconds {
    my(%opt) = @_;
    my $r_walk = $opt{r_walk} or return 0;
    my $bits = $opt{bits} // 64;

    my $per_candidate_ns = 0;
    for my $t (@{ $opt{need_prime_t} // [] }) {
        $per_candidate_ns += cost_prime_candidate($bits) * 1e9;
    }
    for my $t (@{ $opt{need_other_t} // [] }) {
        $per_candidate_ns += cost_other_candidate($t, $bits) * 1e9;
    }
    # have_square positions: count is exact via Calibrate::RootCount;
    # per-candidate cost reuses the functions above (confirmed this
    # session) but isn't wired up here yet - see header note.

    return $r_walk * $per_candidate_ns / 1e9;
}

1;
