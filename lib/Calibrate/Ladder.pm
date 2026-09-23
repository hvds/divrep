package Calibrate::Ladder;

use strict;
use warnings;

use base 'Exporter';
our @EXPORT_OK = qw(
    p_success cost_fail cost_success expected_cost
    %RUNGS %FAMILY_BOOST
);

use Calibrate::Dickman qw(dickman_rho);

# ---------------------------------------------------------------------
# Per-rung escalation-cost model for the ECM/P-1 family of tmfa[]
# methods (coultau.c). Companion to Calibrate::WalkCost - NOT YET
# wired into it (see that module's ladder_tail/p_escalate placeholders,
# which this is meant to eventually replace with something
# theory-grounded rather than a 2-point linear-ramp guess).
#
# ===================================================================
# THE MODEL
# ===================================================================
# p_success(rung, factor_bits): probability a SINGLE call to this rung
# finds a factor of the given bit-size, via Dickman's rho:
#     u = ln(factor) / ln(B1 * boost)
#     p_single = rho(u)
#     p_success = 1 - (1 - p_single)^curves
# "boost" accounts for stage 2 (B2) extending the effective smoothness
# bound beyond a naive B1-only calculation - NOT part of the classical
# theory, purely an empirical fudge factor calibrated this session
# (see FAMILY_BOOST below and its accuracy caveats).
#
# cost_fail(rung, n_bits): expected cost of a FULL failed attempt
# (curves exhausted / B1+B2 phases exhausted, no factor found), as a
# function of n's TOTAL bit-size - NOT the factor size, which drives
# success probability instead, not cost. See RUNGS below for which
# rungs have a real fitted power-law curve (cost = cost_A * bits **
# cost_k) versus a single-anchor-point-plus-shared-exponent fallback.
#
# cost_success(rung, n_bits): expected cost GIVEN the attempt
# succeeds. hvds (chat, this session): "an initial estimate of success
# cost as half of failure cost (assume first success is uniformly
# spread across the spread of curves attempted), but I would expect
# the actual mean to be slightly less." Implemented exactly that way -
# 0.5 * cost_fail() - with the "slightly less" caveat left as a real,
# acknowledged bias (uniform-spread is the simplest assumption, not a
# measured one - see "known gaps" below) rather than something this
# module corrects for.
#
# expected_cost(rung, n_bits, factor_bits) combines both:
#     p * cost_success + (1-p) * cost_fail
#
# ===================================================================
# VALIDATION (this session)
# ===================================================================
# FAMILY_BOOST was fitted from ecm(200,4) and ecm(5000,20) (n=100
# trials/point, 8-11 points each, sweeping factor bitsize at FIXED
# total n bitsize via rungbench's smallbits parameter - separating
# the two effects that a naive single-total-bitsize sweep would
# conflate). Then tested as a genuine HELD-OUT prediction against
# ecm(40000,40) - a third configuration never used in fitting - BEFORE
# gathering any real data for it:
#     bits   predicted  observed   diff
#      30      1.000      1.000    0.000
#      40      1.000      1.000    0.000
#      50      0.997      1.000   -0.003
#      60      0.869      0.820    0.049
#      70      0.488      0.350    0.138
#      80      0.183      0.175    0.008
#      90      0.055      0.067   -0.012
#     100      0.015      0.000    0.015
# Errors mostly under 0.05, worst case 0.138 (still correctly locating
# the transition region) - real evidence the approach generalizes,
# not just fits noise. P-1(5M/100M) was ALSO checked and its own
# best-fit boost (25.8) turned out close to ECM's joint fit (27.3),
# though NOT identical - see "known gaps".
#
# ===================================================================
# KNOWN GAPS
# ===================================================================
# - FAMILY_BOOST is a single flat constant per family. Individually-
#   fit boosts for the two ECM configs used to calibrate it disagreed
#   with each other (35.0 for ecm(200,4) vs 18.8 for ecm(5000,20),
#   n=100 each) more than a "boost is universal" story would predict -
#   the shared value (27.3) is a reasonable compromise, not a tight
#   fit to either. There may be a genuine B1-or-B2/B1-ratio dependence
#   in the true boost that this flat-constant model doesn't capture.
#   Whether P-1 genuinely needs ITS OWN boost distinct from ECM's, or
#   whether one shared constant (~26) works for both, is not fully
#   resolved - early (small-sample) data suggested a big split (9.9 vs
#   29.9), but that mostly evaporated with larger samples (27.3 vs
#   25.8) - so probably NOT a real family-level distinction, but this
#   rests on exactly one well-resolved P-1 configuration.
# - cost_fail()'s bits-scaling exponent (cost_k) is only genuinely
#   FITTED (7 points, 100-500 bits) for p1_5M_100M. Every ECM rung
#   below reuses that SAME exponent (0.9253) anchored to its own
#   single known cost point at whatever bits it was tested at - an
#   assumption (same underlying GMP-modular-arithmetic cost shape
#   should transfer across methods) that has NOT been independently
#   verified for ECM specifically.
# - cost_success()'s "half of cost_fail" is explicitly a first-pass
#   heuristic per hvds, expected to overstate the true mean somewhat -
#   not yet corrected empirically (would need the real per-trial
#   success-time distribution, which rungbench's raw per-trial output
#   has but this module doesn't yet consume - see rungbench.c).
# - Both boost and the cost exponent were fit at ONE total-bits value
#   (200 or 300) per rung; whether "boost" itself is stable across
#   different total-n sizes (as opposed to just different factor
#   sizes at fixed n) hasn't been checked.
# ---------------------------------------------------------------------

our %FAMILY_BOOST = (
    ecm => 27.3,
    p1  => 25.8,   # see "known gaps" - may not be a real distinct value
);

# Shared cost-scaling exponent, fitted ONLY from p1_5M_100M (100-500
# bits, log-log least squares): cost = cost_A * bits ** cost_k.
use constant SHARED_COST_K => 0.9253;

our %RUNGS = (
    ecm_200_4 => {
        family => 'ecm', B1 => 200, curves => 4,
        # anchor: rungbench, n=100, bits=200, smallbits=50 (0% success
        # there) -> mean_ns_fail=4394034ns at 200 bits
        cost_k => SHARED_COST_K,
        cost_A => 4394034e-9 / (200 ** SHARED_COST_K),
    },
    ecm_5000_20 => {
        family => 'ecm', B1 => 5000, curves => 20,
        # anchor: rungbench, n=100, bits=300, smallbits=90 (0% success)
        # -> mean_ns_fail=322022370ns at 300 bits
        cost_k => SHARED_COST_K,
        cost_A => 322022370e-9 / (300 ** SHARED_COST_K),
    },
    ecm_40000_40 => {
        family => 'ecm', B1 => 40000, curves => 40,
        # anchor: rungbench, n=25, bits=300, smallbits=100 (0% success)
        # -> mean_ns_fail=4317003004ns at 300 bits
        cost_k => SHARED_COST_K,
        cost_A => 4317003004e-9 / (300 ** SHARED_COST_K),
    },
    p1_5M_100M => {
        family => 'p1', B1 => 5_000_000, curves => 1,
        # REAL fit (not a single-anchor guess) - rungbench-independent,
        # from the earlier ftest-based balanced sweep, 100-500 bits,
        # log-log least squares: cost = 0.0109464 * bits^0.9253
        cost_k => 0.9253,
        cost_A => 0.0109464,
    },
);

# ---------------------------------------------------------------------
sub p_success {
    my ($rung_key, $factor_bits) = @_;
    my $r = $RUNGS{$rung_key} or die "unknown rung $rung_key\n";
    my $boost = $FAMILY_BOOST{$r->{family}};
    my $u = ($factor_bits * log(2)) / log($r->{B1} * $boost);
    my $single = dickman_rho($u);
    return 1 - (1 - $single) ** $r->{curves};
}

sub cost_fail {
    my ($rung_key, $n_bits) = @_;
    my $r = $RUNGS{$rung_key} or die "unknown rung $rung_key\n";
    return $r->{cost_A} * ($n_bits ** $r->{cost_k});
}

sub cost_success {
    my ($rung_key, $n_bits) = @_;
    # hvds (chat): "an initial estimate of success cost as half of
    # failure cost... I would expect the actual mean to be slightly
    # less." Implemented literally as stated - see "known gaps" above.
    return 0.5 * cost_fail($rung_key, $n_bits);
}

sub expected_cost {
    my ($rung_key, $n_bits, $factor_bits) = @_;
    my $p = p_success($rung_key, $factor_bits);
    return $p * cost_success($rung_key, $n_bits)
         + (1 - $p) * cost_fail($rung_key, $n_bits);
}

1;
