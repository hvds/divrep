package Calibrate::Dickman;

use strict;
use warnings;

use base 'Exporter';
our @EXPORT_OK = qw(dickman_rho);

# ---------------------------------------------------------------------
# Dickman's rho function: rho(u) = the limiting probability (Dickman
# 1930) that a random integer x is x^(1/u)-smooth (all prime factors
# <= x^(1/u)). Defined by the delay differential equation
#     u * rho'(u) + rho(u-1) = 0,   rho(u) = 1 for 0 <= u <= 1.
#
# This is the standard theory behind ECM/P-1's success probability:
# a curve/attempt with smoothness bound B1 finds a factor p with
# probability ~ rho(ln(p)/ln(B1)) (see Calibrate::Ladder for how this
# gets used, and the boost calibration that accounts for stage 2).
#
# Numerically integrated once at load time via RK4 on a fixed-step
# grid, referencing rho(u-1) via linear interpolation of already-
# computed grid points - standard approach for this DDE. Validated
# this session against known published values: rho(2)=1-ln(2)=0.30685,
# rho(3)=0.04861, rho(4)=0.00491, rho(5)=0.0003547 - all matched to
# 4+ significant figures.
# ---------------------------------------------------------------------

use constant STEP => 0.001;
use constant MAXU => 20.0;

my @rho;
my $n_grid;

sub _init {
    return if @rho;
    $n_grid = int(MAXU / STEP) + 1;
    $rho[$_] = 0.0 for 0 .. $n_grid - 1;
    for my $i (0 .. $n_grid - 1) {
        my $u = $i * STEP;
        $rho[$i] = 1.0 if $u <= 1.0;
    }
    my $rho_at = sub {
        my ($u) = @_;
        return 1.0 if $u <= 0;
        my $idx = $u / STEP;
        my $i0 = int($idx);
        return $rho[$n_grid - 1] if $i0 >= $n_grid - 1;
        my $frac = $idx - $i0;
        return $rho[$i0] * (1 - $frac) + $rho[$i0 + 1] * $frac;
    };
    for my $i (1 .. $n_grid - 1) {
        my $u = $i * STEP;
        next if $u <= 1.0;
        my $u_prev = ($i - 1) * STEP;
        my $deriv = sub {
            my ($uu) = @_;
            return -$rho_at->($uu - 1) / $uu;
        };
        my $k1 = $deriv->($u_prev);
        my $k2 = $deriv->($u_prev + STEP / 2);
        my $k3 = $deriv->($u_prev + STEP / 2);
        my $k4 = $deriv->($u_prev + STEP);
        $rho[$i] = $rho[$i - 1] + (STEP / 6) * ($k1 + 2 * $k2 + 2 * $k3 + $k4);
        $rho[$i] = 0.0 if $rho[$i] < 0;
    }
}

sub dickman_rho {
    my ($u) = @_;
    _init();
    return 1.0 if $u <= 0;
    my $idx = $u / STEP;
    my $i0 = int($idx);
    return $rho[$n_grid - 1] if $i0 >= $n_grid - 1;
    my $frac = $idx - $i0;
    return $rho[$i0] * (1 - $frac) + $rho[$i0 + 1] * $frac;
}

1;
