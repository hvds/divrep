package Type::Track;
use strict;
use warnings;

use parent qw{ Type::Tauish };
use Math::GMP;
use Math::Prime::Util qw{ factor_exp is_prime };
use Memoize;

use ModFunc qw{ is_residue gcd };

my $zone = Math::GMP->new(1);

=head2 Type::Track

tau(d + i) = tau(n + i) for 0 <= i < k

A309981(n) is the smallest number k such that the value of n can be deduced
given only the values tau(n), tau(n+1), ..., tau(n+k), where tau is the number
of divisors function.

Establishing A309981(n) = x requires a) a proof that that tau signature of
(n, n + 1 .. n + x - 1) is unique; and b) a demonstration by counterexample
that the tau signature (n, n + 1 .. n + x - 2) is not unique.

=cut

sub init {
    my($self) = @_;
    my $n = $self->n;
    $self->{_target} = [ tau($n) ] if defined $n;
    return;
}

sub name { 'track' }
sub dbname { 'track' }

sub smallest { 1 }

memoize('gprio', NORMALIZER => sub { "$_[1]" });
sub gprio {
    my($self, $n) = @_;
    return -(
        (log($n) / log(2)) ** 1.8
    );
}

sub ming { 0 }

sub maxg {
    my($self, $n) = @_;
    # Cannot have two consecutive squares
    my $q = int(sqrt($n - 1)) + 2;
    return $q * $q - 1 - $n;
}

sub func_value {
    my($self, $n, $k, $d) = @_;
    return $d + $k;
}

sub func_target {
    my($self, $k) = @_;
    use Carp; Carp::confess("no k for func_target") unless defined $k;
    return $self->{_target}[$k] //= tau($self->n + $k);
}

sub apply_m {
    my($self, $m, $fm) = @_;
    my $c = $self->c;

    my $tm = tau($m);
    my $r = rad($m);
    my $mr = $m / $r;
    my $tmr = tau($mr);
    for (my $k = 0; $k < $self->f; ++$k) {
        my $tk = $self->func_target($k);
        if ($tk <= $tm) {
            # tau(mx) > tau(m)
            $c->suppress($m, (-$k) % $m, ($tk == $tm) ? $m - $k : 0);
        }
        if (($mr % $r) == 0 && $tk % $tmr) {
            # mx (mod m rad(m)) with (x, rad(m)) = 1 gives forced multiple
            for my $d (1 .. $r - 1) {
                next if gcd($d, $r) > 1;
                $c->suppress($m, ($mr * $d - $k) % $m);
            }
        }
        if ($tk & 1) {
            # square target, suppress all quadratic non-residues
            for my $d (grep !is_residue($_, $m), 0 .. $m - 1) {
                $c->suppress($m, ($d - $k) % $m);
            }
        }
    }
}

sub disallow {
    my($self, $d) = @_;
    return $self->n == $d;
}

sub check_fixed {
    my($self) = @_;
    my $n = $self->n;
    my $f = $self->f;
    #
    # Go through each k working out what factors are fixed, to find
    # opportunities for additional constraint optimizations.
    #
    my $fixpow;
    for my $k (@{ $self->to_test }) {
        my $tk = $self->func_target($k);
        my $force = $self->find_fixed($n, $tk, $k) or next;
        if ($fixpow) {
            printf "317 Ignoring secondary fix_power(%s)\n", join ', ', @$force;
            my $pell = $self->fix_pell($n, $fixpow, $force);
            if ($pell) {
                my($a, $b, $c) = @$pell;
                my $sign = ($b >= 0) ? '+' : do { $b = -$b; '-' };
                # FIXME: can we upgrade to resolving the Pell equation here?
                printf "317 satisfying Pell %s x^2 %s %s y^2 = %s\n",
                        $a, $sign, $b, $c;
            }
        } else {
            $fixpow = $force;
        }
    }
    return $fixpow;
}

sub float_spare {
    my($self, $n, $k) = @_;
    my $c = $self->c;
    my $kmult = $c->mult;
    my $kmod = ($c->mod_mult + $k) % $kmult;
    my $float = gcd($kmult, $kmod);
    my $spare = $kmult / $float;
    return ($float, $spare);
}

sub fix_pell {
    my($self, $n, $fix1, $fix2) = @_;
    my($k1, $x1, $z1) = @$fix1;
    my($k2, $x2, $z2) = @$fix2;
    return undef unless ($z1 & 1) == 0 && ($z2 & 1) == 0;

    my $a = $x1 ** ($z1 >> 1);
    my $b = -$x2 ** ($z2 >> 1);
    my $c = $k1 - $k2;
    my $g = gcd($a, gcd($b, $c));
    return [ map $_ / $g, ($a, $b, $c) ];
}

sub to_testf {
    my($self, $f) = @_;
    return [ 0 .. $f - 1 ];
}

sub test_target {
    my($self, $k) = @_;
    my $n = $self->n;
    my $tau = $self->func_target($k);
    return [ "$k", ($tau == 2)
        ? sub { is_prime($_[0] + $k) }
        : sub { $tau == tau($_[0] + $k) }
    ];
}   

#
# Calculate floor(y) given d: floor(y) = floor(((d + k) / x) ^ (1/z))
#
sub dtoy {
    my($self, $c, $val) = @_;
    my $base = $val + $c->pow_k;
    return +($base / $c->pow_x)->broot($c->pow_z);
}

sub dtoceily {
    my($self, $c, $val) = @_;
    my $g = $c->pow_g;
    return $g + $self->dtoy($c, $val - $g);
}

#
# Calculate d given y: d = xy^z - k
#
sub ytod {
    my($self, $c, $val) = @_;
    return $c->pow_x * $val ** $c->pow_z - $c->pow_k;
}

#
# Given y == y_m (mod m) and d = xy^z - k, return (d_s, s) as the
# value and modulus of the corresponding constraint on d, d == d_s (mod s).
# If no valid d is possible, returns s == 0.
#
sub mod_ytod {
    my($self, $c, $val, $mod) = @_;
    my($n, $k, $x, $z) = ($c->n, $c->pow_k, $c->pow_x, $c->pow_z);
    my $base = $x * $val ** $z - $k;
# CHECKME: should we increase $mod if gcd($mod, $z) > 1?
    return ($base % $mod, $mod);
}

#
# Given integer s, returns rad(s).
#
sub rad {
    my($s) = @_;
    my $p = 1;
    $p *= $_->[0] for factor_exp($s);
    return $p;
}

sub tau {
    my $n = shift;
    my $k = $zone;
use Carp; confess("@_") unless defined $n;
    $k *= $_->[1] + 1 for factor_exp($n);
    return $k;
}

1;
