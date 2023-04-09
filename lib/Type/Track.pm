package Type::Track;
use strict;
use warnings;

use parent qw{ Type };
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

sub func_name { 'tau' }
sub func { tau($_[1]) }
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
# Given integer s, returns rad(s).
#
sub rad {
    my($s) = @_;
    my $p = $zone;
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
