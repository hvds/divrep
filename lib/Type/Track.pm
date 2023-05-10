package Type::Track;
use strict;
use warnings;

use parent qw{ Type::Tauish };
use Math::GMP;
use Math::Prime::Util qw{ factor_exp is_prime invmod };
use Memoize;

use ModFunc qw{ gcd };
use RootMod qw{ is_residue };

my $zone = Math::GMP->new(1);

my %PROG = (
    cul => './pcrul',
);

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
        (log($n) / log(2)) ** 2.0
    );
}

sub fprio {
    my($self, $n, $k, $expect) = @_;
    my $prio = $self->gprio($n);
    if ($expect) {
        if ($expect < 0) {
            use Carp; Carp::confess("$expect");
        }
        # deprioritize more rapidly than the default with rising $expect
        $prio += List::Util::min(0, -(log($expect) / log(2)) ** 1.6);
    }
    return $prio;
}

sub ming { 0 }

sub maxg {
    my($self, $n) = @_;
    # Special-case, since pcrul doesn't handle it
    return 0 if $n == 1;
    # Cannot have two consecutive squares
    my $q = isqrt($n - 1) + 2;
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

sub prog {
    my($self, $which) = @_;
    return $PROG{$which} // $self->SUPER::prog($which);
}

# TODO: if d+k+r^2 = z^2 (typically with r=1), then d+k = (z-r)(z+r),
# so tau(d+k) is at least 4, and may be forced higher if we know further
# divisibility of z-r or z+r. Is there some way we can track that, eg
# after applying a fix_power?
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

sub validate_fixpow {
    my($self, $force) = @_;
    my $c = $self->c;
    my($k, $x, $z) = @$force;
    my($v, $m) = ($c->mod_mult, $c->mult);
    $v = ($v + $k) % $m;
    $v /= $x;
    $m /= $x;
    return if is_residue($v, $m);
    printf <<OUT, $k, ($x != 1 ? $x : ''), $z, $v, $m;
405 Error: Fixed power v_%s = %sy^%s is non-residue %s (mod %s)
OUT
    exit 1;
}

sub check_fixed {
    my($self) = @_;
    my $n = $self->n;
    #
    # Go through each k working out what factors are fixed, to find
    # opportunities for additional constraint optimizations.
    #
    my $fixpow;
    for my $k (@{ $self->to_test }) {
        my $tk = $self->func_target($k);
        my $force = $self->find_fixed($n, $tk, $k) or next;
        $self->validate_fixpow($force);
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
        # dig for more information
        $self->from_fixpow($force);
    }
    return $fixpow;
}

# given d+k = xy^z is known, do other d+i have known factorizations?
sub from_fixpow {
    my($self, $fixpow) = @_;
    my $c = $self->c;
    my $n = $self->n;
    my($k, $x, $z) = @$fixpow;
    my $xq = remove_squares($x);

    # Main apply() will not have seen v_k = xy^z when x > 1, but does
    # this achieve anything if we're about to fix a power anyway?
    # Probably only for discarded secondary fixes.
    if (0 && $x > 1) {
        my $cp = $c->checkp;
        for my $p (grep is_prime($_), 2 .. $c->check) {
            last if $cp && $p > $cp;
            my $px = 1;
            if (($x % $p) == 0) {
                my $xx = $x;
                while (($xx % $p) == 0) {
                    $xx /= $p;
                    $px *= $p;
                }
            }
            $p = 8 if $p == 2;
            my $inv = (($x % $p) == 0) ? 1 : (
                invmod($x, $p) // do { warn "($x,$p) noinv\n"; next }
            );
            my $pxx = $px * $p;
warn "for [$k, $x, $z] p=$p: px=$px, inv=$inv\n";
            for my $d (grep !is_residue($_, $p), 0 .. $p - 1) {
warn ".. nr $d => @{[ ($d * $px * $inv - $k) % $pxx ]} mod $pxx\n";
                $c->suppress($pxx, ($d * $px * $inv - $k) % $pxx);
            }
        }
    }

    # try x_q(y-i)(y+i)
    for (my $i = 1; $i * $i * $xq <= $k; ++$i) {
        my $ki = $k - $i * $i * $xq;
        my $ti = $self->func_target($ki);
        if ($ti < 4) {
            # must fail when y-i > 1
            $c->suppress(1, 0, $xq * ($i + 2)**2 - $k);
            next;
        }
        my($float, $spare) = $self->float_spare($n, $ki);
        my $fixp = gcd($spare, $float);
        my($fixed_tau, $fixed, $float_tau, @ffact) = (1, $zone, 1);
        for (factor_exp($float)) {
            my($p, $px) = @$_;
            if ($self->is_fixed($p, $px, $c, $n, $fixp)) {
                # take the fixed power, splice out of the list of remaining
                # floating powers
                $fixed_tau *= $px + 1;
                $fixed *= $p ** ($px - 1);
            } else {
                $float_tau *= $px + 1;
                push @ffact, [$p, $px];
            };
        }

        my $fail = sub {
            printf <<OUT, $fixed_tau, $float_tau, $ti, $ki, $c->elapsed;
502 Error: fixed %s, float %s not available in tau %s for k=%s (%.2fs)
OUT
            exit 1;
        };
        $fail->() if $ti % $fixed_tau;

        my $tf = $ti / $fixed_tau;
        $fail->() if $tf < $float_tau;

        my @tff = factor_exp($tf);
        # If we can satisfy floating powers with two spare factors,
        # we have no constraint.
        next if liftable($tf, 2, $float_tau, \@ffact);

        # If we can satisfy with one spare factor, best is when all
        # fixed and (maximized) floating factors are on one side.
        my $best = $fixed * liftable($tf, 1, $float_tau, \@ffact);

        unless ($best) {
            # If we can satisfy only without spare factors, best (if
            # it exists at all) will involve a balance of the fixed
            # and floating factors on either side; we assume this is
            # already so restrictive that a crude approximation will do.
            $best = $fixed * liftable($tf, 0, $float_tau, \@ffact);
            $fail->() unless $best;
            $best = isqrt($best);
        }

        # the highest case that can hit required tau occurs when
        # x_q(y-i) = best, (y+i) is prime
        my $y = $best / $xq + $i;
        printf <<OUT, $k, $float, $float * $spare, $ki, $xq, $y;
318 fix_power at v_%s with %s (mod %s) at v_%s fails after %s.%s^2
OUT
        $c->suppress(1, 0, $xq * $y * $y - $k);
    }

    # TODO: try x(y^2+i)(...) if z is divisible by any odd prime
}

sub liftable {
    my($target, $sparep, $prod, $powers) = @_;
    while ($sparep) {
        return 0 if $target <= 1;
        my $minp = [ factor_exp($target) ]->[0][0];
        $target /= $minp;
        --$sparep;
    }
    return 0 if $target < $prod;
    return 1 unless @$powers;
    my @uppowers = map {
        my($p, $e) = @$_;
        [ $p, $e + 1 ];
    } @$powers;
    my $best = 0;
    _liftable_r($target, $prod, \@uppowers, 0, \$best);
    return $best;
}

sub _liftable_r {
    my($target, $prod, $powers, $index, $rbest) = @_;
    return if $target < $prod;
    if (($target % $prod) == 0) {
        local $powers->[-1][1] = $powers->[-1][1] * ($target / $prod);
        my $this = _deprod($powers);
        $$rbest = $this if $$rbest < $this;
        return;
    }
    return if $index >= @$powers;
    my $base = $powers->[$index][1];
    for my $newpow ($base .. 2 * $base - 1) {
        my $newprod = $prod * $newpow / $base;
        local $powers->[$index][1] = $newpow;
        _liftable_r($target, $newprod, $powers, $index + 1, $rbest);
    }
    return;
}

sub _deprod {
    my($powers) = @_;
    my $s = $zone;
    for (@$powers) {
        my($p, $x) = @$_;
        $s *= $p ** ($x - 1);
    }
    return $s;
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

# Given n, return min x: n = xy^2 for any y.
sub remove_squares {
    my($n) = @_;
    my $s = 1;
    for (factor_exp($n)) {
        my($p, $x) = @$_;
        $s *= $p if $x & 1;
    }
    return $s;
}

sub isqrt {
    my($n) = @_;
    return ref($n) ? $n->bsqrt : int(sqrt($n));
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
