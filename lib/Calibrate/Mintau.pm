package Calibrate::Mintau;

use strict;
use warnings;

use base 'Exporter';
our @EXPORT_OK = qw(mintau divisors_ordered nth_prime);

# ---------------------------------------------------------------------
# Perl port of Hugo's mintau prototype (repo branch "with-mintau",
# script "mintau", commit 5b803bd), simplified: the original's
# incremental positional caching (keyed on gaps between used prime
# ranks, for efficient REPL-style repeated querying) is dropped in
# favour of a plain (t, excluded-prime-ranks) memo - correctness over
# raw speed, since this isn't (yet) a hot path. The core recursive
# algorithm is unchanged from the prototype:
#
#   mintau(t, excluded) = the smallest n with tau(n) = t, using no
#   prime in `excluded`. Recursion: pick the smallest available prime
#   p; for every divisor d of t with d >= highp(t) (using a SMALLER d
#   is never optimal - same pruning the prototype uses), the candidate
#   n = p^(d-1) * mintau(t/d, excluded + {p}); take the smallest.
#
# NOT YET VALIDATED against the real C implementation - only against
# the prototype's own embedded worked examples (t=4 -> 6, t=6 -> 12,
# t=8 -> 24, all with no exclusions), by hand, before this port. Still
# needs cross-checking against real coul.c mintau() calls (via -DCOUL_
# GATE_DEBUG-style instrumentation) the same way top_level_gate()'s
# aq formula was validated - the prototype itself is explicitly
# untested ("I'm not sure whether it works, or how accurate it is").
#
# Uses plain Perl integers/floats throughout, not bigint - fine for
# the modest t values in play (bounded by n), but mintau's RESULT can
# grow large for bigger n; revisit with Math::BigInt if that bites.
# ---------------------------------------------------------------------

# ---- small pure-Perl number theory helpers (no Math::Prime::Util in
# this sandbox) -------------------------------------------------------

sub factor_exp {
    my($n) = @_;
    my @out;
    my $d = 2;
    while ($d * $d <= $n) {
        if ($n % $d == 0) {
            my $e = 0;
            $e++, $n /= $d while $n % $d == 0;
            push @out, [$d, $e];
        }
        $d++;
    }
    push @out, [$n, 1] if $n > 1;
    return @out;
}

{
    my %divisors_cache;
    sub divisors_of {
        my($n) = @_;
        return @{ $divisors_cache{$n} //= do {
            my @d = (1);
            for my $fe (factor_exp($n)) {
                my($p, $e) = @$fe;
                my @new;
                my $pk = 1;
                for my $k (0 .. $e) {
                    push @new, map { $_ * $pk } @d;
                    $pk *= $p;
                }
                @d = @new;
            }
            [ sort { $a <=> $b } @d ];
        } };
    }
}

sub highp {
    my($n) = @_;
    die "highp(1) undefined\n" if $n == 1;
    my @fe = factor_exp($n);
    return $fe[-1][0];
}

sub max_factor {
    my($n) = @_;
    my $s = 0;
    $s += $_->[1] for factor_exp($n);
    return $s;
}

# ---------------------------------------------------------------------
# divisors_ordered($n): the SAME ordering as coul.c's divisors[n].div[]
# - ascending order, then a stable sort by descending highp(d), with
# highp(1) treated as lower than every real prime (so 1 always sorts
# last). Confirmed against hvds' worked example: divisors_ordered(30)
# = [5,10,15,30,3,6,2,1].
#
# divisors[n].highdiv (the count of "high group" entries - those with
# d >= highp(n) - which is all that prep_unforced_x's x-selection loop
# ever actually iterates over, per hvds' clarification) is exactly the
# length of the prefix sharing the same (maximal) highp value; we
# return that count too since callers computing "first_x" or replaying
# the x-selection loop need it.
# ---------------------------------------------------------------------

sub divisors_ordered {
    my($n) = @_;
    my @d = divisors_of($n);
    my %hp = map { $_ => ($_ == 1 ? -1 : highp($_)) } @d;
    my @sorted = sort { $hp{$b} <=> $hp{$a} } @d;
    my $highdiv = 0;
    $highdiv++ while $highdiv < @sorted && $hp{$sorted[$highdiv]} == $hp{$sorted[0]};
    return (\@sorted, $highdiv);
}

{
    my @primes;
    sub _prime_rank {
        # 1-based: _prime_rank(1)==2, _prime_rank(2)==3, ...
        my($r) = @_;
        while (@primes < $r) {
            my $cand = @primes ? $primes[-1] + 1 : 2;
            CAND: while (1) {
                for my $p (@primes) {
                    last if $p * $p > $cand;
                    next CAND if $cand % $p == 0;
                }
                last;
            } continue { $cand++ }
            push @primes, $cand;
        }
        return $primes[$r - 1];
    }
}

# Public wrapper - nth_prime(1)==2, nth_prime(2)==3, etc.
sub nth_prime { return _prime_rank($_[0]); }

sub _next_avail_rank {
    my($excluded_ranks, $from_rank) = @_;   # from_rank: 0-based "last used"
    my $r = $from_rank + 1;
    $r++ while $excluded_ranks->{$r};
    return $r;
}

{
    my %memo;
    sub mintau {
        my($t, $excluded_ranks) = @_;
        $excluded_ranks //= {};
        return 1 if $t == 1;

        my $key = "$t:" . join(',', sort { $a <=> $b } keys %$excluded_ranks);
        return $memo{$key} if exists $memo{$key};

        my $rank = _next_avail_rank($excluded_ranks, 0);
        my $p = _prime_rank($rank);
        my $hp = highp($t);

        my $best;
        for my $d (divisors_of($t)) {
            next if $d < $hp;
            my $px = $p ** ($d - 1);
            last if defined($best) && $px >= $best;   # can only get worse
            my $sub = mintau($t / $d, { %$excluded_ranks, $rank => 1 });
            my $cand = $px * $sub;
            $best = $cand if !defined($best) || $cand < $best;
        }
        return $memo{$key} = $best;
    }
}

1;
