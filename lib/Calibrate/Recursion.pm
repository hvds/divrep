package Calibrate::Recursion;

use strict;
use warnings;
use Calibrate::Mintau qw(mintau divisors_ordered);

use base 'Exporter';
our @EXPORT_OK = qw(top_level_gate estimate_batch_cost);

# ---------------------------------------------------------------------
# Exact walk-vs-recurse gate for a batch's recursion tree, plus a
# Mertens-style estimator for the full tree beyond the first decision.
#
# aq (validated - see chat, D(12,7) batches b1/b6/b37/b43, D(12,2)
# -f0 b0):
#
#   aq = PRODUCT over every distinct prime p appearing ANYWHERE in the
#        batch's full pattern of p^(maxexp(p) [+1 if p==2])
#
# where maxexp(p) is that prime's HIGHEST exponent anywhere in the
# pattern (apply_primary() is called once per prime, for its highest-
# exponent occurrence; apply_secondary() handles every other
# occurrence and does NOT touch aq). The "+1 if p==2" reflects the
# "even modulus gets upgraded one bit" rule in update_chinese(); there
# is NO unconditional bootstrap - confirmed against D(12,2) -f0 (a
# fully-unforced batch: aq=1, not 2).
#
# vi selection (which position gets worked on): NOT "the first '.' in
# the pattern" - that was an early wrong assumption of mine, specific
# to how -j0 happens to behave, not a general truth (hvds, chat). The
# real rule is best_v(j): -j0 picks the position with the HIGHEST
# remaining t_i (-j2: LOWEST), tied by highest q_i, tied by lowest
# position index, restricted to positions whose remaining t_i has an
# odd prime factor (a pure power of 2, or t_i==1, is ineligible under
# -j0/-j2 - only -j4 allocates powers of 2, not modelled here). This
# needs every position's evolving state, not just originally-'.' ones:
# a forced position whose shown pattern token doesn't reach the full
# tau=n is still in play, just passed over while a bigger-t_i position
# is available (confirmed: D(12,9) b37's position 0 never gets its own
# gate call, not because it's complete, but because its remaining
# t_i=6 is never the largest available). "First '.'" only coincides
# with best_v(0)'s choice because a totally fresh position has t_i=n,
# the maximum possible value, so -j0 will always prefer it over any
# partially-forced position when one exists - it is NOT true in
# general and NOT true at all for -j2.
#
# mintau() exclusion set: exactly the primes that get a REAL (x>1)
# allocation somewhere in the batch - i.e. the same prime set that
# maxexp{} above already identifies for aq. NOT "the first f primes"
# (an earlier version of this code used that rule after validating it
# against a real pcoul trace - it matched, but for the wrong reason: a
# bug in apply_null() was marking force-candidate primes as used even
# when a specific batch's combination assigned them nothing (x=0,
# "null" application), which happened to equal f for every batch since
# apply_batch() always considers exactly the first f primes as
# candidates. hvds found and fixed this bug upstream (apply_pfreev
# only excludes when x>1 now); re-validated against the fixed binary,
# which changed b1's real limp from 3603 to 5345 - confirming the
# exclusion set is the *visible* primes, not a count of f). Below the
# top level, the exact identity-based rule is path-dependent (a
# density approach can't track one path); per hvds' guidance this is
# approximated as a COUNT: exclude the smallest (n_pattern_primes +
# depth) primes, where n_pattern_primes is the real distinct-prime
# count in the initial pattern and depth is how many (approximated)
# allocations have been made on the way to this node.
#
# have_square is NOT modelled (different r_walk formula - g'th-root +
# res_array()->count, a piece neither of us has derived) - per hvds,
# deliberately deferred since it's usually a small fraction of total
# cost. x a power of 2, x==nextt with x prime, and external modular
# constraints (-m) are also not modelled (different limit_p branches).
# ---------------------------------------------------------------------

# ---- shared state building --------------------------------------------

sub _build_positions_and_aq {
    my($n, $k, $pattern) = @_;
    my($sq_tag) = $pattern =~ /\[sq=(\d+)\]/;
    my @pos = grep { $_ !~ /^\[/ } split ' ', $pattern;

    my @positions;
    my %maxexp;
    for my $i (0 .. $k - 1) {
        my $tok = $pos[$i];
        if (!defined($tok) || $tok eq '.') {
            push @positions, { t => $n, logq => 0 };
            next;
        }
        my $tau  = 1;
        my $logq = 0;
        for my $factor (split /\./, $tok) {
            my($p, $e) = $factor =~ /^(\d+)(?:\^(\d+))?$/
                or die "_build_positions_and_aq: bad token '$factor'\n";
            $e = defined($e) ? $e + 0 : 1;
            $tau  *= $e + 1;
            $logq += $e * log($p);
            $maxexp{$p} = $e if !defined($maxexp{$p}) || $e > $maxexp{$p};
        }
        push @positions, { t => $n / $tau, logq => $logq };
    }

    my $aq = 1;
    for my $p (keys %maxexp) {
        my $e = $maxexp{$p};
        $e++ if $p == 2;
        $aq *= $p ** $e;
    }

    return (\@positions, $aq, scalar keys %maxexp, $sq_tag);
}

sub _best_v {
    my($j, $positions) = @_;
    my $best;
    for my $i (0 .. $#$positions) {
        my $t = $positions->[$i]{t};
        next if $t == 1;
        next if ($t & ($t - 1)) == 0;   # pure power of 2: ineligible
                                          # for -j0/-j2 (needs -j4)
        my $cand = { i => $i, t => $t, logq => $positions->[$i]{logq} };
        if (!defined $best) { $best = $cand; next; }
        my $better =
            $j == 0 ? ($t > $best->{t}) :
            $j == 2 ? ($t < $best->{t}) :
            die "_best_v: only j=0,2 implemented\n";
        if (!$better && $t == $best->{t}) {
            $better = $cand->{logq} > $best->{logq};
            $better ||= ($cand->{logq} == $best->{logq} && $i < $best->{i});
        }
        $best = $cand if $better;
    }
    return $best ? $best->{i} : undef;
}

# ---------------------------------------------------------------------
# _gate_decision: the shared walk-vs-recurse decision, usable both at
# depth 0 (top_level_gate) and at any depth (_node_cost). Valid only
# for have_square==0, x not a power of 2, no external modular
# constraint (see module intro).
#
# %args: j, positions, aq, k, n_excl_base (baseline exclusion count -
# real distinct-prime count for depth 0, approximate count-based
# running total below that), depth, zmax, gp, gq.
#
# Returns undef if no position is eligible (best_v found nothing - see
# _best_v). Otherwise a hashref: { vi, x, nextt, r_walk, p, limp, cap,
# decision }.
# ---------------------------------------------------------------------

sub _gate_decision {
    my(%a) = @_;
    my($j, $positions, $aq, $k, $n_excl_base, $depth, $zmax, $gp, $gq)
        = @a{qw(j positions aq k n_excl_base depth zmax gp gq)};

    my $vi = _best_v($j, $positions);
    return undef unless defined $vi;

    my $t = $positions->[$vi]{t};

    # have_square trigger: an ODD remaining tau (>1) means this
    # position's completing value must be a perfect square (standard
    # number theory: tau(v) is odd iff v is a perfect square) - pcoul
    # switches to a different formula here (g'th-root walk size times
    # res_array()->count - see module intro), which this code does NOT
    # implement. Flagged rather than silently run through the WRONG
    # (non-square) formula: doing that produced wild errors on real
    # data (D(12,9) b132: 67,698x over-predicted). Per hvds (chat),
    # deliberately not modelled further - measured directly against
    # real D(12,9) data, square-affected batches are ~0.06% of total
    # walkc and ~0.29% of total elapsed time, so precision here isn't
    # worth chasing. Callers should treat this as a cheap terminal,
    # not recurse into it with the general machinery.
    if ($t % 2 == 1 && $t > 1) {
        my $r_walk = int($zmax / $aq);
        $r_walk = int(($r_walk * $gp) / $gq);
        return { vi => $vi, x => undef, nextt => undef, r_walk => $r_walk,
            p => undef, limp => undef, cap => undef, decision => 'WALK',
            have_square => 1 };
    }
    my($ordered, undef) = divisors_ordered($t);
    my $x     = $ordered->[0];
    my $nextt = $t / $x;

    my $r_walk = int($zmax / $aq);
    $r_walk = int(($r_walk * $gp) / $gq);

    # maxforce[vi]-derived starting-prime seed, per prep_maxforce().
    # Two branches: n % 4 != 0 gives a uniform maxforce[i]=k for every
    # position (needed for D(18,*): 18 % 4 == 2); n % 4 == 0 uses the
    # position-dependent k-vi-1 formula (already validated against
    # D(12,*) - see chat). Unaffected by the apply_null/pfreev bug or
    # its fix (confirmed: p was unchanged across old/new binaries in
    # every re-checked trace).
    my $p_start;
    if ($a{n} && $a{n} % 4 != 0) {
        $p_start = $k;
    } else {
        my $mf = $k - $vi - 1;
        $mf = $vi if $vi > $mf;
        $mf = $a{f} if defined($a{f}) && $a{f} > $mf;
        $p_start = $mf;
    }

    my %excl = map { $_ => 1 } (1 .. $n_excl_base + $depth);
    my $mint = $nextt > 1 ? mintau($nextt, \%excl) : 1;
    # lp_x uses the POSITION-SPECIFIC accumulated allocation (ap->q in
    # the C code), NOT the whole-batch aq - these are different
    # quantities: aq (CRT-combined modulus) belongs in r_walk above;
    # q_vi (this position's own product-so-far) belongs here. Missing
    # this distinction was a real bug (see chat) - it happened to be
    # absent from the original top_level_gate (q_vi==1 there, a fresh
    # position, so the bug was invisible), but was already present in
    # _node_cost before this refactor, then got propagated to BOTH
    # once the code was unified - caught by re-validating top_level_
    # gate's known-good values after the refactor.
    my $q_vi = exp($positions->[$vi]{logq});
    my $lp_x = int(($zmax + $vi) / $q_vi);
    $lp_x = int($lp_x / $mint) if $nextt > 1;
    my $limp = int($lp_x ** (1 / ($x - 1)));
    $limp++ while ($limp + 1) ** ($x - 1) <= $lp_x;
    $limp-- while $limp ** ($x - 1) > $lp_x;
    my $cap = $limp;

    my $decision = ($r_walk < (($cap < $p_start) ? 0 : $cap - $p_start))
        ? 'WALK' : 'RECURSE';

    return { vi => $vi, x => $x, nextt => $nextt, r_walk => $r_walk,
        p => $p_start, limp => $limp, cap => $cap, decision => $decision };
}

# ---------------------------------------------------------------------
# top_level_gate(%opt): the single decision at the very start of a
# batch's recursion (depth 0).
#
# %opt: n, k, f, j (0 or 2), pattern, zmax, gp, gq.
# Returns undef if nothing is eligible (shouldn't happen for f < k in
# practice), else { vi, x, nextt, aq, r_walk, p, limp, cap, decision }.
# ---------------------------------------------------------------------

sub top_level_gate {
    my(%opt) = @_;
    my($n, $k, $f, $j, $pattern, $zmax, $gp, $gq)
        = @opt{qw(n k f j pattern zmax gp gq)};
    $j //= 0;

    my($positions, $aq, $n_pattern_primes, $sq_tag)
        = _build_positions_and_aq($n, $k, $pattern);

    # [sq=N]-tagged batches: have_square is set globally from the very
    # first decision (see estimate_batch_cost for the full rationale -
    # this mirrors that short-circuit for consistency, since here the
    # square position is typically NOT the one best_v would even
    # select - it has remaining tau exactly 1, making it ineligible in
    # _best_v - so without this check the general machinery would
    # silently compute a non-square decision for a batch that's
    # actually square throughout).
    if (defined $sq_tag) {
        my $r_walk = int($zmax / $aq);
        $r_walk = int(($r_walk * $gp) / $gq);
        return { vi => undef, x => undef, nextt => undef, aq => $aq,
            r_walk => $r_walk, p => undef, limp => undef, cap => undef,
            decision => 'WALK', have_square => 1 };
    }

    my $g = _gate_decision(j => $j, positions => $positions, aq => $aq,
        k => $k, n_excl_base => $n_pattern_primes, depth => 0,
        zmax => $zmax, gp => $gp, gq => $gq, n => $n, f => $f);
    return undef unless $g;

    return { %$g, aq => $aq };
}

# ---------------------------------------------------------------------
# Mertens-style multi-level cost estimator - see module intro for the
# density/mean-field/count-based approximations involved.
#
# CRITICAL (see chat): children of a RECURSE node must be built by
# recursing FULLY at each of several sampled primes and averaging the
# resulting COSTS - not by averaging p^(x-1) once and recursing on
# that average. p^(x-1) is convex, so a density-weighted mean over a
# wide range is dominated by the top of the range (Jensen's
# inequality); averaging the multiplier first made aq blow up wildly
# on the very first real branch and collapsed the whole tree to a
# near-immediate degenerate fallback (confirmed against real D(12,9)
# batches b64/b36 - both collapsed the same way, one giving a wildly
# high answer and one wildly low - essentially arbitrary noise once
# collapsed). Sample count tapers with depth to keep this affordable
# (default schedule 7,5,3,1,1,...,1 - clamped at the last entry, so
# total evaluations stay bounded regardless of how deep the tree
# actually goes).
# ---------------------------------------------------------------------

use constant WALK_RATE => 1e7;   # candidates/sec - PLACEHOLDER, not
    # yet calibrated against real elapsed times (next step).

our $DEBUG = 0;

sub _li_diff {
    # Approximate count of primes in (a, b] via the logarithmic
    # integral li(x) ~ x/ln(x) - first-order term only.
    my($a, $b) = @_;
    return 0 if $b <= $a;
    my $li = sub { my($x) = @_; return $x <= 2 ? 0 : $x / log($x); };
    my $d = $li->($b) - $li->($a);
    return $d > 0 ? $d : 0;
}

sub _node_cost {
    my(%a) = @_;
    my($j, $positions, $aq, $k, $n_pattern_primes, $depth, $zmax, $gp, $gq,
        $max_depth, $schedule) = @a{qw(j positions aq k n_pattern_primes
        depth zmax gp gq max_depth schedule)};

    return $zmax / WALK_RATE if $depth > $max_depth;   # safety valve

    my $g = _gate_decision(j => $j, positions => $positions, aq => $aq,
        k => $k, n_excl_base => $n_pattern_primes, depth => $depth,
        zmax => $zmax, gp => $gp, gq => $gq, f => $a{f}, n => $a{n});

    if (!$g) {
        my $ret = $aq > 0 ? ($zmax / $aq) / WALK_RATE : $zmax / WALK_RATE;
        print "  " x $depth, "depth=$depth TERMINAL(no eligible vi) aq=$aq walk_items=", $ret*WALK_RATE, "\n" if $DEBUG;
        return $ret;
    }

    print "  " x $depth,
        "depth=$depth vi=$g->{vi} t=$positions->[$g->{vi}]{t} x=$g->{x}",
        " nextt=$g->{nextt} aq=$aq r_walk=$g->{r_walk} p_start=$g->{p}",
        " limp=$g->{limp} decision=$g->{decision}\n" if $DEBUG;

    if ($g->{decision} eq 'WALK') {
        return $g->{r_walk} > 0 ? $g->{r_walk} / WALK_RATE : 1 / WALK_RATE;
    }

    my $branch_count = _li_diff($g->{p}, $g->{cap});
    if ($branch_count <= 0) {
        print "  " x $depth, "  degenerate branch_count<=0, falling back to r_walk\n" if $DEBUG;
        return $g->{r_walk} / WALK_RATE;
    }

    return _recurse_cost_powerlaw(%a, g => $g, depth => $depth,
        j => $j, positions => $positions, aq => $aq, k => $k,
        n_pattern_primes => $n_pattern_primes, zmax => $zmax,
        gp => $gp, gq => $gq, max_depth => $max_depth);
}

# ---------------------------------------------------------------------
# Power-law extrapolation for a RECURSE node's total contribution.
#
# Per hvds (chat): rather than sparsely sampling the whole [p_start,
# cap] range (unstable once branch counts are large and the per-branch
# cost distribution is skewed - see the Simpson-sampling failure on
# real D(12,9) batches, now removed), compute the FULL recursive cost
# exactly at the smallest 3 real primes above p_start, fit a power law
# cost(p) = A * p^gamma to those 3 points (log-log least squares), and
# use that SMOOTH analytic form for everything above them - integrated
# numerically (cheap and stable now, since the integrand is a known
# smooth function, not the true noisy/discontinuous recursive cost).
#
# Basis for expecting a power law at all: hvds' already-validated
# finding that walk-only cost M scales EXACTLY as (p_old/p_new)^e when
# swapping one fixed prime power for another at exponent e (confirmed
# to 4 sig figs against real logs) - i.e. gamma=-e in the pure-walk
# case. Once further recursion (not just walk) happens beneath a
# choice, the hypothesis (hvds, chat) was that |gamma| should still
# lie roughly in [e/2, e] - checked directly against two real D(12,9)
# decision points using this same code (deterministic, single-path
# evaluation) before building this in: |gamma|=1.40 and |gamma|=1.83
# for e=2 (predicted range [1,2]) - both inside range, second case
# very cleanly log-log linear until hitting a floor near cost=1 (see
# next paragraph).
#
# KNOWN LIMITATION, explicitly deferred per hvds: no special handling
# for the tail (large p, where the real cost should flatten out as
# recursion options run out, rather than keep decaying as a power
# law) - the fit is extrapolated across the WHOLE remaining range
# including that tail. This likely over- or under-estimates the tail's
# true (probably small, since large p means little further work)
# contribution; not yet checked how much that matters to the total.
# ---------------------------------------------------------------------

sub _next_prime {
    my($n) = @_;
    my $cand = $n <= 2 ? 2 : int($n) + (int($n) == $n ? 1 : 0);
    $cand = 2 if $cand < 2;
    CAND: while (1) {
        my $d = 2;
        while ($d * $d <= $cand) {
            if ($cand % $d == 0) { $cand++; next CAND; }
            $d++;
        }
        return $cand;
    }
}

sub _recurse_cost_powerlaw {
    my(%a) = @_;
    my $g = $a{g};
    my($j, $positions, $aq, $k, $n_pattern_primes, $depth, $zmax, $gp, $gq,
        $max_depth) = @a{qw(j positions aq k n_pattern_primes depth zmax
        gp gq max_depth)};

    # Test primes SPREAD ACROSS THE WHOLE LOG-RANGE [p_start, cap], not
    # clustered near the bottom (an earlier version tested only the
    # smallest 3 - see git history / chat). Clustering near the bottom
    # meant the fit only ever saw the steepest part of the decay and
    # had no way to detect flattening toward the tail, which is
    # exactly the region dominating the integral once the range spans
    # many orders of magnitude - confirmed as the main remaining
    # source of error, and confirmed to compound multiplicatively with
    # recursion depth (D(12,9) b12, 3 levels deep, was under-predicted
    # ~24x; b4, 2 levels deep, was within 1%). An attempted fix using
    # one-level-lookahead ("does the immediate child's own decision
    # become WALK") to find an exact-tail cutoff analytically was
    # tried and reverted - see chat - it only catches cases where the
    # child walks immediately, not cases where the child recurses
    # further but that whole sub-branch still resolves cheaply a
    # couple of levels down, which is common in exactly the deep cases
    # this needs to fix. Log-spaced test points are a more direct fix:
    # they sample the curve's actual shape across its whole relevant
    # domain instead of trying to predict where it changes shape.
    my $lo = $g->{p} > 2 ? $g->{p} : 2;
    my $hi = $g->{cap};
    my $n_test = 4;
    my @test_p;
    if ($hi > $lo) {
        my($u_lo, $u_hi) = (log($lo), log($hi));
        my %seen;
        for my $i (0 .. $n_test - 1) {
            my $u = $u_lo + ($u_hi - $u_lo) * $i / ($n_test - 1);
            my $p = _next_prime(int(exp($u)) + 1);
            next if $p > $hi || $seen{$p}++;
            push @test_p, $p;
        }
    }
    return $g->{r_walk} / WALK_RATE unless @test_p;   # nothing to try

    my %cost_at;   # prime => cost in SECONDS
    for my $p (@test_p) {
        my $pxm1 = $p ** ($g->{x} - 1);
        my @child_positions = map { { %$_ } } @$positions;
        $child_positions[$g->{vi}]{t}     = $g->{nextt};
        $child_positions[$g->{vi}]{logq} += log($pxm1);
        $cost_at{$p} = _node_cost(
            j => $j, positions => \@child_positions, aq => $aq * $pxm1,
            k => $k, n_pattern_primes => $n_pattern_primes,
            depth => $depth + 1, zmax => $zmax, gp => $gp, gq => $gq,
            max_depth => $max_depth, f => $a{f}, n => $a{n},
        );
    }

    # exact contribution: only the SMALLEST tested prime represents a
    # genuinely isolated single prime near p_start; the others are
    # spread-out SAMPLES used to inform the fit's shape, not exact
    # per-prime contributions (there could be many other real primes
    # near each of them) - so only the smallest one's cost is added as
    # an "exact" term, matching how many actual primes it alone
    # represents at that specific point (essentially none beyond
    # itself, since it's right at the start of the range); the rest of
    # the range (including around the other test points) is covered by
    # the fitted-and-integrated remaining term below.
    my @sorted_p = sort { $a <=> $b } @test_p;
    my $exact = $cost_at{$sorted_p[0]};

    my @pts = map { [log($_), log($cost_at{$_})] }
        grep { $cost_at{$_} > 0 } @test_p;

    my($gamma, $A);
    if (@pts >= 2) {
        my($sx, $sy, $sxx, $sxy, $n) = (0, 0, 0, 0, scalar @pts);
        for (@pts) { $sx += $_->[0]; $sy += $_->[1];
            $sxx += $_->[0]**2; $sxy += $_->[0] * $_->[1]; }
        my $denom = $n * $sxx - $sx * $sx;
        if ($denom != 0) {
            $gamma = ($n * $sxy - $sx * $sy) / $denom;

            # Clamp to the theoretically-motivated range [-e, -e/2]
            # (hvds' hypothesis, checked directly against real D(12,9)
            # decision points - see module intro). Cost should NEVER
            # increase with p (matches the already-validated
            # M~(p_old/p_new)^e relationship, e>0); a positive or
            # out-of-range fit means the test points were too noisy to
            # trust unconstrained (confirmed on real b4 with the
            # earlier 3-clustered-point version: an unconstrained fit
            # produced gamma=+5.05 and an astronomical, physically-
            # impossible extrapolation).
            my $e = $g->{x} - 1;
            my($gamma_lo, $gamma_hi) = (-$e, -$e / 2);
            if ($gamma > $gamma_hi || $gamma < $gamma_lo) {
                $gamma = $gamma > $gamma_hi ? $gamma_hi : $gamma_lo;
                my $sum_resid = 0;
                $sum_resid += ($_->[1] - $gamma * $_->[0]) for @pts;
                my $intercept = $sum_resid / @pts;
                $A = exp($intercept);
            } else {
                my $intercept = ($sy - $gamma * $sx) / $n;
                $A = exp($intercept);
            }
        }
    }

    my $remaining = 0;
    if (defined $gamma && $sorted_p[0] < $g->{cap}) {
        $remaining = _integrate_power_law($A, $gamma, $sorted_p[0], $g->{cap});
    }

    print "  " x $depth, "  tested=[@test_p] costs=[",
        join(',', map { sprintf('%.3g', $cost_at{$_}) } @test_p), "]",
        (defined $gamma ? " gamma=$gamma" : " (no fit - <2 nonzero points)"),
        " exact=$exact remaining=$remaining\n" if $DEBUG;

    return $exact + $remaining;
}

# Numerically integrate A*p^gamma / ln(p) dp from lo to hi. Uses
# log-spaced points (substitution u=ln(p), so dp=p*du - integrating
# uniformly in u rather than p) - NOT linear spacing, which was a real
# bug (see chat): the integrand is sharply peaked near the lower bound
# and decays fast (gamma is typically around -e, e.g. -2), while the
# integration range can span 4+ orders of magnitude (p_start to limp).
# Linear-spaced Simpson points at that width step clean over the
# entire region with real mass, catastrophically overestimating the
# integral - confirmed on real D(12,9) b0: the fix took a ~110x
# over-prediction down to within a few percent (see chat) with no
# other change.
sub _integrate_power_law {
    my($A, $gamma, $lo, $hi, $n_pts) = @_;
    $n_pts //= 21;
    $n_pts++ if $n_pts % 2 == 0;
    return 0 if $hi <= $lo;
    $lo = 2 if $lo < 2;
    my($u_lo, $u_hi) = (log($lo), log($hi));
    my $h = ($u_hi - $u_lo) / ($n_pts - 1);
    my $sum = 0;
    for my $i (0 .. $n_pts - 1) {
        my $u = $u_lo + $h * $i;
        my $p = exp($u);
        my $w = ($i == 0 || $i == $n_pts - 1) ? 1 : ($i % 2 == 1) ? 4 : 2;
        # integrand in u: A*p^gamma/ln(p) * dp/du = A*p^gamma/ln(p) * p
        my $val = $A * ($p ** $gamma) / ($u > 0 ? $u : 0.001) * $p;
        $sum += $w * $val;
    }
    return $sum * $h / 3;
}

# ---------------------------------------------------------------------
# estimate_batch_cost(%opt): top-level entry point.
# %opt: n, k, f, j (0 or 2 only), pattern, zmax, gp, gq.
# Returns estimated elapsed seconds (WALK_RATE-scaled placeholder).
# ---------------------------------------------------------------------

sub estimate_batch_cost {
    my(%opt) = @_;
    my($n, $k, $f, $j, $pattern, $zmax, $gp, $gq) = @opt{
        qw(n k f j pattern zmax gp gq)};

    my($positions, $aq, $n_pattern_primes, $sq_tag)
        = _build_positions_and_aq($n, $k, $pattern);

    # [sq=N]-tagged batches (N>=1): have_square is set from the very
    # first decision (a position in the FORCED pattern is already a
    # complete perfect square - not the "discovered mid-recursion, odd
    # remaining tau" case _gate_decision detects, which only fires
    # once a position's remaining tau becomes odd; a COMPLETE square
    # position has remaining tau exactly 1, so that check never
    # catches this). have_square only ever increases through a
    # recursion, never resets, so the same crude terminal-WALK
    # fallback applies for the WHOLE tree here, not just one node -
    # short-circuit directly rather than entering the general
    # machinery just to hit the same fallback immediately anyway.
    # Confirmed on real D(12,7) b6 (also [sq=1]): pcoul itself
    # resolves these via a SINGLE immediate walk in reality too (one
    # GATE line, decision=WALK) - so this crude fallback may actually
    # be a fairly good match for this case specifically, unlike the
    # mid-recursion-discovered case, which is unvalidated. NOT YET
    # checked against real D(18,4) data (every batch is [sq=1] there)
    # - see chat, this work was paused before that validation ran.
    if (defined $sq_tag) {
        my $r_walk = int($zmax / $aq);
        $r_walk = int(($r_walk * $gp) / $gq);
        return $r_walk > 0 ? $r_walk / WALK_RATE : 1 / WALK_RATE;
    }

    return _node_cost(j => $j, positions => $positions, aq => $aq,
        k => $k, n_pattern_primes => $n_pattern_primes, depth => 0,
        zmax => $zmax, gp => $gp, gq => $gq, max_depth => 40,
        f => $f, n => $n);
}

1;
