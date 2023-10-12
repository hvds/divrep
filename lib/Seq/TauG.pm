package Seq::TauG;
use strict;
use warnings;
use List::Util qw{ max sum };
use Math::GMP;
use Math::Prime::Util qw{ is_prime factor_exp };
use Memoize;

my $zero = Math::GMP->new('0');

=head1 NAME

Seq::TauG

=head1 DESCRIPTION

C<g(n)> is defined as the largest C<k> such that C<f(n, k)> exists.
Knowledge of this function is recorded in the database table C<taug>
described by the embedded C<Seq::TauG::Schema> class; results from
this table will generate objects of this class.

For a given C<n>, C<ming> is the minimum we know C<g(n)> can be. For
C<< ming > 1 >>, this is validated by the existence of an associated
L<Seq::TauF> entry for C<f(n, ming)> (though that entry is not required
to be minimal).

For a given C<n>, C<maxg> is the maximum we know C<g(n)> can be. For
C<< maxg < n >>, this is validated by the existence of one or more
associated L<Seq::Run> entries that in aggregate show no solution
for C<f(n, maxg + 1)> is possible - typically a single invocation
that terminates with C<402 Error: all values %s disallowed>.

For a given C<n>, the C<status> flag C<complete> is set to C<TRUE>
to imply that a) C<ming == maxg>, b) there are associated L<Seq::TauF>
entries for each of C<f(n, 2) .. f(n, maxg)> that are proven minimal.

For a given C<n>, the C<status> flag C<superset> is set to C<TRUE>
when C<n.ming = 1 + {n+1}.ming>, with both C<n> and C<n+1> not C<complete>,
and the C<status> flag C<subset> is set for C<n+1> in the same case.
The run harness does not run those C<n> that are marked as C<superset>,
and C<bad()> on a C<subset> propagates the new C<checked> value to its
C<superset(s)>.

For a given C<n>, C<priority> is used as an input to determine priority
of associated L<Seq::TauF> entries; by default it starts off as
C< -log_2(n) >, but is then lowered when we find results unreasonably
hard to find.

=cut

use parent 'Seq::Table';
my($TABLE, $taug) = ('TauG', __PACKAGE__);
$taug->define($TABLE, 'taug', [
    'key uint n',
    'uint ming',
    'uint maxg',
    'bigint checked',
    'maybe uint depend_n',
    'maybe uint bisected',
    'maybe float bisect_time',
    'flags(complete depend prime superset subset) status',
]);
$taug->has_many(f => 'Seq::TauF', 'n', { order_by => 'k' });
$taug->might_have(depended => 'Seq::TauG', { 'foreign.n' => 'self.depend_n' });

sub rprio {
    my($self, $type) = @_;
    return $type->gprio($self->n);
}

sub max_known {
    my($class, $db) = @_;
    # Note, we start with n=2
    return $db->resultset($TABLE)->get_column('n')->max
            || ($db->type->smallest - 1);
}

# Return a list of taug entries for harness to process, within the
# given range.
sub range {
    my($class, $db, $start, $end) = @_;
    return $db->resultset($TABLE)->search({
        n => {
            '>=' => $start,
            '<=' => $end,
        },
    })->search_bitfield({
        complete => 0,
        superset => 0,
    })->all;
}

sub genTo {
    my($class, $db, $req) = @_;
    my $max = $class->max_known($db);
    $class->generate($db, $req - $max) if $req > $max;
    return;
}

sub generate {
    my($class, $db, $count) = @_;
    my $max = $class->max_known($db);
    my $table = $db->resultset($TABLE);
    my $type = $db->type;
    for my $n ($max + 1 .. $max + $count) {
        my $self = $table->new({
            n => $n,
            ming => $type->ming($n),
            maxg => $type->maxg($n),
            status => (is_prime($n) ? [ 'prime' ] : 0),
            checked => $zero,
        });
        $self->complete(1) if $self->ming == $self->maxg;
        $self->insert;
    }
}

sub good {
    my($self, $db, $ming, $checked) = @_;
    $self->checked($checked) if $checked > $self->checked;
    if ($self->subset) {
        my $gp = $self->predecessor($db);
        # propagate recursively, but ignore any return objects
        $gp->bad($db, $checked - 2) if $gp && !$gp->complete
                && $gp->superset && $gp->ming == $self->ming + 1;
    }
    $self->ming($ming) if $ming > $self->ming;
    return $self->final($db);
}

sub partial {
    my($self, $db, $ming) = @_;
    # FIXME: capture the distinction between 'f(n,k) exists' and
    # 'f(n.k) known minimal' - either have two separate ming fields
    # or mark complete only when ming == maxg _and_ f[k=maxg].complete
    return ();
}

sub bad {
    my($self, $db, $checked) = @_;
    $self->checked($checked) if $checked > $self->checked;
    if ($self->subset) {
        my $gp = $self->predecessor($db);
        # propagate recursively, but ignore any return objects
        $gp->bad($db, $checked - 1) if $gp && !$gp->complete
                && $gp->superset && $gp->ming == $self->ming + 1;
    }
    return $self->final($db);
}

sub ugly {
    my($self, $db, $maxg) = @_;
    $self->maxg($maxg - 1) if $maxg - 1 < $self->maxg;
    return $self->final($db);
}

sub bisect {
    my($self, $db, $maxg, $bisected, $btime) = @_;
    return () if ($self->bisected // 0) > $bisected;
    my $old_maxg = $self->maxg;
    if ($maxg < $old_maxg) {
        $self->maxg($maxg);
        printf "g(%s) <= %s  [bisect %s]\n",
                $self->n, $maxg, $bisected;
    }
    $self->bisected($bisected);
    $self->bisect_time($btime);
    return $self->final($db);
}

sub depends {
    my($self, $db, $ming, $depend_n) = @_;
    $self->ming($ming) if $ming > $self->ming;
    $self->depend(1);
    $self->depend_n($depend_n);
    my $d = $db->resultset($TABLE)->find({ n => $depend_n });
    $self->maxg($d->maxg) if $d->maxg < $self->maxg;
    Seq::TauF->update_depends($db, $self);
    return $self->final($db);
}

sub update_depends {
    my($self, $db) = @_;
    my $dep = $db->resultset($TABLE)->find({ n => $self->depend_n });
    Seq::TauF->update_depends($db, $self);
    $self->ming($dep->ming) if $dep->ming > $self->ming;
    $self->maxg($dep->maxg) if $dep->maxg < $self->maxg;
    $self->complete(1) if $dep->complete;
    $self->update;
    return;
}

sub final {
    my($self, $db) = @_;
    if ($self->ming == $self->maxg) {
        $self->complete(1);
        printf "g(%s) = %s\n", $self->n, $self->maxg;
    }
    $self->update;
    for ($self->f->search({ k => { '>', $self->maxg } })
            ->search_bitfield({ 'complete' => 0 })) {
        # cannot delete, since there may already be runs
        $_->complete(1);
        $_->impossible(1);
        $_->update;
    }
    my @extra;
    my($gp, $gs) = ($self->predecessor($db), $self->successor($db));
    $self->propagate_set($gs);
    push @extra, $gp if $gp && $gp->propagate_set($self);
    return map +($_->complete ? () : $_->fnext($db)), ($self, @extra);
}

# update subset/superset flags on a predecessor/successor pair; returns
# C<TRUE> if the predecessor is newly runnable.
sub propagate_set {
    my($gp, $gs, $db) = @_;
    return 0 unless $gs;
    if ($gs->complete || $gp->complete || $gp->ming <= $gs->ming) {
        if ($gs->subset) {
            $gs->subset(0);
            $gs->update;
        }
        if ($gp->superset) {
            $gp->superset(0);
            $gp->update;
            return 1;
        }
    } else {
        if (!$gs->subset) {
            $gs->subset(1);
            $gs->update;
        }
        if (!$gp->superset) {
            $gp->superset(1);
            $gp->update;
        }
    }
    return 0;
}

sub prep {
    my($self, $db) = @_;
    return () if $self->complete || $self->superset;
    return $self->fnext($db);
}

sub runnable { return () }

sub predecessor {
    my($self, $db) = @_;
    return $db->resultset('TauG')->find({ n => $self->n - 1 });
}

sub successor {
    my($self, $db) = @_;
    return $db->resultset('TauG')->find({ n => $self->n + 1 });
}

sub fnext {
    my($self, $db) = @_;
    return () if $self->complete;
    return Seq::TauF->nextFor($self, $db);
}

sub fall {
    my($self, $db) = @_;
    return Seq::TauF->allFor($self, $db);
}

1;
