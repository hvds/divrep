package Seq::Run::BisectG;
use strict;
use warnings;

=head1 NAME

Seq::Run::BisectG

=head1 DESCRIPTION

Use bisect-g to update Seq::TauG->maxg.

=cut

sub new {
    my($class, $type, $g, $f, $c, $opts) = @_;
    return bless {
        type => $type,
        g => $g,
        f => $f,
        c => $c,
        opts => $opts // [],
    }, $class;
}

sub type { shift->{type} }
sub g { shift->{g} }
sub n { shift->g->n }
sub f { shift->{f} }
sub c { shift->{c} }
sub opts { shift->{opts} }

sub logpath {
    my($self) = @_;
    return sprintf '%s/rbg%s-%s',
            $self->type->logpath, $self->n, $self->c;
}

sub rprio {
    my($self, $type) = @_;
    return $type->gprio($self->n) + 1;
}

sub prep { () }

sub runnable {
    my($self, $db) = @_;
    return () if $self->g->complete
            || $self->g->prime
            || $self->g->depend;
    return $self;
}

sub command {
    my($self) = @_;
    my $g = $self->g;
    return [
        @{ $self->opts }, $g->n, $g->ming, $g->maxg, $g->checked, $self->c,
    ];
}

sub run {
    my($self, $db) = @_;
    my $cmd = $self->command;
    my $named = sprintf 'bg(%s,%s)', $self->n, $self->c;
    my $log = $self->logpath;
    return $self->type->invoke('bisect_g', $named, $cmd, $log);
}

sub failed {
    my($self, $warning) = @_;
    warn $warning;
    return ();
}

sub finalize {
    my($self, $db) = @_;
    my $log = $self->logpath;
    my $fh;
    open($fh, '<', $log)
            or return $self->failed("Can't open $log for reading: $!");
    my %line;
    while (<$fh>) {
        chomp;
        my($rc) = /^(\d{3}) /
                or return $self->failed("Can't parse log line '$_'");
        push @{ $line{$rc} }, $_;
    }
    my($maxg, $btime);
    for (@{ $line{200} // [] }) {
        (my($n), $maxg, $btime) = m{
            ^ 200 \s+ g\( (\d+) \) \s+ <= \s+ (\d+)
            \s+ \( ([\d\.]+) s\) \z
        }x or return $self->failed("Can't parse 200 line '$_'");
        $n == $self->g->n or return $self->failed("n mismatch in '$_'");
    }
    if ($maxg) {
        $self->g->bisect($db, $maxg, $self->c, $btime);
        return ();
    }
    my $fail = join "\n", map @{ $line{$_} }, grep /^5/, keys %line;
    return $self->failed("bisect failed: " . ($fail // 'unknown cause'));
}

1;
