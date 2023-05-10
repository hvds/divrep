package Seq::Run::ShardTest;
use strict;
use warnings;

=head1 NAME

Seq::Run::ShardTest

=head1 DESCRIPTION

Use shard-test to update Seq::TauF->optm with disallowed moduli.

=cut

sub new {
    my($class, $type, $g, $f, $c, $m, $opts) = @_;
    return bless {
        type => $type,
        g => $g,
        f => $f,
        c => $c,
        m => $m,
        opts => $opts // [],
    }, $class;
}

sub type { shift->{type} }
sub g { shift->{g} }
sub n { shift->g->n }
sub f { shift->{f} }
sub k { shift->f->k }
sub c { shift->{c} }
sub m { shift->{m} }
sub opts { shift->{opts} }

sub logpath {
    my($self) = @_;
    return sprintf '%s/rst%s.%s-%s',
            $self->type->logpath, $self->n, $self->k, $self->m;
}

sub rprio {
    my($self, $type) = @_;
    return $type->gprio($self->n) + 100;
}

sub desc {
    my($self) = @_;
    return sprintf "st(%s,%s) -m%s", $self->n, $self->k, $self->m;
}

sub prep { () }

sub runnable {
    my($self, $db) = @_;
    return () if $self->g->complete
            || $self->g->depend;
    return $self;
}

sub command {
    my($self) = @_;
    my $g = $self->g;
    return [
        @{ $self->opts }, $g->n, $self->k, $self->m, $g->checked, $self->c,
    ];
}

sub run {
    my($self, $db) = @_;
    my $cmd = $self->command;
    my $named = sprintf 'st(%s,%s,%s)', $self->n, $self->k, $self->m;
    my $log = $self->logpath;
    return $self->type->invoke('shard_test', $named, $cmd, $log);
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
    my($mods, $btime);
    for (@{ $line{200} // [] }) {
        (my($n, $k), $mods, $btime) = m{
            ^ 200 \s+ f\( (\d+), \s* (\d+) \) \s+ has \s+ \[ (.*?) \]
            \s+ \( ([\d\.]+) s\) \z
        }x or return $self->failed("Can't parse 200 line '$_'");
        $n == $self->n or return $self->failed("n mismatch in '$_'");
        $k == $self->k or return $self->failed("n mismatch in '$_'");
    }
    if (defined $mods) {
        $self->f->shard_test($db, $self->m, [split /\s+/, $mods]);
        return $self->g->final($db);
    }
    my $fail = join "\n", map @{ $line{$_} }, grep /^5/, keys %line;
    my $n = $self->n;
    return $self->failed("@{[ $self->desc ]} failed: "
            . ($fail || 'unknown cause'));
}

1;
