package Git;
use strict;
use warnings;

=head1 NAME

Git data support

=head1 DESCRIPTION

We track two repositories: our own (divrep), and that for Math-Prime-Util-GMP
(mpu). Executables report the state of the code they were built from using
a semicolon-separated string representing the two repos, where each fragment
is of the form "A(B)*", in which A is the SHA of the last committed change
affecting any of the program's dependencies, B is the SHA of the last common
commit between A and the master branch (skipped if A is in master), and the
asterisk is present if any dependency had uncommitted changes.

Additionally, we attempt to give an indication of the more complicated state
of a logfile with distinct states across recoveries. In this case, each
fragment may additionally be annotated with '%<n>' to indicate the number
of distinct states for that fragment, optionally followed by another asterisk
if any of those additional states was not "pure".

We define a string as "pure" if a) it is not marked dirty, and b) either
A is in master (for each repository) or it has been whitelisted.

For C programs, the component parts of the string are made available
by use of 'git-data' in the Makefile, which provides the values:
  DIVREP_CHANGE DIVREP_BASE DIVREP_DIRTY
  MPU_CHANGE MPU_BASE MPU_DIRTY

=head1 CLASS METHODS

=over 4

=item new ( string )

Returns a new instance representing the git state data encapsulated by
the supplied string. A (possibly empty) semicolon-separated list of empty
strings is permitted, but it is a fatal error if a non-empty fragment
cannot be parsed.

The state data may have additional annotations as added by C<composite()>.

=item new_if_valid ( string )

Same as C<new()>, but the fatal error is downgraded to a warning with
a return value of C<undef>.

=item composite ( arrayref )

Given an arrayref of strings representing valid git state data (or an
empty string), returns a best-effort string representing the combination
of them.

=back

=head1 INSTANCE METHODS

=over 4

=item is_pure ( )

Returns C<TRUE> if the state data represents a pure state, per the
definition in the C<DESCRIPTION> section. A composite state is pure
only if all its constituent states are pure.

=cut

my %whitelist = (
    divrep => { map +($_ => 1), (
    ) },
    mpu => { map +($_ => 1), (
        'b363d69',  # hvds fork, simpqs-full branch
    ) },
);

my @repo = (qw{ divrep mpu });
my %repo_idx = map +($repo[$_] => $_), 0 .. $#repo;

sub new {
    my($class, $str) = @_;
    $str //= '';
    my @part = split /;/, $str;
    die "malformed git status string '$str'"
            unless $str eq '' || @part == @repo;
    return bless {
        raw => $str,
        data => [ map _derive($repo[$_], $part[$_]), 0 .. $#repo ],
    }, $class;
}

sub new_if_valid {
    my($class, $str) = @_;
    if (my $self = eval { $class->new($str) }) {
        return $self;
    } else {
        warn $@;
        return $class->new('');
    }
}

# Returns a best-effort composite string representing multiple distinct
# git states over the lifetime of a log.
sub composite {
    my($class, $strs) = @_;
    return $strs->[0] if @$strs < 2;
    my %all;
    for (@$strs) {
        my @part = split ';';
        for (0 .. $#repo) {
            $all{ $repo[$_] }{ $part[$_] // '' } = 1;
        }
    }
    my @part = split ';', $strs->[0];
    for (0 .. $#repo) {
        my $repo = $repo[$_];
        my $seen = $all{$repo};
        $part[$_] //= '';
        delete $seen->{ $part[$_] };
        my $count = keys %$seen;
        my $dirty = grep !_raw_pure_part($repo, _derive($repo, $_)),
                keys %$seen;
        $part[$_] = sprintf '%s%s%s', $part[$_],
                ($count ? "\%$count" : ''), ($dirty ? '*' : '');
    }
    return join ';', @part;
}

sub _derive {
    my($repo, $str) = @_;
    return [ '', '', 1, 0, 0 ] unless defined $str && length $str;
    $str =~ m{
        ^ (?: ([0-9a-f]{7,32}) (?: \( ([0-9a-f]{7,32}) \) )? )? (\*?)
        (?: % (\d+) (\*?) )? $
    }x or die "malformed git status component for '$repo': '$str'";
    return [ $1 // '', $2 // $1 // '', ($3 ? 1 : 0), $4 // 0, ($5 ? 1 : 0) ];
}

sub _raw_pure_part {
    my($repo, $data) = @_;
    my($change, $base, $dirty, $count, $dirtier) = @$data;
    return 0 if $dirty || $dirtier;
    return 1 if $whitelist{$repo}{$change} || $change eq $base;
    return 0;
}

sub is_pure_part {
    my($self, $repo) = @_;
    return _raw_pure_part($repo, $self->{data}[ $repo_idx{$repo} ]);
}

sub is_pure {
    my($self) = @_;
    for my $repo (@repo) {
        return 0 unless $self->is_pure_part($repo);
    }
    return 1;
}

1;
