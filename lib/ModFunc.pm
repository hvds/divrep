package ModFunc;
use strict;

use Math::GMP ();
use List::Util qw{ reduce };

require Exporter;
our @ISA = qw{ Exporter };
our @EXPORT_OK = qw{
    quadvec gcd
};

{
    my %q;

    #
    # Returns an m-bit vector, such that bit i is true iff is_residue(i, m).
    #
    sub quadvec {
        my($m) = @_;
        ${ $q{$m} ||= do {
            my $v = "";
            vec($v, (($_ * $_) % $m), 1) = 1 for 0 .. $m - 1;
            \$v;
        } };
    }
}

sub gcd {
    my $n0 = shift;
    $n0 = Math::GMP->new($n0) unless ref $n0;
    return reduce { $a->bgcd($b) } ($n0, @_);
}

1;
