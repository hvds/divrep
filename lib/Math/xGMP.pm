use strict;
use warnings;
use Math::GMP;

my $LONG = 300;

package Math::GMP {
    sub log10 {
        my($z) = @_;
        my $s = "$z";
        my $len = length($s);
        return log($s) / log(10) if $len < $LONG;
        $s =~ s/^(.)/$1./;
        return log($s) / log(10) + $len - 1;
    }
    sub log {
        my($z) = @_;
        return log10($z) * log(10);
    }
    sub bfdiv {
        my($a, $b) = @_;
        my $sa = "$a";
        return $sa / "$b" if length($sa) < $LONG;
        my $lb = ref($b) ? $b->log : CORE::log($b);
        return exp($a->log - $lb);
    }
}

1;
