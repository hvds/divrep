#!/usr/bin/perl
use strict;
use warnings;
use FindBin;
use lib "$FindBin::Bin";
use Calibrate;
use Calibrate::Search;

my $PCOUL = "$FindBin::Bin/mock-pcoul.pl";
# mock-pcoul.pl is a perl script without a usable shebang in this
# sandbox (noexec mount) - wrap it so build_cmd's argv[0] is actually
# runnable via exec().
my $PCOUL_WRAPPER = "/tmp/pcoul-wrapper.sh";
open my $wfh, '>', $PCOUL_WRAPPER or die $!;
print $wfh "#!/bin/sh\nexec perl '$PCOUL' \"\$\@\"\n";
close $wfh;
chmod 0755, $PCOUL_WRAPPER;

my %common = (n => 12, k => 7, f => 5, xmax => '1000', pcoul => $PCOUL_WRAPPER, jobs => 4);

print "=== batch listing ===\n";
my $bl = Calibrate::list_batches(%common, logfile => undef);
printf "batches=%d square=%d\n", scalar(@{$bl->{batches}}), $bl->{n_square};
die "expected 6 batches, 2 square\n" unless @{$bl->{batches}} == 6 && $bl->{n_square} == 2;
print "OK\n\n";

print "=== gain search per strategy (avoiding the injected solution case) ===\n";
# optimal_g_for_j in the mock: 0=>5.5, 1=>12.25, 2=>3.75, 3=>20, 4=>8.5
# Search j=0,1,3,4 first (no solution trap), then handle j=2 separately.
for my $j (0, 1, 3, 4) {
    my $result = Calibrate::Search::search_gain(
        %common, j => $j, batches => $bl->{batches},
        gain_lo => 1, gain_hi => 40,
        n_coarse => 7, budget_schedule => [3, 10, 40],
        refine_iters => 14, max_den_coarse => 60,
    );
    if ($Calibrate::Search::ABORT) {
        print "j=$j: unexpected ABORT: $Calibrate::Search::ABORT->{v}\n";
        next;
    }
    my ($p, $q) = @{ $result->{best} };
    printf "j=%d best_g=%d/%d (%.4f) total=%.3f all_resolved=%s\n",
        $j, $p, $q, $p/$q, $result->{total}, $result->{all_resolved} ? 'yes' : 'no';
}

print "\n=== j=2 (contains the injected solution trap at batch 0, g near 3.75) ===\n";
my $result2 = Calibrate::Search::search_gain(
    %common, j => 2, batches => $bl->{batches},
    gain_lo => 1, gain_hi => 40,
    n_coarse => 7, budget_schedule => [3, 10, 40],
    refine_iters => 14, max_den_coarse => 60,
);
if ($Calibrate::Search::ABORT) {
    my $a = $Calibrate::Search::ABORT;
    printf "ABORT as expected: solution v=%s found at batch=%s g=%s/%s (n=%s k=%s f=%s j=%s)\n",
        $a->{v}, $a->{batch}, $a->{gp}, $a->{gq}, $a->{n}, $a->{k}, $a->{f}, $a->{j};
} else {
    print "did NOT abort - unexpected given the injected solution trap\n";
    my ($p, $q) = @{ $result2->{best} };
    printf "best_g=%d/%d total=%.3f\n", $p, $q, $result2->{total};
}
