#!/usr/bin/perl
# Parse the -DVERBOSE trace from pcoul (coultau.c's dz()/ct_*() diagnostic
# output) into a per-candidate, per-stage cost TSV, for feeding the
# walk_v() factorization-cost model (see walk-cost-model-intro.md).
#
# Usage:
#   ./pcoul.verbose -f<N> -b<batch> -x<min>:<max> <n> <k> 2>&1 \
#       | perl parse_verbose_cost.pl > out.tsv
#
# Requires the local coultau.c patch that adds:
#   - vi=... to the tau_multi_prep header line
#   - a tau_prime_prep header line (vi=... n)
#   - ct_pretest/ct_bpsw wrappers so the prime-only path is also logged
#
# Output columns (one row per stage-attempt, not one row per candidate -
# aggregate by `id` downstream to get total per-candidate cost):
#   id      sequential candidate id (unique per prep record opened)
#   path    prime | multi
#   vi      position index (from the header line)
#   t       target tau (2 for prime path)
#   e       exponent-so-far at header time (multi path only; 1 for prime)
#   bits    bit-length of the value at header time
#   stage   pretest | bpsw | prep | b63 | p-1 | tqs | ecm | sqf | sqs | hlf
#           | p | pow  (prep = the free trial-division stage, folded to a
#           single synthetic row per candidate since dz() emits several
#           unlabelled div: lines with no per-call boundary worth keeping)
#   ns      elapsed ns charged to this stage (see NOTE on attribution below)
#   outcome 1 (resolved/found) | 0 (ruled out / no factor) | ? (unknown -
#           true for most 'prep' rows, since dz()'s own text doesn't
#           always say whether the record then resolved immediately or
#           fell through to escalation - see caveats)
#   attrib  exact | approx - see NOTE below
#
# NOTE on escalation-phase attribution:
# tau_multi_run() interleaves ladder attempts (b63/p-1/tqs/ecm/...) across
# ALL need_other positions for one 'ati' pending after prep, in rung order
# - not grouped per-candidate. The log carries the exact residual value
# tm->n on every escalation line, but not an explicit "prep concluded,
# residual=R" line. This script therefore matches escalation lines back
# to the record whose LAST KNOWN value equals the printed value:
#   - if a candidate's own prep phase found zero factors (no p:/pow: lines
#     during prep), its known value is still the original header value,
#     so the FIRST escalation line naming that exact value is an EXACT
#     match. This covers the common and most important case: candidates
#     that survive trial division untouched are exactly the "hard,
#     actually expensive" ones we most want good data on.
#   - if prep DID reduce the value (a p:/pow: call fired during prep),
#     the residual is only known once that call's own line is seen. If
#     ambiguity remains (two+ pending candidates whose known value
#     doesn't match the escalation line, most often because their
#     genuinely-reduced residual was never independently observed),
#     the line is attributed to the oldest still-open unresolved record
#     on a FIFO basis and marked attrib=approx. Filter these out
#     downstream if you want an attribution-clean dataset.

use strict;
use warnings;

my $next_id = 1;
my @open;       # records not yet known to be fully closed (multi path,
                # awaiting either prep-resolution or escalation)
my @pending_prime;  # prime-path records awaiting a bpsw: line, keyed by value

# emit one TSV row
sub emit {
    my ($id, $path, $vi, $t, $e, $bits, $stage, $ns, $outcome, $attrib) = @_;
    $_ //= '' for $id, $path, $vi, $t, $e, $bits, $stage, $ns, $outcome, $attrib;
    print join("\t", $id, $path, $vi, $t, $e, $bits, $stage, $ns, $outcome, $attrib), "\n";
}

print join("\t", qw(id path vi t e bits stage ns outcome attrib)), "\n";

# "active" record currently absorbing raw prep-internal div:/p:/pow: lines
# (valid because prep calls are strictly serial - see script header note)
my $active;       # hashref or undef
my $active_prep_ns = 0;   # accumulated ns for the active record's own prep

sub close_active_prep {
    return unless $active;
    if ($active_prep_ns > 0 || $active->{saw_prep_line}) {
        emit($active->{id}, $active->{path}, $active->{vi}, $active->{t},
             $active->{e}, $active->{bits}, 'prep', $active_prep_ns, '?', 'exact');
    }
    $active_prep_ns = 0;
}

while (my $line = <STDIN>) {
    chomp $line;

    if ($line =~ /^tau_prime_prep vi=(\d+) (\d+)$/) {
        close_active_prep();
        my $rec = { id => $next_id++, path => 'prime', vi => $1, t => 2, e => 1,
                    bits => undef, value => $2, resolved => 0 };
        $active = $rec;
        $active_prep_ns = 0;
        next;
    }
    if ($line =~ /^tau_multi_prep vi=(\d+) t=(\d+) e=(\d+) \((\d+)\) (\d+)$/) {
        close_active_prep();
        my $rec = { id => $next_id++, path => 'multi', vi => $1, t => $2, e => $3,
                    bits => $4, value => $5, resolved => 0, reduced => 0 };
        push @open, $rec;
        $active = $rec;
        $active_prep_ns = 0;
        next;
    }

    # prep-internal trial-division messages (dz()); no per-call boundary,
    # just fold into the active record's prep-stage total. Format varies
    # (several distinct messages from tau_multi_prep) but all start "(ns) div:".
    if ($line =~ /^\((\d+)\) div: /) {
        if ($active) {
            $active_prep_ns += $1;
            $active->{saw_prep_line} = 1;
        }
        next;
    }

    # ct_prime "p:" - can fire during prep (multi path) or after an
    # escalation-ladder factor is confirmed prime via tm_factor().
    if ($line =~ /^\((\d+)\) p: (\d+) (\d+)$/) {
        my ($ns, $val, $ok) = ($1, $2, $3);
        if ($active && !$active->{resolved}) {
            # flush accumulated trial-division time as its own row FIRST,
            # then the decisive call as a separate row - do not add ns
            # into $active_prep_ns (that would double it up once
            # close_active_prep() also fires for this same record later).
            if ($active_prep_ns > 0 || $active->{saw_prep_line}) {
                emit($active->{id}, $active->{path}, $active->{vi}, $active->{t},
                     $active->{e}, $active->{bits}, 'prep', $active_prep_ns, '?', 'exact');
            }
            $active_prep_ns = 0;
            $active->{saw_prep_line} = 0;
            $active->{value} = $val;
            $active->{reduced} = 1;
            emit($active->{id}, $active->{path}, $active->{vi}, $active->{t},
                 $active->{e}, $active->{bits}, 'p', $ns, $ok, 'exact');
            $active->{resolved} = 1;
        } else {
            attribute_escalation_line($val, 'p', $ns, $ok);
        }
        next;
    }
    if ($line =~ /^\((\d+)\) pow: (\d+)\^(\d+)$/) {
        my ($ns, $val, $pw) = ($1, $2, $3);
        if ($active && !$active->{resolved}) {
            # pow: is informational, not decisive (prep continues after it,
            # possibly reaching a real resolution or falling through to
            # escalation) - just accumulate its ns like a div: line, don't
            # flush or mark resolved.
            $active_prep_ns += $ns;
            $active->{saw_prep_line} = 1;
            $active->{value} = $val;
            $active->{reduced} = 1;
        } else {
            attribute_escalation_line($val, 'pow', $ns, $pw ? 1 : 0);
        }
        next;
    }

    if ($line =~ /^\((\d+)\) pretest: (\d+) (-?\d+)$/) {
        my ($ns, $val, $res) = ($1, $2, $3);
        if ($active && $active->{path} eq 'prime') {
            emit($active->{id}, 'prime', $active->{vi}, 2, 1, undef,
                 'pretest', $ns, $res, 'exact');
            if ($res eq '1') {
                # needs bpsw later, batched; keep it findable by value
                push @pending_prime, $active;
            }
            $active->{resolved} = 1;
        }
        next;
    }
    if ($line =~ /^\((\d+)\) bpsw: (\d+) (\d+)$/) {
        my ($ns, $val, $ok) = ($1, $2, $3);
        my $rec;
        for my $i (0 .. $#pending_prime) {
            if ($pending_prime[$i]{value} eq $val) {
                $rec = splice(@pending_prime, $i, 1);
                last;
            }
        }
        if ($rec) {
            emit($rec->{id}, 'prime', $rec->{vi}, 2, 1, undef, 'bpsw', $ns, $ok, 'exact');
        } else {
            # shouldn't happen given pretest doesn't mutate n, but don't lose data
            emit('?', 'prime', '?', 2, 1, undef, 'bpsw', $ns, $ok, 'approx');
        }
        next;
    }

    # escalation-ladder lines: "(ns) <label>: n [params...] flag [factor]"
    if ($line =~ /^\((\d+)\) (b63|p-1|tqs|ecm|sqf|sqs|hlf): (\d+) \[[^\]]*\] (\d+)/) {
        my ($ns, $label, $val, $ok) = ($1, $2, $3, $4);
        attribute_escalation_line($val, $label, $ns, $ok);
        next;
    }
    # simpqs ("sqs:") uses a bare int flag with no brackets - already covered
    # by the pattern above (no [..] in its format string), handle separately:
    if ($line =~ /^\((\d+)\) sqs: (\d+) (-?\d+)/) {
        my ($ns, $val, $ok) = ($1, $2, $3);
        attribute_escalation_line($val, 'sqs', $ns, $ok > 0 ? 1 : 0);
        next;
    }
}
close_active_prep();

# Attribute an escalation-phase line to whichever open 'multi' record's
# currently-known value matches; fall back to FIFO + attrib=approx.
sub attribute_escalation_line {
    my ($val, $stage, $ns, $ok) = @_;
    my $rec;
    for my $r (@open) {
        next if $r->{resolved};
        if ($r->{value} eq $val) { $rec = $r; last; }
    }
    my $attrib = 'exact';
    if (!$rec) {
        ($rec) = grep { !$_->{resolved} } @open;
        $attrib = 'approx';
    }
    if ($rec) {
        emit($rec->{id}, $rec->{path}, $rec->{vi}, $rec->{t}, $rec->{e},
             $rec->{bits}, $stage, $ns, $ok, $attrib);
        $rec->{value} = $val;  # in case a factor was divided out and it continues
        if ($stage ne 'p' && $stage ne 'pow' && $ok) {
            # a full factor-finding method succeeding may or may not fully
            # resolve tau - conservatively leave 'resolved' unset unless a
            # decisive p:/pow: line follows; @open is pruned at EOF anyway.
        }
    } else {
        emit('?', '?', '?', '?', '?', '?', $stage, $ns, $ok, 'approx');
    }
}
