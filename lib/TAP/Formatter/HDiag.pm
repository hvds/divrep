package TAP::Formatter::HDiag;
use strict;
use warnings;

use parent qw{TAP::Formatter::Console};

=head1 NAME

TAP::Formatter::HDiag - console TAP formatter with H::Diag progress

=head1 SYNOPSIS

  prove -Ilib -m --formatter TAP::Formatter::HDiag t/t10init t/t20log

=head1 DESCRIPTION

A formatter for C<prove> intended for running the testsuite on a console.

While a test file runs, a single progress line shows the test file, the
number of the latest test and its description, updated in place via
L<H::Diag>.

Any other output from the test file (comments, and with C<-m> also
anything written to stderr) is shown as it arrives: the progress line
is first kept with C<keep_diag()>, so it gives context for that output.

A failing test replaces the progress line with the C<not ok> line,
followed by all output up to the next test line, which is how
C<Test::More> reports the failure.

A TODO test that fails (or unexpectedly passes) replaces the progress
line with its C<not ok> (or C<ok>) line, and any output following it up
to the next test line is suppressed.

Use with C<-m> (merge), otherwise the harness copies the test's stderr
straight to the terminal and the formatter never sees it.

If stdout is not a terminal (or C<HARNESS_NOTTY> is set), the same
output is shown but without the updating progress line: the latest
progress is printed only when it is kept as context for other output.

Under C<-v>, or when running tests in parallel, this falls back to the
normal console formatter; note that in parallel, that formatter does not
show merged stderr.

=cut

sub open_test {
    my($self, $test, $parser) = @_;
    return $self->SUPER::open_test($test, $parser)
        if $self->jobs > 1 || $self->verbose;

    # progress lines are printed directly to STDOUT by H::Diag
    $self->stdout->autoflush(1);
    STDOUT->autoflush(1);
    my $session = TAP::Formatter::HDiag::Session->new({
        name => $test,
        formatter => $self,
        parser => $parser,
        show_count => 0,
    });
    $session->{tty} = -t $self->stdout && !$ENV{HARNESS_NOTTY};
    $session->header;
    return $session;
}

package TAP::Formatter::HDiag::Session;
use strict;
use warnings;

use parent qw{TAP::Formatter::Session};
use H::Diag qw{ diag keep_diag };

# On a terminal, update or keep the progress line via H::Diag. Otherwise
# just remember the latest progress, and print it only when kept.
sub _diag {
    my($self, $s) = @_;
    if ($self->{tty}) {
        diag($s);
    } else {
        $self->{pending} = $s;
    }
    return;
}

sub _keep {
    my($self) = @_;
    if ($self->{tty}) {
        keep_diag();
    } elsif (length($self->{pending} // '')) {
        $self->formatter->_output("$self->{pending}\n");
        $self->{pending} = '';
    }
    return;
}

sub _progress {
    my($self, $s) = @_;
    $self->_diag("$self->{pretty}$s");
    return;
}

# Keep the progress line, then show a line of output below it.
sub _show {
    my($self, $line) = @_;
    $self->_keep;
    $self->formatter->_output("$line\n");
    return;
}

# Replace the progress line with $line, shown as a failure if $fail.
sub _replace {
    my($self, $line, $fail) = @_;
    my $method = $fail ? '_failure_output' : '_output';
    $self->_diag('');
    $self->formatter->$method("$self->{pretty}$line\n");
    return;
}

sub header {
    my($self) = @_;
    $self->{pretty} = $self->formatter->_format_name($self->name);
    $self->{mode} = 'normal';
    $self->_progress('');
    return;
}

sub result {
    my($self, $result) = @_;
    my $formatter = $self->formatter;
    my $line = $self->_format_for_output($result);

    if ($result->is_bailout) {
        $self->_keep;
        $formatter->_failure_output(
            'Bailout called.  Further testing stopped:  '
                . $result->explanation . "\n"
        );
        return;
    }

    if ($result->is_test) {
        if ($result->has_todo) {
            # failing TODO, TODO skip, or unexpectedly passing TODO
            $self->{mode} = 'todo';
            $self->_replace($line, $result->is_actual_ok && !$result->has_skip);
        } elsif (!$result->is_ok) {
            $self->{mode} = 'fail_start';
            $self->_replace($line, 1);
        } else {
            $self->{mode} = 'normal';
            my $planned = $self->parser->tests_planned // '?';
            my $desc = $result->description // '';
            $desc =~ s/^\s*-\s*//;
            $self->_progress(sprintf '%s/%s %s',
                    $result->number, $planned, $desc);
        }
        return;
    }

    if ($result->is_comment || $result->is_unknown) {
        return if $self->{mode} eq 'todo';
        # Test::More's failure diagnostics start with an empty line
        return if $self->{mode} eq 'fail_start' && $line eq '';
        $self->{mode} = 'fail' if $self->{mode} eq 'fail_start';
        $self->_show($line);
        return;
    }

    # plan, version, pragma, yaml: nothing to show
    return;
}

sub clear_for_close {
    return;
}

sub close_test {
    my($self) = @_;
    my $parser = $self->parser;
    my $formatter = $self->formatter;

    # replace any progress line with the result for this file
    $self->_diag('');
    $formatter->_output($self->{pretty});
    if (my $skip_all = $parser->skip_all) {
        $formatter->_output("skipped: $skip_all\n");
    } elsif ($parser->has_problems) {
        $self->_output_test_failure($parser);
    } else {
        my $time_report = $self->time_report($formatter, $parser);
        $formatter->_output($self->_make_ok_line($time_report));
    }

    # avoid circular references
    $self->parser(undef);
    return;
}

1;
