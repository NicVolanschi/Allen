#!/usr/bin/perl

use Time::Local;
use POSIX (strftime);

while (<>) {
    chomp;
    my ($d, $v, $s) = /^"(.*)",(START|STOP):(.*)$/;
    die "line error" if !defined($s);
    my ($year, $month, $day, $hh, $mm, $ss) =
	($d =~ /^(\d\d\d\d)-(\d\d)-(\d\d) (\d\d):(\d\d):(\d\d)$/);
    die "date error" if !defined($ss);
    my $ts = timelocal($ss, $mm, $hh, $day, $month - 1, $year) * 1000;
    my $sts = strftime("%Y-%m-%dT%H:%M:%S", localtime ($ts / 1000));
    print "$sts;$s;$v\n";
}
