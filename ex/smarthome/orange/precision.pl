#!/usr/bin/perl

my %total = ();

while (<>) {
    my ($ts, $s, $v, $d, $n) = /^(\d+);([^;]*);([01]);([^;]*)(?:;(\d+)?)/;
    die "line error" if !defined($d);
    if ($v == 0) {
	die "no delta" if !defined($n);
	$total{$s} += $n;
    }
}

for my $activity (qw(computing office_tv cooking shower dishes living_tv dressing toilet sink eating napping preparing reading)) {
    &assess($activity);
}

exit;

sub assess() {
    my ($activity) = @_;
    my $precision = &get("${activity}_tp") / &get("${activity}_d");
    my $recall = &get("${activity}_tp") / &get("${activity}_a");
    print "$activity: precision=$precision, recall=$recall\n";
}

sub get() {
    my ($k) = @_;
    die "undefined: $k" if !exists($total{$k});
    return $total{$k};
}
