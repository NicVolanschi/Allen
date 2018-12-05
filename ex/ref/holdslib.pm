# User-defined operators

sub up() {
  my ($p) = @_;
  &dn([&not, $p]);
}
sub dn() {
  my ($p) = @_;
  [&and, [&not, $p], [&delay(1),$p]];
}
sub ex() {
  my ($p,$q) = @_;
  [&and, $q, [&not, &holds([&not, $p],$q)]];
}
sub met() {
  my ($p,$q) = @_;
  &occ([&and, &dn($q), &up($p)],$p);
}
sub eq() {
  my ($p,$q) = @_;
  [&and, &holds($p,$q), &holds($q,$p)];
}
sub over() {
  my ($p,$q) = @_;
  my $s=[&and, &up($q), [&and, $p, [&not, &up($p)]]]; my $q1=&ex($s,$q); my $q2=&ex([&not, $p],$q1); my $q3=&ex($s,[&and, $p, $q]); [&and, $q2, $q3];
}
sub overlapped() {
  my ($p,$q) = @_;
  my $s=[&and, &up($p), [&and, $q, [&not, &up($q)]]]; my $p1=&ex($s,$p); &ex([&not, $q],$p1);
}
sub overlaps() {
  my ($p,$q) = @_;
  &ex(&over($p,$q),$p);
}
sub starts() {
  my ($p,$q) = @_;
  my $s=[&and, &up($p), &up($q)]; my $p1=&ex($s,$p); my $q1=&ex($s,$q); my $q2=&ex([&not, $p],$q1); [&and, $p1, $q2];
}
sub started() {
  my ($p,$q) = @_;
  my $s=[&and, &up($p), &up($q)]; my $q1=&ex($s,$q); &ex([&not, $p],$q1);
}
sub ends() {
  my ($p,$q) = @_;
  [&and, &over($q,[&or, $p, [&not, $q]]), [&not, &over($q,$p)]];
}
sub ended() {
  my ($p,$q) = @_;
  &ex(&ends($q,$p),$p);
}
sub meets() {
  my ($p,$q) = @_;
  my $nq=[&not, $q]; [&or, &ends($p,$nq), [&or, &eq($p,$nq), &ended($p,$nq)]];
}
sub contains() {
  my ($p,$q) = @_;
  &ex(&during($q,$p),$p);
}
sub btw() {
  my ($p,$q) = @_;
  &over([&not, $q],[&not, $p]);
}
sub before() {
  my ($p,$q) = @_;
  &meets($p,&between($p,$q));
}
sub after() {
  my ($p,$q) = @_;
  &met($p,&between($q,$p));
}

# User-defined contexts
[
"ctx",
&step(1),
]
