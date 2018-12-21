# User-defined operators

sub equiv() {
  my ($p,$q) = @_;
  [&or, [&and, $p, $q], [&and, [&not, $p], [&not, $q]]];
}
sub sin1() {
  my ($p) = @_;
  &equiv($p,[&not, [&delay(1),$p]]);
}
sub init() {
  my ($N) = @_;
  [&not, [&delay($N),[&true]]];
}
sub from_to() {
  my ($M,$N) = @_;
  [&and, &init($N), [&not, &init($M)]];
}
sub per() {
  my ($p,$N) = @_;
  [&or, &init($N), &equiv($p,[&delay($N),$p])];
}
sub aper() {
  my ($p,$N) = @_;
  [&or, &init($N), &equiv($p,[&not, [&delay($N),$p]])];
}
sub initeq() {
  my ($p,$q,$N) = @_;
  &equiv([&and, &init($N), $p],[&and, &init($N), $q]);
}
sub sin() {
  my ($p,$N) = @_;
  [&and, &initeq($p,[&true],$N), &aper($p,$N)];
}
sub equiv_from_to() {
  my ($p,$q,$M,$N) = @_;
  &equiv([&and, $p, &from_to($M,$N)],[&and, $q, &from_to($M,$N)]);
}
sub wv() {
  my ($p,$T0,$T1,$T0_T1) = @_;
  [&and, &equiv_from_to($p,[&false],0,$T0), [&and, &equiv_from_to($p,[&true],$T0,$T1), &per($p,$T0_T1)]];
}

# User-defined contexts
[
"s1",
&sin([&not, [&wave(1,1,0,10)]],1),
"s2",
&sin([&not, [&wave(10,10,0,100)]],10),
"s3",
&sin1([&wave(1,1,0,10)]),
"s4",
&sin1([&or, [&wave(1,1,0,10)], [&delay(20),[&wave(1,1,0,10)]]]),
"s5",
&sin1([&false]),
"s6",
&sin1([&true]),
"s7",
&aper([&not, [&wave(1,1,0,100)]],3),
"s8",
&sin([&not, [&wave(1,1,0,100)]],2),
"s9",
&sin([&not, [&wave(2,2,0,100)]],2),
"p1",
&per([&wave(1,1,0,100)],2),
"p2",
&per([&wave(1,2,0,100)],3),
"p3",
&per([&wave(2,1,0,100)],3),
"p4",
&per([&true],1),
"p5",
&per([&false],3),
"w1",
&wv([&wave(1,2,0,100)],1,2,3),
]
