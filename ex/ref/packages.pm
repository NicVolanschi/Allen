# User-defined operators

sub SP() {
  my ($r,$s) = @_;
  [&or, &overlaps($r,$s), [&or, &ended($r,$s), &contains($r,$s)]];
}
sub BDPE() {
  my ($pers1_hasPkg_pkg1,$pers2_hasPkg_pkg1) = @_;
  &meets($pers1_hasPkg_pkg1,$pers2_hasPkg_pkg1);
}
sub DPE2() {
  my ($pers1_hasPkg_pkg1,$pers2_hasPkg_pkg1,$pers1_in,$pers2_in) = @_;
  &during(&BDPE($pers1_hasPkg_pkg1,$pers2_hasPkg_pkg1),&SP($pers1_in,$pers2_in));
}
sub BIPE() {
  my ($pers1_hasPkg_pkg1,$pers2_hasPkg_pkg1,$d) = @_;
  [&lt($d), &between($pers1_hasPkg_pkg1,$pers2_hasPkg_pkg1)];
}
sub IPE2() {
  my ($pers1_hasPkg_pkg1,$pers2_hasPkg_pkg1,$pers1_in,$pers2_in,$d,$d1) = @_;
  &contains(&BIPE($pers1_hasPkg_pkg1,$pers2_hasPkg_pkg1,$d),[&lt($d1), &between($pers1_in,$pers2_in)]);
}
sub PCT() {
  my ($pers1_insideCar_c1,$pers2_insideCar_c1,$pers1_in,$pers2_in) = @_;
  &before(&met($pers1_in,$pers1_insideCar_c1),&meets($pers2_in,$pers2_insideCar_c1));
}
sub before_wide() {
  my ($p,$q) = @_;
  [&or, &before($p,$q), [&or, &between($p,$q), &after($q,$p)]];
}
sub UP() {
  my ($pkg1_in,$pers1_hasPkg_pkg1,$pers2_hasPkg_pkg1) = @_;
  [&and, &contains($pkg1_in,$pers1_hasPkg_pkg1), [&or, [&not, &contains($pkg1_in,&before_wide($pers1_hasPkg_pkg1,$pers2_hasPkg_pkg1))], [&not, &contains($pkg1_in,$pers2_hasPkg_pkg1)]]];
}

# User-defined contexts
[
"A1",
&BDPE("hasPkg(Mr1,RedBag)","hasPkg(Mrs2,RedBag)"),
"A2",
&DPE2("hasPkg(Mr1,RedBag)","hasPkg(Mrs2,RedBag)","in(Mr1)","in(Mrs2)"),
"B1",
&BIPE("hasPkg(Mr1,RedBag)","hasPkg(Mrs2,RedBag)",30),
"B2",
&IPE2("hasPkg(Mr1,RedBag)","hasPkg(Mrs2,RedBag)","in(Mr1)","in(Mrs2)",30,10),
"C",
&PCT("insideCar(Mr1,Mini)","insideCar(Mrs2,Mini)","in(Mr1)","in(Mrs2)"),
"D",
&UP("in(BlackBox)","hasPkg(Mr1,BlackBox)","hasPkg(Mrs2,BlackBox)"),
]
