# User-defined operators

sub breakfast() {
  my ($Ts,$Te) = @_;
  my $x=&slot_dst($Ts,$Te); [&and, &occ(&up("ContactS_Cupboard"),$x), &occ(&up("EMeter_Coffeemaker"),$x)];
}
sub lunch() {
  my ($Ts,$Te,$T) = @_;
  &occ([&and, &recent(&up("ContactS_Fridge"),$T), "EMeter_Coffeemaker"],&slot_dst($Ts,$Te));
}
sub dinner() {
  my ($Ts,$Te) = @_;
  my $x=&slot_dst($Ts,$Te); [&and, &occ(&up("ContactS_Fridge"),$x), &occ(&up("EMeter_Coffeemaker"),$x)];
}
sub gotobed() {
  my ($m1,$m2,$T) = @_;
  &occ([&and, &recent(&dn($m1),$T), &up($m2)],&slot_dst(75600000,86400000));
}
sub wakeup() {
  my ($m1,$m2,$T) = @_;
  &occ([&and, &recent(&dn($m1),$T), &up($m2)],&slot_dst(25200000,32400000));
}
sub any_emeter_up() {
  my () = @_;
  &any_up("EMeter_Coffeemaker","EMeter_L");
}
sub any_contact_sw() {
  my () = @_;
  &any_sw("ContactS_Cupboard","ContactS_E","ContactS_Fridge");
}
sub any_motion_but_shower_up() {
  my () = @_;
  &any_up("MotionD_B","MotionD_Ba","MotionD_E","MotionD_K","MotionD_L","MotionD_T");
}
sub any_but_shower2() {
  my () = @_;
  [&or, &any_motion_but_shower_up(), [&or, &any_contact_sw(), &any_emeter_up()]];
}
sub bath() {
  my ($T) = @_;
  [&gt($T), &flat_right("MotionD_S",[&not, &any_but_shower2()])];
}
sub departurealert() {
  my ($T,$Hs,$He) = @_;
  &during([&gt($T), "ContactS_E"],&slot_dst($Hs,$He));
}
sub dooralert() {
  my ($T) = @_;
  [&gt($T), [&and, "ContactS_E", [&not, "MotionD_E"]]];
}
sub any_motion_up() {
  my () = @_;
  &any_up("MotionD_B","MotionD_Ba","MotionD_E","MotionD_K","MotionD_L","MotionD_S","MotionD_T");
}
sub indoor_post() {
  my () = @_;
  &holds([&not, [&or, &any_motion_up(), [&or, &any_emeter_up(), &any_contact_sw()]]],[&gt(600000), &between(&dn("ContactS_E"),&up("ContactS_E"))]);
}

# User-defined contexts
[
"ctx1",
&step(1),
]
