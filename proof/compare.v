Set Implicit Arguments.
Unset Strict Implicit.

Require Import basics.
Require Import enat.
Require Import allen.
Require Import signal.

(*
 * Comparaison of two intervals
 *)

Section compare.

Ltac G x := generalize x.

Ltac BAD := intros BAD; inversion BAD.


(*
 * When two intervals share some point
 *)

Lemma on_right_before (p:sig) (I J:allen) (t:nat) :
 (on I p) ->
 (in_allen t J) ->
 ~(p t) ->
 (left I) <= (left J) ->
 (ilt (right I) (right J)).
intros IOnp tInJ Npt LL.
G (inat_compare_lt_le (Fix t) (right I)); intros [LT|LE].
- exfalso.
  G (IOnp _ (in_allen_def (le_trans _ _ _ LL (allen_left tInJ)) LT)).
  auto.
- apply (ile_ilt_trans LE (allen_right tInJ)).
Qed.

Lemma end_before_has_down (p:sig) (I J:allen) :
 (tas (left I) J p) ->
 (ilt (right J) (right I)) ->
 (exists t, (in_allen t I) /\ ~(p t)).
intros (IJ,Jp) RR.
G (ilt_left_is_fix RR); intros (rj,RJ).
exists rj. split.
- split.
  + G (allen_right IJ). rewrite RJ; simpl; apply lt_le.
  + rewrite <- RJ. auto.
- apply (bounded_right_out Jp RJ).
Qed.

Lemma ilt_right_down_point (p q:sig) (I J:allen) (t:nat) :
 (tas t I p) ->
 (tas t J q) ->
 (ilt (right I) (right J)) ->
 (exists t, (in_allen t J) /\ ~(p t)).
intros tIp tJq RR.
G (ilt_left_is_fix RR). intros (ri,RI).
exists ri. split;[split|].
- apply lt_le.
  G (allen_right (tas_allen tIp)). rewrite RI. apply le_lt_trans.
  apply (allen_left (tas_allen tJq)).
- rewrite <- RI; auto.
- apply (bounded_right_out (tas_sig tIp) RI).
Qed.

Lemma tas_tas_not_left_gt (p:sig) (I J:allen) (ti tj:nat) :
 (tas ti I p) ->
 (tas tj J p) ->
 (ti<=tj) ->
 ~((left J)<(left I)).
intros (tiInI,IInp) (tjInJ,JInp) LE LT.
case_eq (left I);[intros EQ; rewrite EQ in LT;inversion LT|intros pli LI].
G (previous_left_out IInp LI). apply not_not.
apply (in_sig_slice JInp (t:=pli)).
split.
+ rewrite LI in LT; rewrite <- ltS__le; auto.
+ G (allen_right tjInJ); apply ilt_trans. simpl.
  G LE. apply lt_le_trans.
  G (allen_left tiInI). apply lt_le_trans.
  rewrite LI. auto.
Qed.

Lemma tas_tas_not_left_lt (p:sig) (I J:allen) (ti tj:nat) :
 (tas ti I p) ->
 (tas tj J p) ->
 (* Use a (on (make_allen ti tj) p) *)
 (forall t, (ti<t) -> (t<tj) -> (p t)) ->
 ~((left I)<(left J)).
intros (tiInI,IInp) (tjInJ,JInp) JOIN LT.
case_eq (left J);[intros EQ; rewrite EQ in LT;inversion LT|intros plj LJ].
G (previous_left_out JInp LJ). apply not_not.
apply (in_sig_slice IInp (t:=plj)).
split.
+ rewrite LJ in LT; rewrite <- ltS__le; auto.
+ rewrite ilt__not_ile.
  case_eq (right I);[intros ri RI|intros _; apply not_ile_inf_left].
  rewrite ile_fix; intros ILE.
  G (bounded_right_out IInp RI). apply not_not.
  apply JOIN;[G (allen_right tiInI);rewrite RI;auto|].
  G (allen_left tjInJ). apply lt_le_trans.
  rewrite LJ, ltS__le; auto.
Qed.

Lemma tas_tas_not_right_lt (p:sig) (I J:allen) (ti tj:nat) :
 (tas ti I p) ->
 (tas tj J p) ->
 (forall t, (ti<t) -> (t<tj) -> (p t)) ->
 ~(ilt (right I) (right J)).
intros (tiInI,IInp) (tjInJ,JInp) JOIN ILT.
case_eq (right I);[intros ri RI|intros EQ; rewrite EQ in ILT;inversion ILT].
G (bounded_right_out IInp RI). apply not_not.
G (nat_compare ri tj); intros[LT|[EQ|GT]].
- apply JOIN; auto.
  G (allen_right tiInI). rewrite RI. auto.
- rewrite EQ.
  apply (tas_p (tas_def tjInJ JInp)).
- apply (in_sig_slice JInp).
  split.
  + apply lt_le.
    G GT. apply le_lt_trans.
    apply (allen_left tjInJ).
  + rewrite <- RI. auto.
Qed.    

Lemma tas_tas_not_right_gt (p:sig) (I J:allen) (ti tj:nat) :
 (tas ti I p) ->
 (tas tj J p) ->
 (ti<=tj) ->
 ~(ilt (right J) (right I)).
intros (tiInI,IInp) (tjInJ,JInp) LE ILT.
case_eq (right J);[intros rj RJ|intros EQ; rewrite EQ in ILT;inversion ILT].
G (bounded_right_out JInp RJ). apply not_not.
apply (in_sig_slice IInp (t:=rj)).
split.
+ apply lt_le.
  G (allen_right tjInJ). rewrite RJ. simpl. apply le_lt_trans.
  G LE. apply le_trans.
  apply (allen_left tiInI). 
+ rewrite <- RJ; auto.
Qed.

Lemma tas_tas_join_allen_sig (p:sig) (I J:allen) (ti tj:nat) :
 (tas ti I p) ->
 (tas tj J p) ->
 (ti<=tj) ->
 (forall t, (ti<t) -> (t<tj) -> (p t)) ->
 (eq_allen I J).
intros tiIp tjJp LE JOIN.
split.
- G(nat_compare (left I) (left J));intros[LT|[EQ|GT]];[exfalso|auto|exfalso].
  + apply (tas_tas_not_left_lt tiIp tjJp JOIN LT).
  + apply (tas_tas_not_left_gt tiIp tjJp LE GT).
- G(inat_compare (right I) (right J));intros[LT|[EQ|GT]];[exfalso|auto|exfalso].
  + apply (tas_tas_not_right_lt tiIp tjJp JOIN LT).
  + apply (tas_tas_not_right_gt tiIp tjJp LE GT).
Qed.

(*
 * On unicity
 *)
Lemma tas_uniq (p:sig) (I1 I2:allen) (t:nat) :
 (tas t I1 p) ->
 (tas t I2 p) ->
 (eq_allen I1 I2).
intros tI1p tI2p.
apply (tas_tas_join_allen_sig tI1p tI2p); [auto|].
intros x; intros LT1 LT2; exfalso.
G (lt_trans _ _ _ LT1 LT2); apply lt_irrefl.
Qed.

Lemma tas_uniq_left (p:sig) (I1 I2:allen) (t:nat) :
 (tas t I1 p) ->
 (tas t I2 p) ->
 (left I1)=(left I2).
intros tI1p tI2p.
G (tas_uniq tI1p tI2p).
intros (OK,_); auto.
Qed.

Lemma tas_uniq_left_wrong (p:sig) (I1 I2:allen) (t:nat) :
 (tas t I1 p) ->
 (tas t I2 p) ->
 ~((left I1)<(left I2)).
intros tI1p tI2p.
rewrite <- le__not_lt, le_fix_def; right; apply eq_sym.
apply (tas_uniq_left tI1p tI2p).
Qed.

Lemma tas_uniq_right (p:sig) (I1 I2:allen) (t:nat) :
 (tas t I1 p) ->
 (tas t I2 p) ->
 (right I1)=(right I2).
intros tI1p tI2p.
G (tas_uniq tI1p tI2p).
intros (_,OK); auto.
Qed.

Lemma tas_uniq_right_wrong (p:sig) (I1 I2:allen) (t:nat) :
 (tas t I1 p) ->
 (tas t I2 p) ->
 ~(ilt (right I1) (right I2)).
intros tI1p tI2p.
rewrite <- ile__not_ilt; unfold ile; right; apply eq_sym.
apply (tas_uniq_right tI1p tI2p).
Qed.

Lemma in_sig_inc_allen (p:sig) (I1 I2:allen) (t:nat) :
 (tas t I1 p) ->
 (tas t I2 p) ->
 (inc_allen I1 I2).
intros tI1p tI2p t' (LE,RI).
split.
- rewrite <- (tas_uniq_left tI1p tI2p); auto.
- rewrite <- (tas_uniq_right tI1p tI2p); auto.
Qed.

Lemma inc_sig_inc_allen (p q:sig) (I J:allen) (t:nat) :
 (inc_sig p q) ->
 (tas t I p) ->
 (tas t J q) ->
 (inc_allen I J).
intros PQ (tInI,IInp) (tInJ,JInq).
apply (in_allen_in_sig_slice__inc_allen tInI tInJ JInq).
intros tt ttInI.
apply PQ.
apply (tas_p (tas_def ttInI IInp)).
Qed.

Lemma in_sig_on_equiv_allen (p:sig) (I J:allen) :
 (left J)=(left I) ->
 (right J)=(right I) ->
 (in_sig I p) ->
 (in_sig J p).
intros L R.
apply (eq_allen_in_sig (eq_allen_sym (eq_allen_def L R))).
Qed.


Lemma before_has_previous (I J:allen) (plj:nat) :
 (left I)<(left J) ->
 (ile (Fix (left J)) (right I)) ->
 (left J)=(S plj) ->
 (in_allen plj I).
intros LL LR LJ.
split.
- rewrite LJ in LL. apply ltS__le; auto.
- G LR. apply ilt_ile_trans; simpl.
  rewrite LJ; auto.
Qed.

(*
 * when the two intervals share a common point
 *)

Lemma tas_has_intersection (p q:sig) (I J:allen) (t:nat) :
 (tas t I p) ->
 (tas t J q) ->
 (ilt (Fix (left I)) (right J)).
intros ((LE1,RI1),_) ((LE2,RI2),_).
apply (le_ilt_trans LE1 RI2).
Qed.

End compare.
