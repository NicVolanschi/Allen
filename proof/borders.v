Set Implicit Arguments.
Unset Strict Implicit.

Require Import basics.
Require Import enat.
Require Import allen.
Require Import signal.
Require Import compare.

Section borders.

Ltac G x := generalize x.

Ltac BAD := intros BAD; inversion BAD.

(* The general lemma when we have an up event at t *)
Lemma up_allen (p:sig) (t:nat) :
 ~(p t) ->
 (p (S t)) ->
 (exists I, (exists J, (tas t I (not_sig p))
                    /\ (tas (S t) J p)
                    /\ (right I)=(Fix (S t))
                    /\ (left J)=(S t) ))
.
rewrite <- not_sig_def.
intros NotPSt Pt.
G (get_sig NotPSt); intros (I,(tInI,IInNp)).
G (get_sig Pt); intros (J,(StInJ,JInp)).
exists I; exists J.
split;[split|split;[split|split]];auto.
- G(inat_compare (right I) (Fix (S t))); intros [LT|[EQ|GT]];[exfalso|auto|exfalso].
  + case_eq (right I);[intros n R|intros EQ; rewrite EQ in LT; inversion LT].
    G (allen_right tInI); G LT.
    rewrite R; simpl.
    apply ltS_lt_false.
  + cut (in_allen (S t) I).
    * intros StInI.
      G (tas_p (tas_def StInI IInNp)); auto.
    * split;[|auto].
      G (allen_left tInI); auto with arith.
- G(nat_compare (left J) (S t)); intros [LT|[EQ|GT]];[exfalso|auto|exfalso].
  + cut (in_allen t J).
    * intros tInJ.
      G (tas_p (tas_def tInJ JInp)); auto.
    * split;[auto with arith|].
      G (allen_right StInJ); case (right J);[|auto].
      intros n; simpl; auto with arith.
  + case_eq (left J).
    * intros EQ; rewrite EQ in GT; inversion GT.
    * intros n L.
      G (allen_left StInJ); G GT.
      rewrite L; simpl.
      apply ltS_lt_false.
Qed.

Lemma down_allen (p:sig) (t:nat) :
 (p t) ->
 ~(p (S t)) ->
 (exists I, (exists J, (tas t I p)
                    /\ (tas (S t) J (not_sig p))
                    /\ (right I)=(Fix (S t))
                    /\ (left J)=(S t) ))
.
intros Pt NPSt.
rewrite <- not_not in Pt.
G (up_allen (p:=(not_sig p)) (t:=t) Pt NPSt).
intros (I,(J,(tIp,(StJp,(RI,LJ))))).
exists I. exists J.
split; auto.
apply (eq_sig_tas (eq_sig_not_not p) tIp).
Qed.

Lemma up_allen_left (p:sig) (t:nat) :
 ~(p t) ->
 (p (S t)) ->
 (exists I, (in_sig I (not_sig p)) /\ (right I)=(Fix (S t))).
intros NOT IS.
G (up_allen NOT IS).
intros (I,(_,((_,IInp),(_,(RI,_))))).
exists I; split; auto.
Qed.

(* the 4 projections of previous lemmas *)
Lemma up_allen_right (p:sig) (t:nat) :
 ~(p t) ->
 (p (S t)) ->
 (exists I, (in_sig I p) /\ (left I)=(S t)).
intros NotPt PSt.
G (up_allen NotPt PSt).
intros (_,(J,(_,((_,JInp),(_,LI))))).
exists J; auto.
Qed.

Lemma down_allen_left (p:sig) (t:nat) :
 (p t) ->
 ~(p (S t)) ->
 (exists I, (in_sig I p) /\ (right I)=(Fix (S t))).
intros Pt NotPSt.
G (down_allen Pt NotPSt).
intros (I,(_,((_,IInp),(_,(RI,_))))).
exists I; split; auto.
Qed.

Lemma down_allen_right (p:sig) (t:nat) :
 (p t) ->
 ~(p (S t)) ->
 (exists I, (in_sig I (not_sig p)) /\ (left I)=(S t)).
intros Pt NotPSt.
G (down_allen Pt NotPSt).
intros (_,(J,(_,((_,JInp),(_,LI))))).
exists J; auto.
Qed.

(* Applications of previous lemmas *)
Lemma next_down (I:allen) (p:sig) (r:nat) :
 (in_sig I p) ->
 (right I) = (Fix r) ->
 (exists J, (in_sig J (not_sig p)) /\ (left J)=r).
intros IInp RI.
case_eq r.
- intros EQ.
  G (allen_right_gt0 I). rewrite RI, EQ; BAD.
- intros pr EQ.
  rewrite EQ in RI.
  apply (down_allen_right (previous_right_in IInp RI) (bounded_right_out IInp RI)).
Qed.

Lemma in_allen_last_is_right (p:sig) (I:allen) (t:nat) :
 (tas t I p) ->
 ~(p (S t)) ->
 (right I)=(Fix (S t)).
intros (tInI,IInp) NotPSt.
G (tas_p (tas_def tInI IInp)). intros Pt.
G (down_allen_left Pt NotPSt).
intros (II,(IIInP,RII)).
rewrite <- RII.
apply (tas_uniq_right (tas_def tInI IInp)
                      (tas_def (in_allen_previous_right RII) IIInP)).
Qed.

Lemma not_sig_follow (p:sig) (I J:allen) (pr:nat) :
 (in_sig I p) ->
 (in_sig J (not_sig p)) ->
 (left J)=(S pr) ->
 (in_allen pr I) ->
 (right I)=(Fix (left J)).
intros IInp JInNotp LJ prInJ.
rewrite LJ.
apply (in_allen_last_is_right (p:=p) (I:=I) (t:=pr)). 
split; auto.
rewrite <- LJ.
apply (in_left JInNotp).
Qed.

Lemma border_left (p:sig) (I:allen) (t1 t2:nat) :
 (tas t2 I p) ->
 ~(p t1) ->
 (p (S t1)) ->
 (t1<t2) ->
 (forall x, (t1 < x) -> (x <= t2) -> (p x)) ->
 (left I)=(S t1).
intros t2Ip NPt1 PSt1 LE SLI.
G (up_allen_right NPt1 PSt1).
intros (II,(IIInp,LII)).
rewrite <- LII.
apply (tas_uniq_left (I2:=II) t2Ip). split; auto.
split.
rewrite LII; apply (lt_leS LE).
apply (in_allen_in_sig_follow_right (p:=p) (t:=(S t1))); auto.
- split; auto.
  rewrite <- LII.
  apply in_allen_left.
- intros x LTx LEx.
  apply SLI; auto.
  apply lt_le; auto.
Qed.


Lemma in_sig_between (p:sig) (I J K:allen) :
 (right J)=(Fix (left I)) ->
 (right I)=(Fix (left K)) ->
 (in_sig J (not_sig p)) ->
 (in_sig K (not_sig p)) ->
 (forall t, (in_allen t I) -> (p t)) ->
 (in_sig I p).
intros JI IK JInNotp KInNotq SLICE.
split;[|split;[|auto]].
- case_eq (left I); auto.
  intros l LI.
  rewrite LI in JI.
  apply (previous_right_in JInNotp JI).
- case_eq (right I); auto.
  intros r RI.
  G IK; rewrite RI; simpl; intros OK. inversion OK.
  apply (in_left KInNotq).
Qed.

Lemma previous_up (I:allen) (p:sig) (pl:nat) :
 (in_sig I p) ->
 (left I) = (S pl) ->
 (exists J, (in_sig J (not_sig p)) /\ (right J)=(Fix (S pl))).
intros IInp LI.
apply down_allen_left.
- apply (previous_left_out IInp LI).
- rewrite not_not_sig_def.
  rewrite <- LI. 
  apply (in_left IInp).
Qed.



End borders.
