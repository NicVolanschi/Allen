Set Implicit Arguments.
Unset Strict Implicit.

Require Import basics.
Require Import enat.
Require Import allen.
Require Import signal.
Require Import borders.
Require Import compare.
Require Import reactives.


Section extend.

Ltac G x := generalize x.

Ltac BAD := intros BAD; inversion BAD.

Ltac INC_CMP CV1 CV2 :=
  intros I J (LL,RR);
  apply (inc_allen_by_comp2 (CV1 _ _ LL) (CV2 _ _ RR)).

Ltac RINC_CMP CV1 CV2 :=
  intros I J (LL,RR);
  apply (inc_allen_by_comp2 (CV1 _ _ LL) (CV2 _ _ RR)).



(* eq_pred *)

Definition eq_pred (f g:(allen -> Prop)) := forall I, (f I)<->(g I).



(*
 * filter
 *)
Definition filter (f:(allen -> Prop)) (p:sig) : sig :=
 fun t => (exists I, (tas t I p) /\ (f I)).

Lemma eq_pred_eq_filter (f g:(allen -> Prop)) (p:sig) :
 (eq_pred f g) -> (eq_sig (filter f p) (filter g p)).
intros EQ t.
split;intros (I,(tIp,fI));exists I;split;auto.
- rewrite <- (EQ I); auto.
- rewrite (EQ I); auto.
Qed.

Lemma filter_follow_changes (F:allen->Prop) (p:sig) (t:nat) :
 (p t) ->
 (p (S t)) ->
 ((filter F p) t) ->
 ((filter F p) (S t)).
intros Pt PSt (I,((tI,Ip),FI)).
exists I.
split;[split|];auto.
apply (in_allen_in_sig__on_succ (tas_def tI Ip) PSt).
Qed.

Lemma filter_unfollow_changes (F:allen->Prop) (p:sig) (t:nat) :
 (p t) ->
 (p (S t)) ->
 ((filter F p) (S t)) ->
 ((filter F p) t).
intros Pt PSt (I,((StI,Ip),FI)).
exists I.
split;[split|];auto.
apply (in_allen_in_sig__on_prev (tas_def StI Ip) Pt).
Qed.

Lemma continuous___same_filter (F:allen->Prop) (p:sig) (t:nat) :
 (p t) ->
 (p (S t)) ->
 (((filter F p) t) <-> ((filter F p) (S t))).
intros Pt PSt.
split; [ apply (filter_follow_changes Pt PSt)
       | apply (filter_unfollow_changes Pt PSt)].
Qed.

Lemma inc_sig_filter (F:allen->Prop) (p:sig) : (inc_sig (filter F p) p).
intros t (I,(tIp,_)).
apply (tas_p tIp).
Qed.

Lemma filter_in_sig (p:sig) (f:allen->Prop) (I:allen) :
 (in_sig I p) ->
 (f I) ->
 (in_sig I (filter f p)).
intros IInp FI.
split;[|split].
- case_eq (left I); auto; intros pli LI.
  intros (II,((pliInII,IIInp),FII)).
  G (previous_left_out IInp LI). apply not_not.
  apply (tas_p (tas_def pliInII IIInp)).
- case_eq (right I); auto; intros ri RI.
  intros (II,((pliInII,IIInp),FII)).
  apply (bounded_right_out IInp RI).
  apply (tas_p (tas_def pliInII IIInp)).
- intros t tInI; exists I; split; auto; split; auto.
Qed.

Lemma inc_sig_filters (f g:(allen -> Prop)) (p:sig) :
 (forall I, (f I) -> (g I)) ->
 (inc_sig (filter f p) (filter g p)).
intros INC t (I,(tIp,FI)).
exists I. split;[auto|].
apply (INC I FI).
Qed.

Lemma inc_sig_allen_filter (F:allen->Prop) (p:sig) :
 (inc_sig_allen (filter F p) p).
intros I IInEx.
G IInEx; intros (A,(B,C)).
split;[|split].
- case_eq (left I); auto.
  intros l LI Pl.
  rewrite LI in A.
  apply A.
  G (in_left IInEx); rewrite LI; intros AS.
  rewrite continuous___same_filter;[ auto | auto | ].
  apply (inc_sig_filter AS).
- case_eq (right I); auto.
  intros r RI Pr.
  rewrite RI in B.
  apply B.
  G (previous_right RI); intros (pr,PRI).
  rewrite PRI.
  rewrite PRI in RI.
  rewrite PRI in Pr.
  G (previous_right_in IInEx RI); intros BP.
  rewrite <- continuous___same_filter;[auto | | auto ].
  apply (inc_sig_filter BP).
- intros t tInI.
  apply (inc_sig_filter (C _ tInI)).
Qed.

Lemma in_sig_filter (p:sig) (f:allen->Prop) (I:allen) :
 (in_sig I (filter f p)) ->
 (safe_allen_fun f) ->
 (f I).
intros IInF SF.
G (in_left IInF). intros (J,((lJ,Jp),FJ)).
G (inc_sig_allen_filter IInF); intros IInp.
G (tas_uniq (tas_def lJ Jp) (tas_def (in_allen_left I) IInp)); intros EQA.
apply (SF _ _ EQA FJ).
Qed.

Lemma tas_filter_tas_arg (F:allen->Prop) (p:sig) (I:allen) (t:nat) :
 (tas t I (filter F p)) ->
 (tas t I p).
intros (tInI,IInF).
split;[auto|].
apply (inc_sig_allen_filter IInF).
Qed.

Lemma filter_tas (p:sig) (f:allen->Prop) (I:allen) (t:nat):
 (tas t I p) ->
 (f I) ->
 (tas t I (filter f p)).
intros tIp FI.
apply (tas_def (tas_allen tIp) (filter_in_sig (tas_sig tIp) FI)).
Qed.


Lemma not_filter (f g:(allen -> Prop)) (p:sig) :
 (safe_allen_fun f) ->
 (inc_sig (or_sig (filter (fun I => ~(f I)) p) (not_sig p))
          (not_sig (filter f p)) ).
intros SF t [(I,(tIp,NF))|Np].
- apply all_not_not_ex.
  intros II.
  apply or_not_not_and.
  G (pcheck (tas t II p)). intros [EQ|NEQ]; [right|left;auto].
  G NF; apply ncontra.
  apply (SF _ _ (eq_allen_sym (tas_uniq tIp EQ))).
- G Np; apply ncontra.
  apply inc_sig_filter.
Qed.


(*
 * EXTEND
 *)
Definition extend (R:(allen -> allen -> Prop)) (p q:sig) : sig :=
 (filter (fun I => (exists J, (in_sig J q) /\ (R I J))) p).

Lemma inc_sig_extend_left (R:allen->allen->Prop) (p q:sig) :
 (inc_sig (extend R p q) p).
apply inc_sig_filter.
Qed.

Lemma contra_extend (R1 R2:(allen -> allen -> Prop)) (p q:sig) (t:nat) :
 (safe_allen_relation R2) ->
 (inclusive_relation R1) ->
 (inclusive_relation R2) ->
 (forall I J, (R1 I J) -> (R2 I J) -> False) ->
 (extend R1 p q t) ->
 (extend R2 p q t) ->
 False.
intros SF INC1 INC2 IMP (I,(tIp,(J,(Jq,R1IJ)))) (II,(tIIp,(JJ,(JJq,R2IJ)))).
G (inc_allen_in_allen (INC1 _ _ R1IJ) (tas_allen tIp)). intros tJ.
G (inc_allen_in_allen (INC2 _ _ R2IJ) (tas_allen tIIp)). intros tJJ.
G (tas_uniq tIIp tIp). intros III.
G (tas_uniq (tas_def tJJ JJq) (tas_def tJ Jq)). intros JJJ.
apply (IMP _ _ R1IJ (SF _ _ _ _ III JJJ R2IJ)).
Qed.

(* should be used for all inclusive relation *)
Lemma ext_inc (R:(allen -> allen -> Prop)) (p q:sig) (t:nat) :
 (extend R p q t) ->
 (inclusive_relation R) ->
 (exists I, (tas t I p) /\ (exists J, (tas t J q) /\ (R I J))).
intros (I,(tIp,(J,(JInq,RIJ)))) INC.
exists I. split;[auto|].
exists J. split;[|auto].
split;[|auto].
apply (inc_allen_in_allen (INC _ _ RIJ) (tas_allen tIp)).
Qed.

Lemma inc_sig_not_extend (f:(allen -> allen -> Prop)) (p q:sig) :
 (inc_sig (not_sig p) (not_sig (extend f p q))).
apply inc_sig_not.
apply inc_sig_filter.
Qed.




End extend.
