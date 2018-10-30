Set Implicit Arguments.
Unset Strict Implicit.

Require Import basics.
Require Import enat.
Require Import allen.
Require Import signal.
Require Import borders.
Require Import compare.

Section reactives.

Ltac G x := generalize x.

Ltac BAD := intros BAD; inversion BAD.



(* inc_sig *)

Lemma inc_sig_not (p q:sig):(inc_sig p q) -> (inc_sig (not_sig q) (not_sig p)).
intros INC t.
apply ncontra; auto.
Qed.


Lemma inc_sig_allen_redef_l (p q:sig) :
 (inc_sig_allen p q) ->
 (forall (I:allen),
    (in_sig I q) ->
    ((in_sig I p) \/ (on I (not_sig p))) ).
intros H I IInq.
cut ((in_sig I p)\/(~(in_sig I p))); [|tauto].
intros [IN|NI];[left;auto|right].
intros t tInI.
intros BAD.
G (get_sig BAD); intros (J,(tInJ,JInp)).
G (H _ JInp); intros JInq.
G (tas_uniq_left (tas_def tInI IInq) (tas_def tInJ JInq)); intros L.
G (tas_uniq_right (tas_def tInI IInq) (tas_def tInJ JInq)); intros R.
G (in_sig_on_equiv_allen L R JInp); auto.
Qed.

(*
 * AND
 *)

Definition and_sig (p q:sig) : sig := fun t => (p t) /\ (q t).

Lemma and_sig_def (p q:sig) (t:nat) :
 (p t) ->
 (q t) ->
 ((and_sig p q) t).
unfold and_sig; simpl. auto.
Qed.

Lemma and_sig_right (p q:sig) (t:nat) : ((and_sig p q) t) -> (q t).
simpl. unfold and_sig. tauto.
Qed.

Lemma and_left (p q:sig) (t:nat) : ((and_sig p q) t) -> (p t).
unfold and_sig. simpl; tauto.
Qed.

Lemma and_right (p q:sig) (t:nat) : ((and_sig p q) t) -> (q t).
unfold and_sig. simpl; tauto.
Qed.

Lemma inc_and_sig (p q:sig) (I:allen) :
 (in_sig I q) ->
 (forall t, (in_allen t I) -> (p t)) ->
 (in_sig I (and_sig p q)).
intros IInp INC.
split;[|split].
- case_eq (left I); auto.
  intros pl LI (ppl,qpl).
  apply (previous_left_out IInp LI); auto.
- case_eq (right I); auto.
  intros n RI (ppl,qpl).
  apply (bounded_right_out IInp RI); auto.
- intros t tInI. split.
  + apply (INC _ tInI).
  + apply (tas_p (tas_def tInI IInp)).
Qed.

Lemma and_sig_inc_sig_commm (p q:sig) :
 (inc_sig (and_sig p q) (and_sig q p)).
intros t (Pt,Qt); split; auto.
Qed.

Lemma and_sig_comm (p q:sig) : (eq_sig (and_sig p q) (and_sig q p)).
apply inc_sig_asym; apply and_sig_inc_sig_commm.
Qed.

Lemma in_sig_and_sym (p q:sig) (I:allen) :
 (inc_sig_allen (and_sig p q) (and_sig q p)).
apply inc_sig_allen_refl.
apply and_sig_comm.
Qed.

Lemma in_sig_and__inc_allen (p q:sig) (I J:allen) (t:nat) :
 (tas t I (and_sig p q)) ->
 (tas t J p) ->
 (inc_allen I J).
intros (tInI,IInA) (tInJ,JInp).
apply (in_allen_in_sig_slice__inc_allen tInI tInJ JInp).
intros tt ttInI.
G (tas_p (tas_def ttInI IInA)); intros (OK,_); auto.
Qed.

Lemma over_over_new_right_left (p q:sig) (I J:allen) (t:nat)
 (WF:(ilt (Fix (left J)) (right I))) :
 (tas t I p) ->
 (tas t J q) ->
 ((left I) < (left J)) ->
 (ilt (right I) (right J)) ->
 (tas t (make_allen (m:=left J) (M:=(right I)) WF) (and_sig p q)).
intros tIp tJq LIJ RIJ.
G tIp; intros (tInI,IInp). G tJq; intros (tInJ,JInq).
split;[|].
- split;[apply (allen_left tInJ)|apply (allen_right tInI)].
- split;[|split]; simpl.
  + case_eq (left J); auto; intros lj LJ.
    G (previous_left_out JInq LJ).
    apply ncontra; apply and_right.
  + case_eq (right I); auto; intros ri RI.
    G (bounded_right_out IInp RI).
    apply ncontra; apply and_left.
  + intros t' (LE,LT).
    split.
    * apply (in_sig_slice IInp).
      split;[ | auto].
      apply lt_le. apply (lt_le_trans _ _ _ LIJ LE).
    * apply (in_sig_slice JInq).
      split;[auto |].
      apply (ilt_trans LT RIJ).
Qed.








(*
 * OR
 *)
Definition or_sig (p q:sig) : sig := fun t => (p t) \/ (q t).

Lemma or_sig_right (p q:sig) (t:nat) : (q t) -> (or_sig p q t).
right; auto.
Qed.

Lemma not_or__and_not (p q:sig) (t:nat) :
 ((not_sig (or_sig p q)) t) -> ((and_sig (not_sig p) (not_sig q)) t).
unfold and_sig, or_sig, not_sig; simpl.
tauto.
Qed.

Lemma and_not__not_or (p q:sig) (t:nat) :
 ((and_sig (not_sig p) (not_sig q)) t) -> ((not_sig (or_sig p q)) t).
unfold and_sig, or_sig, not_sig; simpl.
tauto.
Qed.

Lemma inc_sig_or (p x:sig) : (inc_sig p (or_sig x p)).
intros t Pt. right. auto.
Qed.

Lemma or_sig_exclude_left (p q:sig) (t:nat) :
 ((or_sig p q) t) ->
 ((not_sig p) t) ->
 (q t).
intros [Pt|Qt] NPt; [exfalso;auto|auto].
Qed.

Lemma inc_allen_or_right (p x:sig) (I J:allen) (t:nat) :
  (tas t I p) ->
  (tas t J (or_sig x p)) ->
  (inc_allen I J).
intros tIp tJOR.
G (inc_sig_or (p:=p) x); intros IOR.
apply (inc_sig_inc_allen IOR tIp tJOR).
Qed.

(*
 * IMPLY
 *)
Definition imp_sig (p q:sig) := (or_sig (not_sig p) q).

Lemma in_sig_imply_right (p q:sig) (I J K:allen) (t:nat) :
  (tas t I p) ->
  (tas t J q) ->
  (tas t K (imp_sig p q)) ->
  (ilt (right I) (right K)) ->
  (ile (right I) (right J)).
intros (tInI,IInp) (tInJ,JInq) (tInK,KInOR) IK.
G (inat_compare_lt_le (right J) (right I)). intros [LT|OK]; [exfalso|auto].
G LT; clear LT; case_eq (right J);[intros rj RJ LT|auto].
cut (imp_sig p q rj).
- apply tilde; rewrite <- not_sig_def.
  apply and_not__not_or; split.
  + rewrite not_sig_def, not_sig_def, not_not.
    cut(in_allen rj I);[intros rjInI|].
    * apply (tas_p (tas_def rjInI IInp)).
    * split;[|auto].
      apply lt_le.
      G (allen_right tInJ). rewrite RJ. simpl. apply le_lt_trans.
      apply (allen_left tInI).
  + apply (bounded_right_out JInq RJ). 
- cut (in_allen rj K);[intros rjInK|].
  + apply (tas_p (tas_def rjInK KInOR)).
  + split;[|apply (ilt_trans LT IK)].
    apply lt_le.
    G (allen_right tInJ). rewrite RJ. simpl. apply le_lt_trans.
    apply (allen_left tInK).
Qed.

Lemma in_sig_imply_left (p q:sig) (I J K:allen) (t:nat) :
  (tas t I p) ->
  (tas t J q) ->
  (tas t K (imp_sig p q)) ->
  (left I)<(left K) ->
  (left I)<(left J).
intros tIp tJq tKOR IK.
G (inc_allen_or_right tJq tKOR).
intros INC; G (inc_allen_left INC).
apply (lt_le_trans _ _ _ IK).
Qed.

Lemma ends_not_imp (p q:sig) (I J:allen) (pli:nat) :
 (in_sig I p) ->
 (in_sig J q) ->
 (left J)<(left I) ->
 (right I)=(right J) ->
 (left I)=(S pli) ->
 ~(imp_sig q p pli).
intros IInp JInq LL RR LI.
apply and_not__not_or. split.
- rewrite not_sig_def, not_sig_def, not_not.
  apply (in_sig_slice JInq).
  (* lemmma for borders *)
  split.
  + rewrite LI in LL; rewrite <- ltS__le; auto.
  + rewrite <- RR.
    G (wf I). rewrite LI.
    case (right I); auto.
    intros ii. simpl. auto with arith.
- apply (previous_left_out IInp LI); auto.
Qed.

Lemma in_sig_imp_left (p q:sig) (I J K:allen) (t ri:nat) :
 (tas t I p) ->
 (tas t J q) ->
 (tas t K (imp_sig q p)) ->
 (left J)<(left I) ->
 (right I)=(right J) ->
 (right I)=(Fix ri) ->
 (left J) < (left K).
intros tIp tJq tKO LL RR RI.
G tIp; intros (tInI,IInp).
G (gt0_has_previous LL). intros (pli,LI).
cut ((left K)=(left I));[intros EQ;rewrite EQ;auto|].
cut ((imp_sig q p) (left I));[rewrite LI|right;apply (in_left IInp)].
cut (~((imp_sig q p) pli)).
- intros NOpli OSpli. G (up_allen NOpli OSpli). clear NOpli OSpli.
  intros (_,(KK,(_,(liKKO,(_,OK))))).
  rewrite <- OK.
  cut (eq_allen KK K);[intros(ELL,_);auto|].
  apply (tas_tas_join_allen_sig liKKO tKO)
    ;[G (allen_left tInI); rewrite LI; auto|].
  rewrite <- LI.
  intros tt GT LT.
  right.
  apply (in_sig_slice IInp).
  split;[apply (lt_le GT)|].
  G (allen_right tInI). apply ilt_trans. auto.
- apply (ends_not_imp (tas_sig tIp) (tas_sig tJq) LL RR LI).
Qed.

Lemma in_sig_imp_right (p q:sig) (I J K:allen) (t ri:nat) :
 (tas t I p) ->
 (tas t J q) ->
 (tas t K (imp_sig q p)) ->
 (left J)<(left I) ->
 (right I)=(right J) ->
 (right I)=(Fix ri) ->
 (ilt (right J) (right K)).
intros tIp tJq tKO LL RR RI.
rewrite <- RR, RI.
apply (in_allen_in_sig_follow_right tKO).
intros tt GT LE; G LE; rewrite (le_fix_def).
intros [LT|EQ];[right|left].
- apply (tas_p (I:=I)).
  apply tas_def;[|apply (tas_sig tIp)].
  split.
  + apply lt_le. G GT; apply le_lt_trans.
    apply (allen_left (tas_allen tIp)).
  + rewrite RI; simpl; auto.
- rewrite RR in RI.
  G (bounded_right_out (tas_sig tJq) RI).
  rewrite EQ; auto.
Qed.




(*
 * UP
 *)
Definition up (p:sig) : sig := fun t =>
 (0<t) /\ (exists I, (t=(left I)) /\ (in_sig I p)).

Lemma up_succ (p:sig) (t:nat) :
 ~(p t) ->
 (p (S t)) ->
 ((up p) (S t)).
intros BEF UP.
split; auto with arith.
G (up_allen_right BEF UP); intros (I,(IInp,LI)).
exists I; auto.
Qed.

Lemma in_allen_NoUp_left (p:sig) (I:allen) (t:nat) :
 (tas t I p) ->
 (not_sig (up p) t) ->
 (0<t) ->
 ((left I) < t).
intros (tInI,IInp) NUP GT0.
G (allen_left tInI).
apply diff_le_lt.
G NUP; apply ncontra; intros LL.
split;[auto|].
exists I;split;[auto|auto].
Qed.

Lemma join_or_up (p:sig) (I1 I2:allen) (t1 t2:nat) :
 (tas t1 I1 p) ->
 (tas t2 I2 p) ->
 (t1 <= t2) ->
 ((eq_allen I1 I2) \/ (exists t, (t1<t<=t2) /\ (up p t))).
intros t1I1p t2I2p LE.
apply (dec_imp (tas_tas_join_allen_sig t1I1p t2I2p LE)).
rewrite (not_for__ex_not ); auto.
intros (t,NIM).
G (not_imply2 NIM); intros (LTt,(GTt,NPt)). clear NIM.
G (try_find_left2 (tas_p t2I2p)).
intros [BAD | (m,(LTm,(NPm,SLI)))]; [exfalso; G (BAD _ GTt); auto|].
cut (p (S m));[intros PSm|apply SLI;auto].
G(nat_compare_lt_le m t); intros [Lm|Em].
- exfalso.
  G NPt. apply not_not.
  apply SLI; [auto| apply (lt_le GTt)].
- exists (S m);split.
  + split.
    * omega.
    * apply (lt_leS LTm).
  + split;[auto with arith|].
    exists I2. split;[|apply (tas_sig t2I2p)].
    rewrite (border_left t2I2p NPm PSm LTm); auto.
Qed.

Lemma inc_sig_up (p:sig) : (inc_sig (up p) p).
intros t (G,(I,(tInI,IInp))).
apply (tas_p (I:=I)). split; auto.
rewrite tInI. apply in_allen_left.
Qed.

Lemma up_left (p:sig) (I:allen) (t:nat) :
 (tas t I p) ->
 (up p t) ->
 (left I)=t.
intros tIp (GT0,(II,(LII,IIInq))).
rewrite LII.
apply (tas_uniq_left tIp). split; auto.
rewrite LII. apply in_allen_left.
Qed.

Lemma up_in (p:sig) (t:nat) : (up p t) -> (p t).
intros (GT0c,(I,(LI,IInp))).
rewrite LI.
apply (tas_p (tas_def (in_allen_left I) IInp)).
Qed.

Lemma up_shared (p:sig) (I:allen) (t1 t2:nat) :
 (tas t1 I p) ->
 (in_allen t2 I) ->
 (up p t1) ->
 (up p t2) ->
 (t1=t2).
intros tIp t2InI (GT0,(I1,(LI1,I1Inp))) (_,(I2,(LI2,I2Inp))).
rewrite LI1 in *. clear LI1.
rewrite LI2 in *. clear LI2.
rewrite <- (tas_uniq_left tIp (tas_def (in_allen_left I1) I1Inp)).
rewrite <- (tas_uniq_left (tas_mov tIp t2InI)
                          (tas_def (in_allen_left I2) I2Inp)); auto.
Qed.

Lemma before_up (p:sig) (t:nat) : (up p (S t)) -> ~(p t).
intros (_,(I,(LI,IInp))).
apply (previous_left_out IInp (eq_sym LI)).
Qed.

(*
 * SYNC
 *)
Definition sync (p q:sig) := (and_sig (up p) (up q)).

Lemma sync_comm (p q:sig) (t:nat) : (sync p q t) -> (sync q p t).
intros (U1,U2). split; auto.
Qed.

Lemma inc_sig_sync_first (p q:sig) : (inc_sig (sync p q) p).
intros t (U1,U2).
apply (inc_sig_up U1).
Qed.
Lemma sync_left_first (p q:sig) (I:allen) (t:nat) :
 (tas t I p) ->
 (sync p q t) ->
 (left I)=t.
intros tIp (U1,_).
apply (up_left tIp U1).
Qed.

Lemma sync__left (p q:sig) (I J:allen) (t:nat) :
 (tas t I p) ->
 (tas t J q) ->
 (sync p q t) ->
 (left I)=(left J).
intros tIp tJq SY.
rewrite (sync_left_first tIp SY).
rewrite (sync_left_first tJq (sync_comm SY)).
auto.
Qed.

Lemma sync_left (p q:sig) (I J:allen) (t pli:nat) :
 (tas t I p) ->
 (tas t J q) ->
 (left I) = (left J) ->
 (left I) = (S pli) ->
 (sync p q (left I)).
intros (_,Ip) (_,Jq) LL LI.
split; [split|split].
- rewrite LI; auto with arith.
- exists I. auto.
- rewrite LI; auto with arith.
- exists J; auto.
Qed.

(* 
 * UP_AFTER
 *)
Definition up_after (p q:sig) :=
  (and_sig (up q) (and_sig p (not_sig (up p)))).

Lemma overlaps_up_after_left (p q:sig) (I J:allen) (t:nat) :
 (tas t I p) ->
 (tas t J q) ->
 ((left I) < (left J)) ->
 (ilt (right I) (right J)) ->
 (ilt (Fix (left J)) (right I)) ->
 (up_after p q (left J)).
intros tIp tJq LIJ RIJ LIRJ.
split;[split|split].
- apply (lt_0lt LIJ).
- exists J. split;[auto|apply (tas_sig tJq)].
- apply (in_sig_slice (tas_sig tIp)).
  apply (in_allen_def (lt_le LIJ) LIRJ).
- intros (A,(K,(JK,KInp))).
  rewrite JK in *.
  G (tas_mov tIp (in_allen_def (lt_le LIJ) LIRJ)). intros IN.
  rewrite (tas_uniq_left IN (tas_def (in_allen_left K) KInp)) in LIJ.
  apply (lt_irrefl _ LIJ).
Qed.


(*
 * DN
 *)
Definition dn (p:sig) : sig := fun t =>
 (exists I, ((Fix t)=(right I)) /\ (in_sig I p)).

(*
 * DELAY
 *)
Definition delay (T:nat) (p:sig) : sig := fun t =>
  (T<=t) /\ (p (t-T)).

Lemma in_sig_close_in_sig_delay (p:sig) (I:allen) (T:nat) :
 (in_sig I p) ->
 (in_sig (make_allen (m:=T+(left I)) (M:=(fiadd T (right I))) (wf_shift T I))
         (delay T p) ).
intros IInp.
split;[|split;[|]].
- simpl. case T;simpl.
  + case_eq (left I); auto.
    intros pl LI.
    G (previous_left_out IInp LI).
    apply ncontra.
    intros (_,OK). replace (pl-0) with pl in OK;[auto|auto with arith].
  + intros PT.
    case_eq (left I); [intros _|intros pl].
    * replace (PT+0) with PT;[|auto with arith].
      intros (BAD,_). G BAD.
      rewrite (le__not_lt). auto.
    * intros LI.
      G (previous_left_out IInp LI).
      apply ncontra.
      intros (_,OK). G OK.
      replace (PT + S pl - S PT) with pl;[auto|apply addSsubS].
- simpl.
  case_eq (right I); simpl; [|auto].
  intros r RI.
  intros (_,OK). G OK.
  replace (T+r-T) with r;[|rewrite minus_plus; auto].
  apply (bounded_right_out IInp RI).
- intros t (LE,RI). simpl in LE, RI.
  split.
  + G LE; auto with arith.
    apply le_add_le.
  + apply (in_sig_slice IInp).
    split;[apply (le_add_le_sub LE)|].
    G RI; case_eq (right I); auto.
    clear RI; simpl. intros r RI.
    apply lt_add_lt_sub_left.
    G (allen_right_gt0 I); rewrite RI; auto.
Qed.

Lemma in_sig_delay1_eq_sig (p:sig) (I J:allen) (t:nat) :
 (tas t I p) ->
 (tas t J (delay 1 p)) ->
 (eq_allen J
      (make_allen (m:=(1+(left I))) (M:=(fiadd 1 (right I))) (wf_shift 1 I)) ).
intros (tInI,IInp) (tInJ,JInDY).
apply (tas_uniq (tas_def tInJ JInDY));split;[split|apply (in_sig_close_in_sig_delay 1 IInp)].
- G (nat_compare (left I) t); intros [OK|[BAD|VBAD]].
  + apply (lt_leS OK).
  + exfalso.
    G (tas_p (tas_def tInJ JInDY)).
    unfold delay.
    G BAD. case t.
    * intros _ (NO,_); inversion NO.
    * intros pl LI.
      replace (S pl - 1) with pl;[|auto with arith]. intros (_,OK). G OK.
      apply (previous_left_out IInp LI).
  + exfalso.
    G (allen_left tInI).
    rewrite le__not_lt. apply not_not; auto.
- G (allen_right tInI).
  simpl; case (right I); simpl; auto.
Qed.


Lemma in_sig_delay1_left (p:sig) (I J:allen) (t:nat) :
 (tas t I p) ->
 (tas t J (delay 1 p)) ->
 (left J)=(S (left I)).
intros tIp tJDY.
G (in_sig_delay1_eq_sig tIp tJDY).
intros (OK,_); auto.
Qed.

End reactives.
