Set Implicit Arguments.
Unset Strict Implicit.

Require Import basics.
Require Import enat.
Require Import allen.
Require Import signal.
Require Import compare.
Require Import borders.
Require Export reactives.
Require Import extend.

Section allenfuns.

Ltac G x := generalize x.

Ltac BAD := intros BAD; inversion BAD.

Ltac INC_CMP CV1 CV2 :=
  intros I J (LL,RR);
  apply (inc_allen_by_comp2 (CV1 _ _ LL) (CV2 _ _ RR)).

Ltac RINC_CMP CV1 CV2 :=
  intros I J (LL,RR);
  apply (inc_allen_by_comp2 (CV1 _ _ LL) (CV2 _ _ RR)).

Ltac SAFE_ALLEN_RELATION2 :=
  intros I1 I2 J1 J2 (E1,E2) (E3,E4) (LL1,RR1);
  rewrite E1 in *; rewrite E2 in *; rewrite E3 in *; rewrite E4 in *;
  split; auto.

(*
 * HOLDS
 *)
Definition holds (p q:sig) : sig := fun t =>
 (exists (I:allen), (tas t I q) /\ (on I p)).

(*
 * OCCURS
 *)
Definition occurs (p q:sig) : sig :=
 (filter (fun I => (exists t, (in_allen t I) /\ (p t))) q).

Lemma inc_sig_allen_occurs_right (p q:sig) :
  (inc_sig_allen (occurs p q) q).
apply inc_sig_allen_filter.
Qed.

Lemma in_sig_occurs_has (p q:sig) (I:allen) :
 (in_sig I (occurs p q)) ->
 (exists t, (in_allen t I) /\ (p t)).
intros IInO.
apply (in_sig_filter IInO).
intros A B EQA (t,(tInI,Pt)).
exists t; split; auto.
apply (inc_allen_refl EQA tInI).
Qed.

Lemma occurs_not_right (p q:sig) (I J:allen) (t:nat) :
 (tas t I p) ->
 (tas t J q) ->
 (occurs (not_sig p) q t) ->
 ((left I)<=(left J)) ->
 (ilt (right I) (right J)).
intros tIp tJq (JJ,((tInJJ,JJInq),(tt,(ttInJJ,NPtt)))) LL.
G (tas_uniq (tas_def tInJJ JJInq) tJq); intros JJJ; clear tInJJ JJInq.
G (eq_allen_in_allen JJJ ttInJJ). intros ttInJ. clear ttInJJ JJJ.
G NPtt; clear NPtt.
apply contra. rewrite <- ile__not_ilt, not_sig_def, not_not.
intros RR. apply (tas_p (I:=I)).
split;[|apply (tas_sig tIp)].
apply (in_allen_inter ttInJ LL RR).
Qed.

Lemma up_os_upr (p q:sig) (t:nat) : (up (occurs (sync p q) q) t) -> (up q t).
intros (GT0c,(I,(LI,IInO))).
split;[auto|].
exists I; split;[auto|].
apply (inc_sig_allen_filter IInO).
Qed.

Lemma up_os_os (p q:sig) (t:nat) : 
 (up (occurs (sync p q) q) t) ->
 (occurs (sync p q) q t).
intros UP.
apply (up_in UP).
Qed.

Lemma up_os_up (p q:sig) (t:nat) :
 (up q t) ->
 (occurs (sync p q) q t) ->
 (up p t).
intros UQ (J,(tJq,(t2,(t2InJ,(UP2,UQ2))))).
rewrite (up_shared tJq t2InJ UQ UQ2); auto.
Qed.

Lemma up_os_upl (p q:sig) (t:nat) : (up (occurs (sync p q) q) t) -> (up p t).
intros UPO.
apply (up_os_up (up_os_upr UPO) (up_os_os UPO)).
Qed.


Lemma occurs_sync_shared_left (p q:sig) (I J1 J2:allen) (t2:nat) :
 (tas t2 I p) ->
 (tas (left I) J1 (occurs (sync p q) q)) ->
 (tas t2 J2 (occurs (sync p q) q)) ->
 (left J1)=(left J2).
intros t2Ip t1J1O t2J2O.
G (join_or_up t1J1O t2J2O (allen_left (tas_allen t2Ip))).
intros [EQ | (t,((LT,GT),UP))]; [apply (proj1 EQ)|exfalso].
G (lt_getS LT); intros (pt,PT). rewrite PT in *. clear PT t.
cut (in_allen pt I);[intros ptInI|].
- G (in_sig_slice (tas_sig t2Ip) ptInI).
  G (before_up (up_os_upl UP)); auto.
- split.
    rewrite <- ltS__le; auto.
  + G (allen_right (tas_allen t2Ip)); apply ilt_trans. simpl.
    G GT. apply lt_le_trans. auto.
Qed.

Lemma sync_shared_left__starts (p q:sig) (I J:allen) (t t1:nat) :
 (tas t I p) ->
 (tas t J (occurs (sync p q) q)) ->
 (in_allen t1 I) ->
 (sync p q t1) ->
 (left I)=(left J).
intros tIp tJO t1InI SY.
G (sync_left_first (tas_mov tIp t1InI) SY); intros LI.
rewrite <- LI in *. clear LI t1InI.
G (inc_sig_sync_first (sync_comm SY)); intros qt1.
G (get_sig qt1). intros (J1,t1J1q).
cut (tas (left I) J1 (occurs (sync p q) q)); [intros t1J1O|].
- rewrite <- (occurs_sync_shared_left tIp t1J1O tJO).
  apply (sync__left (tas_left tIp) t1J1q SY).
- apply (filter_tas t1J1q).
  exists (left J1); split;[apply in_allen_left|auto].
  rewrite <- (sync__left (tas_left tIp) t1J1q SY).
  auto.
Qed.


(*
 * OCCURS_UP
 *)
Definition occurs_up (p q:sig) := (occurs (up_after q p) p).

Lemma inc_sig_allen_occurs_up (p q:sig) : (inc_sig_allen (occurs_up p q) p).
  apply inc_sig_allen_filter.
Qed.

Lemma in_sig_occup (p q:sig) (I J:allen) :
 (in_sig I p) ->
 (tas (left I) J q) ->
 0 < (left I) ->
 (not_sig (up q) (left I)) ->
 (in_sig I (occurs_up p q)).
intros Ip ttJq GT0 NUPQtt.
apply (filter_in_sig Ip).
exists (left I). split.
- apply in_allen_left.
- split.
  + split; [assumption|].
    exists I. auto.
  + split;[|assumption].
    apply (tas_p ttJq).
Qed.

Lemma occoccup (p q:sig) (I J:allen) (t:nat) :
 (tas t I p) ->
 (tas (left I) J q) ->
 0 < (left I) ->
 (not_sig (up q) (left I)) ->
 (ilt (right J) (right I)) ->
 (occurs (not_sig q) (occurs_up p q) t).
intros tIp ttJq GT0 NUPQtt LT.
exists I. split;[split|].
- apply (tas_allen tIp).
- apply (in_sig_occup (tas_sig tIp) ttJq GT0 NUPQtt).
- apply (end_before_has_down ttJq LT).
Qed.

Lemma up_after_share_left (p q:sig) (I J:allen) (t l:nat) :
  (tas t I (occurs_up q p)) ->
  (tas t J (and_sig p q)) ->
  (up_after p q l) ->
  (in_allen l J) ->
  l=(left I).
intros tIO tJA ((GT0,(II,(LII,IIInq))),(Pl,NUpl)) lInL.
rewrite LII in *; clear LII l.
G (eq_sig_tas (and_sig_comm p q) tJA). intros tJrA.
G (tas_filter_tas_arg tIO); intros tIq.
G (in_sig_and__inc_allen tJrA tIq).
intros JIncI.
G (JIncI _ lInL). intros lInI.
G (in_allen_left II). intros lInII.
rewrite (tas_uniq_left (tas_def lInI (tas_sig tIq)) (tas_def lInII IIInq)).
auto.
Qed.

Lemma up_after_left (p q:sig) (I:allen) :
 (in_sig I (occurs_up q p)) ->
 (exists K, (in_sig K p)
         /\ (left K)<(left I)
         /\ (ilt (Fix (left I)) (right K)) ).
intros IInO.
cut (exists t, (in_allen t I)/\ (up_after p q t)).
- intros (t,(tInI,((GT0,(II,(LII,IIInq))),(Pt,NUpt)))).
  G (get_sig Pt); intros (K,(tInK,KInp)).
  exists K; split; auto.
  G (in_allen_left II); rewrite <- LII; intros tInII.
  G (tas_uniq_left (tas_def tInII IIInq) (tas_def tInI (inc_sig_allen_occurs_right IInO))).
  intros LILII.
  G (nat_compare (left K) (left I)); intros [OK|[BAD|BAD]].
  + split; auto.
    rewrite <- LILII.
    apply (le_ilt_trans (allen_left tInII) (allen_right tInK)).
  + exfalso.
    G NUpt; apply not_not; unfold up.
    split;[apply GT0|].
    exists K; split;[|auto].
    rewrite BAD, LII; auto.
  + exfalso; G BAD. apply le_not_gt.
    rewrite <- LILII, <- LII; apply (allen_left tInK).
- apply (in_sig_filter IInO).
  intros A B EQ (t,(tInA,UP)).
  exists t; split; [apply (eq_allen_in_allen EQ tInA)|auto].
Qed.

Lemma occurs_up_after_on_left (p q:sig) (I J K:allen) (t u':nat) :
 (tas t I (occurs_up q p)) ->
 (tas t J (and_sig p q)) ->
 (tas t K p) ->
 (in_allen u' J) ->
 (up_after p q u') ->
 (left K)<(left I).
intros tIO tJA tKp u'InJ NPu'.
G (up_after_left (tas_sig tIO)). intros (K2,(K2Inp,(K2I,ILT))).
rewrite (tas_uniq_left (p:=p) (I1:=K) (I2:=K2) (t:=u')); auto.
- apply (tas_mov tKp (in_sig_and__inc_allen tJA tKp u'InJ)).
- split;[split|auto].
  + apply lt_le.
    apply (lt_le_trans _ _ _ K2I).
    G (allen_left u'InJ).
    apply le_trans.
    G (eq_sig_tas (and_sig_comm p q) tJA). intros tJrA.
    G (in_sig_and__inc_allen tJrA (tas_filter_tas_arg tIO)).
    intros JincI.
    apply (allen_left (JincI _ (in_allen_left J))).
  + rewrite (up_after_share_left tIO tJA NPu' u'InJ); auto.
Qed.

Lemma overlaps_occurs_up (p q:sig) (I J:allen) (t:nat) :
 (tas t I p) ->
 (tas t J q) ->
 (left I) < (left J) ->
 (ilt (right I) (right J)) ->
 (tas t J (occurs_up q p)).
intros tIp tJq LIJ RIJ.
split;[apply (tas_allen tJq)|].
split;[|split].
- case_eq (left J); auto; intros lj LJ.
  intros (K,(ljKq,_)).
  G (tas_p ljKq).
  apply (previous_left_out (tas_sig tJq) LJ).
- case_eq (right J); auto; intros ri RJ.
  intros (K,(ljKq,_)).
  G (tas_p ljKq).
  apply (bounded_right_out (tas_sig tJq) RJ).
- intros t' t'InJ; exists J. split; [apply (tas_mov tJq t'InJ)|].
  exists (left J). split;[|].
  + apply in_allen_left.
  + apply (overlaps_up_after_left tIp tJq LIJ RIJ).
    apply (tas_has_intersection tJq tIp).
Qed.







(*
 * AUXILARY ALLEN'S FUNCTIONS
 *)
(*
 * init
 *)
Definition init (p:sig) : sig := (filter (fun I => (left I)=0) p).

(*
 * final
 *)
Definition final (p:sig) : sig := (filter (fun I => (right I)=Inf) p).

Lemma not_final (p:sig) (I:allen) (t:nat) :
 (tas t I p) ->
 (not_sig (final p) t) ->
 (right I)<>Inf.
intros tIp.
apply ncontra; intros RI.
exists I; auto.
Qed.

Lemma not_final_fix_right (p:sig) (I:allen) (t:nat) :
 (tas t I p) ->
 (not_sig (final p) t) ->
 (exists ri, (right I)=(Fix ri)).
intros tIp.
case_eq (right I).
- intros ri RI _. exists ri; auto.
- intros RI NF. exfalso.
  G NF. rewrite not_sig_def. apply tilde. rewrite not_not.
  exists I; auto.
Qed.


(*
 * ALLEN'S FUNCION
 *)
(*
 * MEETS
 *)
Definition Meets (x:allen) (y:allen) : Prop := (right x)=(Fix (left y)).
Definition meets := extend Meets.

Lemma meets_by_end (p q:sig) (I J:allen) (t:nat) :
 (tas t I p) ->
 (in_sig J (not_sig q)) ->
 (right I)=(right J) ->
 (not_sig (final p) t) ->
 (meets p q t).
intros tIp JInNq RI NotF.
exists I. split;[auto|].
G (not_final_fix_right tIp NotF). intros (ri,FRI).
G (previous_right FRI). intros (pri,PRI).
rewrite PRI in *. clear PRI.
rewrite FRI in RI.
G (bounded_right_out JInNq (eq_sym RI)). rewrite not_sig_def, not_not. intros QSri.
G (previous_right_in JInNq (eq_sym RI)); rewrite not_sig_def; intros NQri.
G (up_allen_right NQri QSri); intros (K,(KInq,EQ)).
exists K. split;[auto|unfold Meets; rewrite FRI, EQ; auto].
Qed.

(*
 * MET
 *)
Definition MetBy (x:allen) (y:allen) : Prop := (Fix (left x))=(right y).
Definition met := extend MetBy.

(*
 * EQ
 *)
Definition Eq (x:allen) (y:allen) : Prop := (eq_allen x y).
Definition eq := extend Eq.

Lemma Eq_inc : (inclusive_relation Eq). INC_CMP eq_le2 eq_ile. Qed.

Lemma inc_sig_eq_left (p q r:sig) :
 (inc_sig p (eq q r)) ->
 (inc_sig p q).
intros INC.
apply (inc_sig_trans INC).
apply inc_sig_extend_left.
Qed.

(*
 * STARTS
 *)
Definition Starts (x:allen) (y:allen) : Prop :=
    (left x)=(left y)
 /\ (ilt (right x) (right y)).
Definition starts := extend Starts.

Lemma Starts_inc : (inclusive_relation Starts). INC_CMP eq_le2 ilt_ile. Qed.

(*
 * STARTED
 *)
Definition StartedBy (x:allen) (y:allen) : Prop :=
    (left x)=(left y)
 /\ (ilt (right y) (right x)).
Definition started := extend StartedBy.

Lemma startedBy_Starts (I J:allen) :
 (StartedBy I J) ->
 (Starts J I).
intros (LL,RR); split; auto.
Qed.

(*
 * ENDS
 *)
Definition Ends (x:allen) (y:allen) : Prop :=
    (left y)<(left x)
 /\ (right x)=(right y).
Definition ends := extend Ends.

Lemma ends_safe : (safe_allen_relation Ends). SAFE_ALLEN_RELATION2. Qed.

Lemma Ends_inc : (inclusive_relation Ends). INC_CMP lt_le eq_ile. Qed.

(*
 * ENDED
 *)
Definition EndedBy (x:allen) (y:allen) : Prop :=
    (left x)<(left y)
 /\ (right x)=(right y).
Definition ended := extend EndedBy.

Lemma EndedBy_inc : (rinclusive_relation EndedBy). RINC_CMP lt_le eq_ile2. Qed.

(*
 * OVERALAPS
 *)
Definition Overlaps (x:allen) (y:allen) : Prop :=
    (left x)<(left y)
 /\ (ilt (Fix (left y)) (right x))
 /\ (ilt (right x) (right y)).
Definition overlaps := extend Overlaps.

(*
 * OVERLAPPED
 *)
Definition OverlappedBy (x:allen) (y:allen) : Prop :=
    (left y)<(left x)
 /\ (ilt (Fix (left x)) (right y))
 /\ (ilt (right y) (right x)).
Definition overlapped := extend OverlappedBy.
 
(*
 * DURING
 *)
Definition During (x:allen) (y:allen) : Prop :=
    (left y)<(left x)
 /\ (ilt (right x) (right y)).
Definition during := extend During.

Lemma During_inc_allen (I J:allen) : (During I J) -> (inc_allen I J).
intros (LL,RR).
apply (left_right_inc_allen (lt_le LL) (ilt_ile RR)).
Qed.

Lemma During_safe : (safe_allen_relation During). SAFE_ALLEN_RELATION2. Qed.

Lemma During_inc : (inclusive_relation During). INC_CMP lt_le ilt_ile. Qed.

Lemma eq_right_during (I J1 J2:allen) :
 (eq_allen J1 J2) ->
 (During I J1) ->
 (During I J2).
intros (LL,RR) (L1,R1). rewrite LL in L1. rewrite RR in R1.
split; auto.
Qed.

Lemma During_in_allen_left (I J:allen) :
  (During I J) ->
  (in_allen (left I) J).
intros DRG.
apply (inc_allen_in_allen_left (During_inc DRG)).
Qed.



(*
 * CONTAINS
 *)
Definition Contains (x:allen) (y:allen) : Prop :=
    (left x)<(left y)
 /\ (ilt (right y) (right x)).
Definition contains := extend Contains.

Lemma contains_has_left (I J:allen) : (Contains I J) -> (in_allen (left J) I).
intros (LL,RR).
split;[apply (lt_le LL) | apply (ilt_trans (wf J) RR)].
Qed.

Lemma During_Contains (I J:allen) : (During I J) -> (Contains J I).
auto.
Qed.

Lemma Contains_During (I J:allen) : (Contains I J) -> (During J I).
auto.
Qed.

(*
 * OVER
 *)
Definition over (p q:sig) : sig := fun t =>
  (exists I, (tas t I p)
          /\ (exists J, (tas t J q)
                     /\ ((left I) < (left J))
                     /\ (ilt (right I) (right J)) )).

Lemma ends_fix_over (p q:sig) (I J:allen) (t ri:nat) :
 (tas t I p) ->
 (tas t J q) ->
 (left J)<(left I) ->
 (right I)=(right J) ->
 (right I)=(Fix ri) ->
 (over q (imp_sig q p) t).
intros tIp tJq LL RR RI.
exists J. split;[auto|].
G (get_sig (or_sig_right (not_sig q) (tas_p tIp))). intros (K,tKO).
exists K. split;[auto|split].
- apply (in_sig_imp_left tIp tJq tKO LL RR RI).
- apply (in_sig_imp_right tIp tJq tKO LL RR RI).
Qed.


End allenfuns.
