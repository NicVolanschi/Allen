Set Implicit Arguments.
Unset Strict Implicit.

Require Import basics.
Require Import enat.

Section allen.

Ltac G x := generalize x.

Ltac BAD := intros BAD; inversion BAD.

(*
 * Allen
 *)
Record allen : Type := {
 left : nat;
 right : inat;
 wf : ilt (Fix left) right
}.

(* TBR *)
Definition make_allen (m:nat) (M:inat) (H:(ilt (Fix m) M)) :=
 {| left:=m; right:=M; wf:=H |}.

Definition eq_allen (I J:allen) := (left I)=(left J) /\ (right I)=(right J).

Definition in_allen (t:nat) (I:allen) : Prop := 
 ((left I)<=t) /\ (ilt (Fix t) (right I)).

Definition inc_allen (I J:allen) :=
  (forall t, (in_allen t I) -> (in_allen t J)).

Definition safe_allen_fun (f:allen->Prop) := forall (I J:allen),
 (eq_allen I J) -> (f I) -> (f J).

Lemma allen_right_gt0 (I:allen) : (ilt (Fix 0) (right I)).
G (wf I).
case (right I) as [n|]; simpl; [omega|auto].
Qed.

Lemma previous_right (I:allen) (n:nat) :
 (right I)=(Fix n) ->
 (exists pn, n=(S pn)).
intros RI. G (allen_right_gt0 I). rewrite RI.
case n as [|n]; [BAD|exists n; auto].
Qed.


(* eq_allen *)
Lemma eq_allen_def (I J:allen) :
 (left I)=(left J) ->
 (right I)=(right J) ->
 (eq_allen I J).
split; auto.
Qed.

Lemma eq_allen_refl (I:allen) : (eq_allen I I).
split; auto.
Qed.

Lemma eq_allen_sym I J : (eq_allen I J) -> (eq_allen J I).
intros (LL,RR); split; auto.
Qed.

Lemma eq_allen_trans I J K : (eq_allen I J) -> (eq_allen J K) -> (eq_allen I K).
intros (LL1,RR1) (LL2,RR2); split; [rewrite LL1|rewrite RR1]; auto.
Qed.

(* in_allen *)
Lemma in_allen_def (I:allen) (t:nat) :
 ((left I)<=t) ->
 (ilt (Fix t) (right I)) ->
 (in_allen t I).
split; auto.
Qed.

Lemma allen_left t I : (in_allen t I) -> (left I) <= t.
intros (OK,_); auto.
Qed.

Lemma allen_right t I : (in_allen t I) -> (ilt (Fix t) (right I)).
intros (_,OK); auto.
Qed.

Lemma in_allen_left (I:allen) : (in_allen (left I) I).
split;[auto|apply (wf I)].
Qed.

Lemma in_allen_previous_right (I:allen) (r:nat) : 
 (right I)=(Fix (S r)) ->
 (in_allen r I).
intros RI.
split.
- G (wf I). rewrite RI. simpl. omega.
- rewrite RI. simpl. omega.
Qed.

(* inc_allen *)
Definition inclusive_relation (R:(allen->allen->Prop)) := forall I J,
 (R I J) -> (inc_allen I J).

Definition rinclusive_relation (R:(allen->allen->Prop)) := forall I J,
 (R I J) -> (inc_allen J I).

Lemma inc_allen_has_left (I J:allen) : (inc_allen I J) -> (in_allen (left I) J).
intros INC.
apply (INC (left I) (in_allen_left I)).
Qed.

Lemma inc_allen_by_comp (I J:allen) :
 (left J) <= (left I) ->
 (ilt (right I) (right J)) ->
 (inc_allen I J).
intros LL RR t tInI.
split.
apply (le_trans _ _ _ LL (allen_left tInI)).
apply (ilt_trans (allen_right tInI) RR).
Qed.

Lemma inc_allen_by_comp2 (I J:allen) :
 (left J) <= (left I) ->
 (ile (right I) (right J)) ->
 (inc_allen I J).
intros LL RR t tInI.
split.
apply (le_trans _ _ _ LL (allen_left tInI)).
apply (ilt_ile_trans (allen_right tInI) RR).
Qed.

Ltac INC_CMP CV1 CV2 :=
  intros I J (LL,RR);
  apply (inc_allen_by_comp2 (CV1 _ _ LL) (CV2 _ _ RR)).

Ltac RINC_CMP CV1 CV2 :=
  intros I J (LL,RR);
  apply (inc_allen_by_comp2 (CV1 _ _ LL) (CV2 _ _ RR)).

Lemma in_allen_inter (I J:allen) (t:nat) :
 (in_allen t I) ->
 (left J) <= (left I) ->
 (ile (right I) (right J)) ->
 (in_allen t J).
intros tInI LL RR.
split.
- apply (le_trans _ _ _  LL (allen_left tInI)).
- apply (ilt_ile_trans (allen_right tInI) RR).
Qed.

Lemma inc_allen_in_allen_left (I J:allen) :
 (inc_allen I J) ->
 (in_allen (left I) J).
intros IJ.
apply (IJ (left I) (in_allen_left I)).
Qed.

Lemma inc_allen_left (I J:allen) :
 (inc_allen I J) ->
 (left J)<=(left I).
intros IJ.
apply (allen_left (inc_allen_in_allen_left IJ)).
Qed.

Lemma inc_allen_in_allen_right (I J:allen) (pr:nat) :
 (inc_allen I J) ->
 (right I)=(Fix (S pr)) ->
 (in_allen pr J).
intros IJ RI.
apply (IJ pr (in_allen_previous_right RI)).
Qed.


Lemma inc_allen_refl I J : (eq_allen I J) -> (inc_allen I J).
intros (LL,RR) t (LE,LT). rewrite LL in *; rewrite RR in *.
apply (in_allen_def LE LT).
Qed.

Lemma eq_allen_in_allen t I J :
 (eq_allen I J) ->
 (in_allen t I) ->
 (in_allen t J).
intros EQ IN.
apply (inc_allen_refl EQ IN).
Qed.

Lemma inc_allen_in_allen (I J:allen) (t:nat) :
 (inc_allen I J) ->
 (in_allen t I) ->
 (in_allen t J).
intros INC tI.
apply (INC t tI).
Qed.

Lemma eq_right_inc_allen (I J1 J2:allen) :
 (eq_allen J1 J2) ->
 (inc_allen I J1) ->
 (inc_allen I J2).
intros EQ INC t tI.
apply (eq_allen_in_allen EQ (INC t tI)).
Qed.

Lemma eq_left_inc_allen (I1 I2 J:allen) :
 (eq_allen I1 I2) ->
 (inc_allen I1 J) ->
 (inc_allen I2 J).
intros EQ INC t tI2.
apply (INC t (eq_allen_in_allen (eq_allen_sym EQ) tI2)).
Qed.

Lemma eq_inc_allen (I1 I2 J1 J2:allen) :
 (eq_allen I1 I2) ->
 (eq_allen J1 J2) ->
 (inc_allen I1 J1) ->
 (inc_allen I2 J2).
intros EQ1 EQ2 INC.
apply (eq_right_inc_allen EQ2 (eq_left_inc_allen EQ1 INC)).
Qed.

Ltac Easy := simpl;(try auto);(try auto with arith);(try omega).

Lemma inc_allen_first_inf (I J:allen) :
 (inc_allen I J) ->
 (right I)=Inf ->
 (right J)=Inf.
intros INC RI.
case_eq (right J); [intros rj RJ;exfalso | auto].
G (nat_compare_le_lt (left I) rj); intros [LE|GT].
- cut (in_allen rj J);[|apply INC; apply (in_allen_def LE); rewrite RI; Easy].
  intros RjJ; G (allen_right RjJ).
  rewrite RJ; apply ilt_irrefl.
- G (allen_right (INC (left I) (in_allen_left I))).
  rewrite RJ; simpl; omega.
Qed.

Lemma inc_allen_right (I J:allen) :
 (inc_allen I J) ->
 (ile (right I) (right J)).
intros IJ.
case_eq (right I); [intros rI | ]; intros RI;
case_eq (right J); [intros rJ| | intros rJ | ]; intros RJ; simpl.
- G (previous_right RI); intros (pr,PRI). rewrite PRI in *; clear PRI.
  G (IJ pr (in_allen_previous_right RI)).
  intros (_,OK). rewrite RJ in OK.
  apply (ilt_ileS OK).
- apply ile_inf.
- cut (in_allen rJ I).
  + intros rJInI; G (IJ rJ rJInI).
    intros (_,BAD). rewrite RJ in BAD. simpl in BAD.
    exfalso. apply (lt_irrefl _ BAD).
  + G RJ; rewrite (inc_allen_first_inf IJ RI).
    BAD.
- apply ile_inf.
Qed.

Lemma left_right_inc_allen (I J:allen) :
 ((left J) <= (left I)) ->
 (ile (right I) (right J)) ->
 (inc_allen I J).
intros LEL ILER t (LEt,LTt).
split.
- apply (le_trans _ _ _ LEL LEt).
- apply (ilt_ile_trans LTt ILER).
Qed.

Lemma inc_allen_asym (I J:allen) :
 (inc_allen I J) ->
 (inc_allen J I) ->
 (eq_allen I J).
intros IJ JI.
split.
- apply (le_antisym _ _ (inc_allen_left JI) (inc_allen_left IJ)).
- apply (ile_antisym (inc_allen_right IJ) (inc_allen_right JI)).
Qed.

(* TBR
Lemma eq_allen_in_allen t I J :
 (eq_allen I J) ->
 (in_allen t I) ->
 (in_allen t J).
intros EQ IN.
apply (inc_allen_refl EQ IN).
Qed.
 *)
(* TBR
Lemma in_allen_on_equiv_allen (t:nat) (I J:allen) :
 (left I)=(left J) ->
 (right I)=(right J) ->
 (in_allen t I) ->
 (in_allen t J).
intros LL RR IN.
apply (inc_allen_refl (eq_allen_def LL RR) IN).
Qed.
 *)
Lemma wf_shift (T:nat) (I:allen) : (ilt (Fix (T+(left I))) (fiadd T (right I))).
G (wf I).
case (right I);simpl;[auto with arith|auto].
Qed.

Lemma allen_has_intersection (I J:allen) (t:nat) :
 (in_allen t I) ->
 (in_allen t J) ->
 (ilt (Fix (left I)) (right J)).
intros (LE1,RI1) (LE2,RI2).
apply (le_ilt_trans LE1 RI2).
Qed.


Lemma in_allen_by_include (I J:allen) (t:nat) :
 (in_allen t I) ->
 (left J)<=(left I) ->
 (ile (right I) (right J)) ->
 (in_allen t J).
intros (LE,RI) LELL LERR.
split.
- apply (le_trans _ _ _ LELL LE).
- apply (ilt_ile_trans RI LERR).
Qed.

Lemma in_allen_by_include_right (I J:allen) (t:nat) :
 (in_allen t I) ->
 (left I)=(left J) ->
 (ilt (right I) (right J)) ->
 (in_allen t J).
intros tInI LL LTRR.
apply (in_allen_by_include tInI).
- rewrite LL; auto.
- apply (ilt_ile LTRR).
Qed.

Lemma in_allen_by_include_left (I J:allen) (t:nat) :
 (in_allen t I) ->
 (left J)<(left I) ->
 (right I)=(right J) ->
 (in_allen t J).
intros tInI LTLL RR.
apply (in_allen_by_include tInI).
- apply (lt_le LTLL).
- rewrite RR; auto.
  apply ile_refl.
Qed.

End allen.
