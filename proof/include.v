Set Implicit Arguments.
Unset Strict Implicit.

Require Import basics.
Require Import enat.
Require Import allen.
Require Import signal.
Require Import compare.


Section include.

Ltac G x := generalize x.

Ltac BAD := intros BAD; inversion BAD.


(* *)
Lemma eq_sig_in_sig_l (p q:sig) (I:allen) :
 (eq_sig p q) ->
 (in_sig I p) ->
 (in_sig I q).
intros EQ IInp.
split;[|split].
- case_eq (left I); [auto|intros pl LI].
  rewrite <- (EQ pl).
  apply (previous_left_out IInp LI).
- case_eq (right I); [intros r RI|auto].
  rewrite <- (EQ r).
  apply (bounded_right_out IInp RI).
- intros t tInI.
  G (in_sig_slice IInp tInI).
  rewrite (EQ t); auto.
Qed.

Lemma eq_sig__in_sig (p q:sig) (I:allen) :
 (eq_sig p q) ->
 ((in_sig I p) <-> (in_sig I q)).
intros EQ.
split.
- apply (eq_sig_in_sig_l EQ).
- rewrite eq_sig_sym in EQ.
  apply (eq_sig_in_sig_l EQ).
Qed.

End include.



