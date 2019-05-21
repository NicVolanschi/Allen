(*
 * Proofs of equivalences using until and since
 *
 * Bernard P. Serpette
 * Nic Volanschi
 *)
Set Implicit Arguments.
Unset Strict Implicit.

Require Import basics.
Require Import enat.
Require Import allen.
Require Import signal.
Require Import compare.
Require Import include.
Require Import borders.
Require Import extend.
Require Import allenfuns.

Section spec.

Ltac G x := generalize x.

Ltac BAD := intros BAD; inversion BAD.

(* tactic *)
Ltac CONTRA NAME1 NAME2 :=
  rewrite <- not_not; intros NAME1; G NAME2; apply not_not.

(* basics *)
Lemma and_not_or_not P Q : (~P /\ ~Q) -> ~(P \/ Q).
tauto.
Qed.

Lemma not_or__and_not P Q : ~(P \/ Q) <-> (~P /\ ~Q).
tauto.
Qed.

Lemma le0 x : (x <= 0) -> (x = 0).
auto with arith.
Qed.

Lemma ltS x : (x < (S x)).
auto.
Qed.

Lemma ltS_le x y : (x < S y) -> (x <= y).
  auto with arith.
Qed.

Lemma le_ltS x y : (x <= y) -> (x < (S y)). auto with arith. Qed.

Lemma lt_nle x y : (x < y) -> ~(y <= x). auto with arith. Qed.

Lemma le_nlt x y : (x <= y) -> ~(y < x). auto with arith. Qed.

Lemma nlt_le x y : ~(x < y) -> (y <= x).
  apply le__not_lt.
Qed.

Lemma nilt_ile x y : ~ (ilt x y) -> (ile y x).
rewrite ilt__not_ile. tauto.
Qed.

Lemma le_ile x y : (x <= y) -> (ile (Fix x) (Fix y)).
apply ile_fix.
Qed.

Lemma ilt_lt x y : (ilt (Fix x) (Fix y)) -> (x < y).
  auto.
Qed.

(* enat *)

Lemma ile_inf_left x : (ile Inf x) -> (x=Inf).
intros [LT|EQ].
- exfalso. apply (not_ilt_inf_left LT).
- auto.
Qed.  

Lemma ilt_nile x y : (ilt x y) -> ~(ile y x).
rewrite ilt__not_ile. tauto.
Qed.

Lemma ile_nilt x y : (ile x y) -> ~(ilt y x).
rewrite ilt__not_ile. tauto.
Qed.

(* allen *)

(* signal *)
Lemma in_sig_on (I:allen) (p:sig) : (in_sig I p) -> (on I p).
  intros IN t.
  apply (in_sig_slice IN).
Qed.

Lemma tas_before_left t I p pLI :
  (tas t I p) ->
  (left I)=(S pLI) ->
  (ilt (Fix pLI) (Fix t)).
intros tIp PLI. simpl.
G (allen_left (tas_allen tIp)); apply lt_le_trans.
rewrite PLI; auto.
Qed.

Lemma sig_has t I p :
  (in_sig I p) ->
  (in_allen t I) ->
  (p t).
intros Ip tI.
apply (tas_p (tas_def tI Ip)).
Qed.

Lemma tas_has t I p x :
  (tas t I p) ->
  (in_allen x I) ->
  (p x).
intros tIp xI.
apply (tas_p (tas_mov tIp xI)).
Qed.

Lemma tas_ilt_right t I p : (tas t I p) -> (ilt (Fix t) (right I)).
intros tIp.
apply (allen_right (tas_allen tIp)).
Qed.

Lemma tas_le_left t I p : (tas t I p) -> (left I) <= t.
intros tIp.
apply (allen_left (tas_allen tIp)).
Qed.

Lemma tas_before t I p x y :
  (tas t I p) ->
  (t <= x) ->
  y < (left I) ->
  y <= x.
intros tIp LE LL.
G LE; apply le_trans.
G (tas_le_left tIp). apply le_trans.
apply lt_le. auto.
Qed.

Lemma not_on I p :
  ~(on I p) ->
  (exists t, (in_allen t I) /\ ~(p t)).
unfold on.
intros NA.  
G (not_all_ex_not _ _ NA). clear NA.
intros (t,NI). exists t.
apply (not_imply_and NI).
Qed.

Lemma tas_out_on_left t t0 I p :
  (tas t I p) ->
  (t0 <= t) ->
  (not_sig p t0) ->
  (t0 < left I).
intros tIp LE nPt0.
rewrite <- not_not, <- le__not_lt. intros LE2.
G nPt0.
apply not_not.
apply (tas_has tIp). split;[auto|].
G (tas_ilt_right tIp). apply ile_ilt_trans.
apply (le_ile LE).
Qed.

Lemma tas_out_on_right t t0 I p :
  (tas t I p) ->
  (t <= t0) ->
  (not_sig p t0) ->
  (ile (right I) (Fix t0)).
intros tIp LE nPt0.
rewrite ile__not_ilt.  
intros LT.
G nPt0. apply not_not.
apply (tas_has tIp). split;[|auto].
G LE. apply le_trans.
apply (tas_le_left tIp).
Qed.

Lemma strict_border_right t0 t1 p :
  (not_sig p t1) ->
  (p t0) ->
  (t1 <= t0) ->
  (t1 < t0).
rewrite le_fix_def.
intros nPt1 Pt0 [LT|EQ]; [auto|exfalso].
G nPt1. apply not_not. rewrite EQ. auto.
Qed.

Lemma strict_border_left t0 t1 p :
  (not_sig p t0) ->
  (p t1) ->
  (t1 <= t0) ->
  (t1 < t0).
rewrite le_fix_def.
intros nPt1 Pt0 [LT|EQ]; [auto|exfalso].
G nPt1. apply not_not. rewrite <- EQ. auto.
Qed.

Lemma has_before_right t I p :
  (in_sig I p) ->
  (right I)=(Fix (S t)) ->
  (p t).
intros Ip RI.
apply (sig_has Ip).
split.
- rewrite <- ltS__le.
  apply ilt_lt. rewrite <- RI.
  apply (wf I).
- rewrite RI.
  apply lt_ilt. auto.
Qed.

Lemma in_allen_last_is_left (p:sig) (I:allen) (t:nat) :
 (tas (S t) I p) ->
 ~(p t) ->
 (left I)=(S t).
intros StIp nPt.
G (up_allen_right nPt (tas_p StIp)).
intros (II,(IIp,LI)).
G (in_allen_left II). rewrite LI. intros IN.
rewrite (tas_uniq_left StIp (tas_def IN IIp)). auto.
Qed.

(* signal : concerne les slices *)

Lemma empty_slice b P : (forall x, (b < x) -> (x <= b) -> (P x)).
intros x LT LE.
exfalso.
G LE.
apply lt_not_le. auto.
Qed.

Lemma sing_slice_r b P :
  (P (S b)) ->
  (forall x, (b < x) -> (x <= (S b)) -> (P x)).
intros x PS LT LE.
rewrite (le_antisym _ _ LE (lt_leS LT)). auto.
Qed.

Lemma sing_slice_l b P :
  (P b) ->
  (forall x, (b <= x) -> (x < (S b)) -> (P x)).
intros x PS LE LT.
rewrite <- (le_antisym _ _ LE (ltS_le LT)). auto.
Qed.

Lemma close_lr_lr b e P :
  (forall x, (b <= x) -> (x <= e) -> (P x)) ->
  (forall x, (b < x) -> (x < e) -> (P x)).
intros H x LT1 LT2.
apply (H _ (lt_le LT1) (lt_le LT2)).
Qed.

Lemma close_lr_l b e P :
  (forall x, (b <= x) -> (x <= e) -> (P x)) ->
  (forall x, (b < x) -> (x <= e) -> (P x)).
intros H x LT1 LT2.
apply (H _ (lt_le LT1) LT2).
Qed.

Lemma close_rS_r b e P :
  (forall x, (b <= x) -> (x < (S e)) -> (P x)) ->
  (forall x, (b < x) -> (x <= e) -> (P x)).
intros H x LT1 LT2.
apply (H _ (lt_le LT1) (le_ltS LT2)).
Qed.

Lemma extend_slice_close_right b e (P:nat -> Prop) :
  (P e) ->
  (forall x, (b < x) -> (x < e) -> (P x)) ->
  (forall x, (b < x) -> (x <= e) -> (P x)).
intros Pe SL x LT LE.
rewrite le_fix_def in LE. G LE. clear LE. intros [LT2|EQ].
- apply (SL _ LT LT2).
- rewrite EQ; auto.
Qed.

Lemma extend_slice_open_right b e (P:nat -> Prop) :
  (P e) ->
  (forall x, (b <= x) -> (x < e) -> (P x)) ->
  (forall x, (b <= x) -> (x <= e) -> (P x)).
intros Pe SL x LT LE.
rewrite le_fix_def in LE. G LE. clear LE. intros [LT2|EQ].
- apply (SL _ LT LT2).
- rewrite EQ; auto.
Qed.


Lemma tas_in_slice_right t t0 I p :
  (tas t I p) ->
  (ile (Fix t0) (right I)) ->
  (forall x, (t <= x) -> (x < t0) -> (p x)).
intros tIp LT0 x LE LT.
apply (tas_has tIp).
split.
- G LE. apply le_trans.
  apply (tas_le_left tIp).
- G LT0. apply ilt_ile_trans.
  apply (lt_ilt LT).
Qed.

Lemma tas_in_slice_left t t0 I p :
  (tas t I p) ->
  ((left I) <= t0) ->
  (forall x, (t0 <= x) -> (x <= t) -> (p x)).
intros tIp LT0 x LT LE.
apply (tas_has tIp).
split.
- G LT. apply le_trans. auto.
- G (tas_ilt_right tIp). apply ile_ilt_trans.
  apply (le_ile LE).
Qed.

Lemma tas_in_slice_right_right t I J p :
  (tas t I p) ->
  (ile (right J) (right I)) ->
  (forall x, (t <= x) -> (x < (left J)) -> (p x)).
intros tIp RR.
apply (tas_in_slice_right tIp).
G RR. apply ile_trans.
apply (ilt_ile (wf J)). 
Qed.

Lemma tas_in_slice_left_left t I J p :
  (tas t I p) ->
  ((left I) < (left J)) ->
  (forall x, ((left J) < x) -> (x <= t) -> (p x)).
intros tIp LL.
apply close_lr_l.
apply (tas_in_slice_left tIp).
apply (lt_le LL).
Qed.



Lemma extend_right_until t0 t (q:sig) :
  t <= t0 ->
  (q t0) ->
  (forall x, t <= x -> x < t0 -> q x) ->
  (q t).
intros LE. rewrite le_fix_def in LE. G LE. clear LE.
intros [LT|EQ] Qt0 On.
- apply On;auto.
- rewrite EQ; auto.
Qed.

Lemma extend_left_since t0 t (q:sig) :
  t0 <= t ->
  (q t0) ->
  (forall x, t0 < x -> x <= t -> q x) ->
  (q t).
intros LE. rewrite le_fix_def in LE. G LE. clear LE.
intros [LT|EQ] Qt0 On.
- apply On;auto.
- rewrite <- EQ; auto.
Qed.



Lemma tas_follow_right t t' I p :
  (tas t I p) ->
  (forall x, (t < x) -> (x <= t') -> (p x)) ->
  (ilt (Fix t') (right I)).
apply in_allen_in_sig_follow_right.
Qed.

Lemma tas_follow_left (p:sig) (I:allen) (t t':nat) :
 (tas t I p) ->
 (forall x, (t'<=x) -> (x<t) -> (p x)) ->
 ((left I) <= t').
intros tIp Slice.
case_eq (left I); [intros LI | intros lI LI];[auto with arith|].
rewrite le__not_lt. intros LT.
G (previous_left_out (tas_sig tIp) LI). apply not_not.
apply Slice;[|].
- rewrite <- ltS__le; auto.
- G (allen_left (tas_allen tIp)).
  rewrite LI.
  apply leS_lt.
Qed.  

Lemma tas_follow_left_eq t t' I p :
  (tas t I p) ->
  (forall x, (t' < x) -> (x <= t) -> (p x)) ->
  ((left I) <= (S t')).
intros tIp Onp.
apply (tas_follow_left tIp).
intros xx LE2 LT2.
apply Onp.
+ apply (leS_lt LE2).
+ apply (lt_le LT2).
Qed.

Lemma tas_follow_right_eq t t' I p :
  (tas t I p) ->
  (forall x, (t <= x) -> (x < t') -> (p x)) ->
  (ile (Fix t') (right I)).
intros tIp Onp.
case_eq t';[intros; apply ile0|].
intros pt PT.
apply ilt_ileS.
apply (tas_follow_right tIp).
intros xx LT2 LE2.
apply Onp.
+ apply (lt_le LT2).
+ rewrite PT, ltS__le. auto.
Qed.

Lemma not_before_slice p t t1 t2 :
  (not_sig p t2) ->
  (t2 <= t) ->
  (forall x, (t1 < x) -> (x <= t) -> (p x)) ->
  (t2 <= t1).
intros nPt2 LE2 ON.
rewrite le__not_lt. intros LT.
G nPt2. apply not_not.
apply (ON _ LT LE2).
Qed.

Lemma not_after_slice p t t1 t2 :
  (not_sig p t1) ->
  (t <= t1) ->
  (forall x, (t <= x) -> (x < t2) -> (p x)) ->
  (t2 <= t1).
intros nPt1 LE1 ON.
rewrite le__not_lt. intros LT.
G nPt1. apply not_not.
apply (ON _ LE1 LT).
Qed.


Lemma tas_move_on_right t0 t I p :
  (tas t0 I p) ->
  (t0 <= t) ->
  (forall x, (t0 < x) -> (x <= t) -> (p x)) ->
  (tas t I p).
intros t0Ip LE On.
split;[split|apply (tas_sig t0Ip)].
- G LE. apply le_trans.
  apply (tas_le_left t0Ip).
- apply (tas_follow_right t0Ip On).
Qed.

Lemma tas_move_on_left t0 t I p :
  (tas t0 I p) ->
  (t <= t0) ->
  (forall x, (t <= x) -> (x < t0) -> (p x)) ->
  (tas t I p).
intros t0Ip LE On.
split;[split|apply (tas_sig t0Ip)].
- apply (tas_follow_left t0Ip On).
- G (tas_ilt_right t0Ip). apply ile_ilt_trans.
  apply (le_ile LE).
Qed.
  
Lemma tas_moved_left t0 t I p :
  (tas t0 I p) ->
  (t <= t0) ->
  (forall x, (t <= x) -> (x < t0) -> (p x)) ->
  (tas t I p).
intros t0Ip LE On.
split;[split|apply (tas_sig t0Ip)].
- apply (tas_follow_left t0Ip On).
- G (tas_ilt_right t0Ip). apply ile_ilt_trans.
  apply (le_ile LE).
Qed.


(* signal : les slices ouverts *)

Lemma tas_open_left t I p :
  (tas t I p) ->
  (forall x, (x <= t) -> (p x)) ->
  (left I) = 0.
intros tIp On.
apply le0.
apply (tas_follow_left tIp).
intros x LE LT.
apply On.
apply (lt_le LT).
Qed.

Lemma tas_open_left_inv t I p :
  (tas t I p) ->
  (left I) = 0 ->
  (forall x, (x <= t) -> (p x)).
intros tIp LI x LE.
apply (tas_has tIp).
split.
- rewrite LI. auto with arith.
- G (tas_ilt_right tIp). apply ile_ilt_trans.
  apply (le_ile LE).
Qed.  

Lemma tas_open_right t I p :
  (tas t I p) ->
  (forall x, (t <= x) -> (p x)) ->
  (right I) = Inf.
intros tIp On.
case_eq (right I); auto.
intros n RI.
exfalso.
G (bounded_right_out (tas_sig tIp) RI).
apply not_not.
apply On.
apply lt_le.
G (tas_ilt_right tIp). rewrite RI; auto.
Qed.

Lemma tas_open_right_inv t I p :
  (tas t I p) ->
  (right I) = Inf ->
  (forall x, (t <= x) -> (p x)).
intros tIp RI x LE.
apply (tas_has tIp).
split.
- G LE. apply le_trans.
  apply (tas_le_left tIp).
- rewrite RI. apply ilt__inf.
Qed.  

(* // until:
(p U q)(t) <-> E t’>=t . q(t') & A t’’ in [t, t’) . p(t’) // on considere que [x,x) est vide
*)
Definition Until (p q:sig) : sig :=
  fun t =>
    exists t',
      t <= t' /\
      (q t') /\
      (forall x, (t <= x) -> (x < t') -> (p x))
.

(* // since:
(p S q)(t) <-> E t’<=t . q(t’) & A t’’ in (t’,t] . p(t’)
 *)
Definition Since (p q:sig) : sig :=
  fun t =>
    exists t',
      t' <= t /\
      (q t') /\
      (forall x, (t' < x) -> (x <= t) -> (p x))
.
  
(* // weak until:
(p W q)(t) <-> (p U q)(t) | A t’>=t . p(t’)
 *)
Definition WeakUntil (p q:sig) : sig :=
  fun t =>
    (Until p q t) \/
    (forall t', t <= t' -> (p t')).

(* // weak since:
(p Z q)(t) <-> (p S q) | A t’<=t . p(t’)
 *)
Definition WeakSince (p q:sig) : sig :=
  fun t =>
    (Since p q t) \/
    (forall t', t' <= t -> (p t'))
.

(* frighteq(p,q) = p W ~q *)
Definition frighteq (p q:sig) := (WeakUntil p (not_sig q)).

Lemma tas_tas_frighteq t I p J q :
  (tas t I p) ->
  (tas t J q) ->
  (frighteq p q t) ->
  (ile (right J) (right I)).
intros tIp tJq [(t0,(LE0,(nQt0,Onp)))|Onp].
- G (tas_follow_right_eq tIp Onp). apply ile_trans.
  G (tas_out_on_right tJq LE0 nQt0). apply ile_trans.
  apply ile_refl.
- rewrite (tas_open_right tIp Onp).
  apply ile_inf.
Qed.

Lemma tas_tas_frighteq_inv t I p J q :
  (tas t I p) ->
  (tas t J q) ->
  (ile (right J) (right I)) ->
  (frighteq p q t).
intros tIp tJq RR.
case_eq (right J); [intros rJ RJ;left| intros RJ;right].
- exists rJ. split;[|split].
  + G (tas_ilt_right tJq).
    rewrite RJ. apply lt_le.
  + apply (bounded_right_out (tas_sig tJq) RJ).
  + apply (tas_in_slice_right tIp).
    rewrite <- RJ; auto.
- rewrite RJ in RR.
  apply (tas_open_right_inv tIp (ile_inf_left RR)).
Qed.

(* flefteq(p,q) = frighteq(q,p) *)
Definition flefteq (p q:sig) := (frighteq q p).

Lemma tas_tas_flefteq t I p J q :
  (tas t I p) ->
  (tas t J q) ->
  (flefteq p q t) ->
  (ile (right I) (right J)).
intros tIp tJq FL.
apply (tas_tas_frighteq tJq tIp FL).
Qed.

Lemma tas_tas_flefteq_inv t I p J q :
  (tas t I p) ->
  (tas t J q) ->
  (ile (right I) (right J)) ->
  (flefteq p q t).
intros tIp tJq LE.
apply (tas_tas_frighteq_inv tJq tIp LE).
Qed.

(* feq(p,q) = flefteq(p,q) & frighteq(p,q) *)
Definition feq (p q:sig) := (and_sig (flefteq p q) (frighteq p q)).

Lemma tas_tas_feq_inv t I p J q :
  (tas t I p) ->
  (tas t J q) ->
  ((right I) = (right J)) ->
  (feq p q t).
intros tIp tJq RR.
split.  
- apply (tas_tas_flefteq_inv tIp tJq).
  rewrite RR. apply ile_refl.
- apply (tas_tas_frighteq_inv tIp tJq).
  rewrite RR. apply ile_refl.
Qed.

(* fleft(p,q) = flefteq(p,q) & ~frighteq(p,q) *)
Definition fleft (p q:sig) := (not_sig (frighteq p q)).

Lemma tas_tas_fleft t I p J q :
  (tas t I p) ->
  (tas t J q) ->
  (fleft p q t) ->
  (ilt (right I) (right J)).
unfold fleft.
intros tIp tJq FL.
CONTRA INV FL.
apply (tas_tas_frighteq_inv tIp tJq).
apply (nilt_ile INV).
Qed.

Lemma tas_tas_fleft_inv t I p J q :
  (tas t I p) ->
  (tas t J q) ->
  (ilt (right I) (right J)) ->
  (fleft p q t).
intros tIp tJq LT.
intros FR; G LT.
apply ile_nilt.
apply (tas_tas_frighteq tIp tJq FR).
Qed.

(* fright(p,q) = frighteq(p,q) & ~flefteq(p,q) *)
Definition fright (p q:sig) := (and_sig (frighteq p q) (not_sig (flefteq p q))).

(* Frighteq(p,q) = p U ~q *)
Definition Frighteq (p q:sig) := (Until p (not_sig q)).

(* Flefteq(p,q) = Frighteq(q,p) *)
Definition Flefteq (p q:sig) := (Frighteq q p).

(* Feq(p,q) = Flefteq(p,q) & Frighteq(p,q) *)
Definition Feq (p q:sig) := (and_sig (Flefteq p q) (Frighteq p q)).


(* brighteq(p,q) = p Z ~q *)
Definition brighteq (p q:sig) := (WeakSince p (not_sig q)).

Lemma tas_tas_brighteq t I p J q :
  (tas t I p) ->
  (tas t J q) ->
  (brighteq p q t) ->
  ((left I) <= (left J)).
intros tIp tJq [(t0,(LE0,(nQt0,Onp)))|Onp].
- G (lt_leS (tas_out_on_left tJq LE0 nQt0)). apply le_trans.
  apply (tas_follow_left_eq tIp Onp).
- rewrite (tas_open_left tIp Onp).
  auto with arith.
Qed.

Lemma tas_tas_brighteq_inv t I p J q :
  (tas t I p) ->
  (tas t J q) ->
  ((left I) <= (left J)) ->
  (brighteq p q t).
intros tIp tJq LL.
unfold brighteq.  
case_eq (left J); [intros LJ; right | intros pLJ LJ; left].
- rewrite LJ in LL.
  apply (tas_open_left_inv tIp (le0 LL)).
- exists pLJ. split;[|split].
  + G (tas_le_left tJq). apply le_trans.
    rewrite LJ; auto.
  + apply (previous_left_out (tas_sig tJq) LJ).
  + apply (tas_in_slice_left tIp).
    rewrite <- LJ; auto.
Qed.

(* blefteq(p,q) = brighteq(q,p) *)
Definition blefteq (p q:sig) := (brighteq q p).

Lemma tas_tas_blefteq t I p J q :
  (tas t I p) ->
  (tas t J q) ->
  (blefteq p q t) ->
  ((left J) <= (left I)).
intros tIp tJq [(t0,(LE0,(nPt0,ONq)))|ONq].
- G (lt_leS (tas_out_on_left tIp LE0 nPt0)). apply le_trans.
  apply (tas_follow_left_eq tJq ONq).
- rewrite (tas_open_left tJq ONq).
  auto with arith.
Qed.

Lemma tas_tas_blefteq_inv t I p J q :
  (tas t I p) ->
  (tas t J q) ->
  ((left J) <= (left I)) ->
  (blefteq p q t).
intros tIp tJq LL.
case_eq (left I); [intros LI; right | intros pLI LI; left].
- rewrite LI in LL.
  apply (tas_open_left_inv tJq  (le0 LL)).
- exists pLI. split;[|split].
  + G (tas_le_left tIp). apply le_trans.
    rewrite LI; auto.
  + apply (previous_left_out (tas_sig tIp) LI).
  + apply (tas_in_slice_left tJq).
    rewrite <- LI; auto.
Qed.

(* beq(p,q) = blefteq(p,q) & brighteq(p,q) *)
Definition beq (p q:sig) := (and_sig (blefteq p q) (brighteq p q)).

Lemma tas_tas_beq_inv t I p J q :
  (tas t I p) ->
  (tas t J q) ->
  ((left I) = (left J)) ->
  (beq p q t).
intros tIp tJq LL.
split.  
- apply (tas_tas_blefteq_inv tIp tJq).
  rewrite LL. apply le_refl.
- apply (tas_tas_brighteq_inv tIp tJq).
  rewrite LL. apply le_refl.
Qed.

(* bleft(p,q) = blefteq(p,q) & ~brighteq(p,q) *)
Definition bleft (p q:sig) := (not_sig (brighteq p q)).

Lemma tas_tas_bleft t I p J q :
  (tas t I p) ->
  (tas t J q) ->
  (bleft p q t) ->
  ((left J) < (left I)).
intros tIp tJq nBR.
CONTRA INV nBR.
apply (tas_tas_brighteq_inv tIp tJq).
apply (nlt_le INV).
Qed.

Lemma tas_tas_bleft_inv t I p J q :
  (tas t I p) ->
  (tas t J q) ->
  ((left J) < (left I)) ->
  (bleft p q t).
intros tIp tJq LL.
intro BR.
G (tas_tas_brighteq tIp tJq BR).
apply (lt_nle LL).
Qed.

(* bright(p,q) = brighteq(p,q) & ~blefteq(p,q) *)
Definition bright (p q:sig) := (not_sig (blefteq p q)).

Lemma tas_tas_bright_inv t I p J q :
  (tas t I p) ->
  (tas t J q) ->
  ((left I) < (left J)) ->
  (bright p q t).
intros tIp tJq LL.
intros BL; G LL.
apply le_nlt.
apply (tas_tas_blefteq tIp tJq BL).
Qed.

(* Brighteq(p,q) = p S ~q *)
Definition Brighteq (p q:sig) := (Since p  (not_sig q)).

(* Blefteq(p,q) = Brighteq(q,p) *)
Definition Blefteq (p q:sig) := (Brighteq q p).

(* Beq(p,q) = Blefteq(p,q) & Brighteq(p,q) *)
Definition Beq (p q:sig) := (and_sig (Blefteq p q) (Brighteq p q)).

(* occurred(p,q) = q S (p & q) *)
Definition occurred (p q:sig) := (Since q (and_sig p q)).

(* possible(p,q) = q U (p & q) *)
Definition possible (p q:sig) := (Until q (and_sig p q)).

(*
 * Equivalences
 *)

(*
Lemma XX_equiv_l (p q:sig) : (inc_sig (XX p q) (XX_new p q)).
Qed.

Lemma XX_equiv_r (p q:sig) : (inc_sig (XX_new p q) (XX p q)).
Qed.

Lemma XX_equiv (p q:sig) : (eq_sig (XX p q) (XX_new p q)).
apply inc_sig_asym;[apply XX_equiv_l|apply XX_equiv_r].
Qed.
 *)

(*
 * During
 *)
Definition during_new (p q:sig) :=
  (and_sig (and_sig (bleft p q) p)
           (and_sig q (fleft p q)) ).
  
Lemma during_equiv_l (p q:sig) : (inc_sig (during p q) (during_new p q)).
intros t (I,(tIp,(J,(Jq,(LL,RR))))).
G (tas_inc_tas tIp Jq (inc_allen_by_comp2 (lt_le LL) (ilt_ile RR))).
intros tJq.
split;[split|split].
- apply (tas_tas_bleft_inv tIp tJq LL).
- apply (tas_p tIp).
- apply (tas_p tJq).
- apply (tas_tas_fleft_inv tIp tJq RR).
Qed.

Lemma during_equiv_r (p q:sig) : (inc_sig (during_new p q) (during p q)).
intros t ((BL,Pt),(Qt,FL)).
G (get_sig Pt); intros (I,tIp).
G (get_sig Qt); intros (J,tJq).
exists I. split;[auto|].
exists J. split;[apply(tas_sig tJq)|].
split.
- apply (tas_tas_bleft tIp tJq BL).
- apply (tas_tas_fleft tIp tJq FL).
Qed.

Lemma during_equiv (p q:sig) : (eq_sig (during p q) (during_new p q)).
apply inc_sig_asym;[apply during_equiv_l|apply during_equiv_r].
Qed.

(*
 * ENDS
 *)
Definition ends_new p q :=
  (and_sig (and_sig (bleft p q) p)
           (and_sig q (feq p q)) ).

Lemma ends_equiv_l (p q:sig) : (inc_sig (ends p q) (ends_new p q)).
intros t (I,(tIp,(J,(Jq,(LL,RR))))).
G (tas_inc_tas tIp Jq (inc_allen_by_comp2 (lt_le LL) (eq_ile RR))).
intros tJq.
split;[split|split].
- apply (tas_tas_bleft_inv tIp tJq LL).
- apply (tas_p tIp).
- apply (tas_p tJq).
- apply (tas_tas_feq_inv tIp tJq RR).
Qed.

Lemma ends_equiv_r (p q:sig) : (inc_sig (ends_new p q) (ends p q)).
intros t ((BL,Pt),(Qt,(FL,FR))).
G (get_sig Pt); intros (I,tIp).
G (get_sig Qt); intros (J,tJq).
exists I. split;[auto|].
exists J. split;[apply(tas_sig tJq)|].
split.
- apply (tas_tas_bleft tIp tJq BL).
- apply (ile_antisym (tas_tas_flefteq tIp tJq FL)
                     (tas_tas_frighteq tIp tJq FR) ).
Qed.

Lemma ends_equiv (p q:sig) : (eq_sig (ends p q) (ends_new p q)).
apply inc_sig_asym;[apply ends_equiv_l|apply ends_equiv_r].
Qed.

(*
 * STARTS
 *)
Definition starts_new p q :=
  (and_sig (and_sig (beq p q) p)
           (and_sig q (fleft p q)) ).

Lemma starts_equiv_l (p q:sig) : (inc_sig (starts p q) (starts_new p q)).
intros t (I,(tIp,(J,(Jq,(LL,RR))))).
G (tas_inc_tas tIp Jq (inc_allen_by_comp2 (eq_le (eq_sym LL)) (ilt_ile RR))).
intros tJq.
split;[split|split].
- apply (tas_tas_beq_inv tIp tJq LL).
- apply (tas_p tIp).
- apply (tas_p tJq).
- apply (tas_tas_fleft_inv tIp tJq RR).
Qed.

Lemma starts_equiv_r (p q:sig) : (inc_sig (starts_new p q) (starts p q)).
intros t (((BL,BR),Pt),(Qt,FL)).
G (get_sig Pt); intros (I,tIp).
G (get_sig Qt); intros (J,tJq).
exists I. split;[auto|].
exists J. split;[apply(tas_sig tJq)|].
split.
- apply (le_antisym _ _ (tas_tas_brighteq tIp tJq BR)
                    (tas_tas_blefteq tIp tJq BL) ).
- apply (tas_tas_fleft tIp tJq FL).
Qed.

Lemma starts_equiv (p q:sig) : (eq_sig (starts p q) (starts_new p q)).
apply inc_sig_asym;[apply starts_equiv_l|apply starts_equiv_r].
Qed.

(*
 * EQ
 *)
Definition eq_new p q :=
  (and_sig (and_sig (beq p q) p)
           (and_sig q (feq p q)) ).

Lemma eq_equiv_l (p q:sig) : (inc_sig (eq p q) (eq_new p q)).
intros t (I,(tIp,(J,(Jq,(LL,RR))))).
G (tas_inc_tas tIp Jq (inc_allen_by_comp2 (eq_le (eq_sym LL)) (eq_ile RR))).
intros tJq.
split;[split|split].
- apply (tas_tas_beq_inv tIp tJq LL).
- apply (tas_p tIp).
- apply (tas_p tJq).
- apply (tas_tas_feq_inv tIp tJq RR).
Qed.

Lemma eq_equiv_r (p q:sig) : (inc_sig (eq_new p q) (eq p q)).
intros t (((BL,BR),Pt),(Qt,(FL,FR))).
G (get_sig Pt); intros (I,tIp).
G (get_sig Qt); intros (J,tJq).
exists I. split;[auto|].
exists J. split;[apply(tas_sig tJq)|].
split.
- apply (le_antisym _ _ (tas_tas_brighteq tIp tJq BR)
                    (tas_tas_blefteq tIp tJq BL) ).
- apply (ile_antisym (tas_tas_flefteq tIp tJq FL)
                     (tas_tas_frighteq tIp tJq FR) ).
Qed.

Lemma eq_equiv (p q:sig) : (eq_sig (eq p q) (eq_new p q)).
apply inc_sig_asym;[apply eq_equiv_l|apply eq_equiv_r].
Qed.

(*
 * OVER
 *)
Definition over_new p q :=
  (and_sig (and_sig (bright p q) p)
           (and_sig q (fleft p q)) ).

Lemma over_equiv_l (p q:sig) : (inc_sig (over p q) (over_new p q)).
intros t (I,(tIp,(J,(tJq,(LL,RR))))).
split;[split|split].
- apply (tas_tas_bright_inv tIp tJq LL).
- apply (tas_p tIp).
- apply (tas_p tJq).
- apply (tas_tas_fleft_inv tIp tJq RR).
Qed.

Lemma over_equiv_r (p q:sig) : (inc_sig (over_new p q) (over p q)).
intros t ((nBL,Pt),(Qt,FL)).
G (get_sig Pt); intros (I,tIp).
G (get_sig Qt); intros (J,tJq).
exists I. split;[auto|].
exists J. split;[auto|].
split.
- CONTRA INV nBL.
  apply (tas_tas_blefteq_inv tIp tJq (nlt_le INV)).
- CONTRA INV FL.
  apply (tas_tas_frighteq_inv tIp tJq (nilt_ile INV)).
Qed.

Lemma over_equiv (p q:sig) : (eq_sig (over p q) (over_new p q)).
apply inc_sig_asym;[apply over_equiv_l|apply over_equiv_r].
Qed.

(*
 * OVERLAPS
 *)
Definition overlaps_new p q := (Until p (over p q)).

Lemma overlaps_equiv_l (p q:sig) : (inc_sig (overlaps p q) (overlaps_new p q)).
intros t (I,(tIp,(J,(Jq,(LL,(LR,RR)))))).
G (ilt_left_is_fix RR). intros (ri,RI).
G LR. rewrite RI. simpl. intros Rri.
G (lt_getS Rri). intros (pt, PT).
exists pt. split;[auto|split].
- G (tas_ilt_right tIp).
  rewrite RI; simpl. rewrite PT. apply ltS_le.
- exists I. split;[|].
  + split;[|apply (tas_sig tIp)].
    split; [|].
    * apply ltS_le.
      apply ilt_lt.
      rewrite <- PT, <- RI.
      apply (ilt_trans (lt_ilt LL) LR).
    * rewrite RI, PT.
      apply lt_ilt. auto.
  + exists J. split;[|split;auto].
    split;[|auto].
    split.
    * apply ltS_le. rewrite <- PT.
      apply ilt_lt. rewrite <- RI. auto.
    * G RR. apply ilt_trans. rewrite RI, PT. simpl. auto.
- apply (tas_in_slice_right tIp).
  rewrite RI, PT. apply le_ile. auto.
Qed.

Lemma overlaps_equiv_r (p q:sig) : (inc_sig (overlaps_new p q) (overlaps p q)).
intros t (t0,(LE0,((I,(t0Ip,(J,(t0Jq,(LL,RR))))),ON))).
exists I. split.
- apply (tas_move_on_left t0Ip LE0 ON).
- exists J. split;[apply (tas_sig t0Jq)|split;auto;split;auto].
  G (tas_ilt_right t0Ip). apply ile_ilt_trans.
  apply (le_ile (tas_le_left t0Jq)).
Qed.

Lemma overlaps_equiv (p q:sig) : (eq_sig (overlaps p q) (overlaps_new p q)).
apply inc_sig_asym;[apply overlaps_equiv_l|apply overlaps_equiv_r].
Qed.


(*
 * OVERLAPPED
 *)
Definition overlapped_new p q := (Since p (over q p)).

Lemma overlapped_equiv_l (p q:sig) : (inc_sig (overlapped p q) (overlapped_new p q)).
intros t (I,(tIp,(J,(Jq,(LL,(LR,RR)))))).
exists (left I). split;[auto|split].
- apply (tas_le_left tIp).
- exists J. split;[|].
  + split;[|auto].
    split;[apply (lt_le LL)|auto].
  + exists I. split;[|split;auto].
    apply (tas_left tIp).
- apply (tas_in_slice_left tIp). auto.
Qed.

Lemma overlapped_equiv_r (p q:sig) : (inc_sig (overlapped_new p q) (overlapped p q)).
intros t (t0,(LE0,((J,(t0Jq,(I,(Ip,(LL,RR))))),ON))).
exists I. split.
- apply (tas_move_on_right Ip LE0 ON).
- exists J. split;[apply (tas_sig t0Jq)|split;auto;split;auto].
  G (tas_ilt_right t0Jq). apply ile_ilt_trans.
  apply (le_ile (tas_le_left Ip)).
Qed.

Lemma overlapped_equiv (p q:sig) : (eq_sig (overlapped p q) (overlapped_new p q)).
apply inc_sig_asym;[apply overlapped_equiv_l|apply overlapped_equiv_r].
Qed.

(*
 * STARTED
 *)
Definition started_new p q := (Since p (starts q p)).

Lemma started_equiv_l (p q:sig) : (inc_sig (started p q) (started_new p q)).
intros t (I,(tIp,(J,(Jq,(LL,RR))))).
exists (left I). split;[auto|split].
- apply (tas_le_left tIp).
- exists J. split;[|].
  + rewrite LL.
    apply (in_sig_tas_left Jq).
  + exists I. split;[apply (tas_sig tIp)|split;auto].
- apply (tas_in_slice_left tIp).
  rewrite LL. auto.
Qed.

Lemma started_equiv_r (p q:sig) : (inc_sig (started_new p q) (started p q)).
intros t (t0,(LE0,((J,(t0Jq,(I,(Ip,(LL,RR))))),ON))).
exists I. split.
- G ON; G LE0; apply tas_move_on_right.
  split;[|auto].
  split.
  + rewrite <- LL.
    apply (tas_le_left t0Jq).
  + G RR. apply ilt_trans.
    apply (tas_ilt_right t0Jq). 
- exists J. split;[apply (tas_sig t0Jq)|split;auto].
Qed.

Lemma started_equiv (p q:sig) : (eq_sig (started p q) (started_new p q)).
apply inc_sig_asym;[apply started_equiv_l|apply started_equiv_r].
Qed.

                       
(*
 * ENDED
 *)
Definition ended_new p q := (Until p (ends q p)).

Definition max (x y:nat) : nat := (Peano.max x y).

Lemma ended_equiv_l (p q:sig) : (inc_sig (ended p q) (ended_new p q)).
intros t (I,(tIp,(J,(Jq,(LL,RR))))).
exists (Peano.max t (left J)). split;[|split].
- auto with arith.
- exists J. split;[|].
  + G (max_spec t (left J)). intros [(LT,M)|(LE,M)]; rewrite M.
    * apply (in_sig_tas_left Jq).
    * split;[|auto].
      split;[auto|].
      rewrite <- RR.
      apply (tas_ilt_right tIp).
  + exists I. split;[apply (tas_sig tIp)|split;auto].
- apply (tas_in_slice_right tIp).
  G (max_spec t (left J)). intros [(LT,M)|(LE,M)]; rewrite M.
  + rewrite RR.
    apply (ilt_ile (wf J)).
  + apply (ilt_ile (tas_ilt_right tIp)).
Qed.

Lemma ended_equiv_r (p q:sig) : (inc_sig (ended_new p q) (ended p q)).
intros t (t0,(LE0,((J,(t0Jq,(I,(Ip,(LL,RR))))),ON))).
exists I. split.
- G ON; G LE0; apply tas_move_on_left.
  split;[|auto].
  split.
  + G (tas_le_left t0Jq). apply le_trans.
    apply (lt_le LL).
  + rewrite <- RR.
    apply (tas_ilt_right t0Jq). 
- exists J. split;[apply (tas_sig t0Jq)|split;auto].
Qed.

Lemma ended_equiv (p q:sig) : (eq_sig (ended p q) (ended_new p q)).
apply inc_sig_asym;[apply ended_equiv_l|apply ended_equiv_r].
Qed.




(*
 * MEETS
 *)
Definition meets_new p q :=
  (Until p (and_sig (and_sig p (not_sig q)) (Feq p (not_sig q)))).

Lemma meets_equiv_l (p q:sig) : (inc_sig (meets p q) (meets_new p q)).
intros t (I,(tIp,(J,(Jq,ME)))).
unfold Meets in ME.
G (previous_right ME). intros (pt,LJ). rewrite LJ in *.
exists pt. split;[|split;[split;[split|split]|]].
- apply ltS_le.
  G (tas_ilt_right tIp).
  rewrite ME. apply lt_ilt.
- apply (has_before_right (tas_sig tIp) ME).
- apply (previous_left_out Jq LJ).
- exists (left J). split;[|split].
  + rewrite LJ; auto.
  + rewrite LJ. apply (bounded_right_out (tas_sig tIp) ME).
  + rewrite LJ.
    apply sing_slice_l.
    apply (previous_left_out Jq LJ).
- exists (left J). split;[|split].
  + rewrite LJ; auto.
  + rewrite not_sig_def, not_sig_def, not_not.
    apply (in_left Jq).
  + rewrite LJ.
    apply sing_slice_l.
    apply (previous_right_in (tas_sig tIp) ME).
- apply (tas_in_slice_right tIp).
  rewrite ME. apply le_ile. auto.
Qed.

Lemma meets_equiv_r (p q:sig) : (inc_sig (meets_new p q) (meets p q)).
intros t (t0,(LE0,(((Pt0,nQt0),((t1,(LE1,(nPt1,On1))),(t2,(LE2,(nnQt2,On2))))),ON))).
G nnQt2.
rewrite not_sig_def, not_sig_def, not_not. intros Qt2.
G (get_sig Pt0); intros (I,t0Ip).
exists I. split.
- apply (tas_move_on_left t0Ip LE0 ON).
- G (get_sig Qt2); intros (J,t2Jq).
  exists J. split;[apply (tas_sig t2Jq)|].
  unfold Meets.
  G (not_after_slice nPt1 LE1 On2). intros LE21.
  G (not_after_slice nnQt2 LE2 On1). intros LE12.
  G (le_antisym _ _ LE21 LE12). intros EQ21.
  rewrite EQ21 in *. clear LE21 LE12 EQ21.
  G (strict_border_left nPt1 Pt0 LE2). intros LT10.
  G (lt_getS LT10). intros (pt,PT). rewrite PT in *.

  G (tas_move_on_right t0Ip (ltS_le LT10) (close_rS_r On2)). intros ptIp.
  rewrite (in_allen_last_is_right ptIp nPt1).

  G (On1 pt (ltS_le LT10) (ltS pt)). intros nQpt.
  rewrite (in_allen_last_is_left t2Jq nQpt). auto.
Qed.

Lemma meets_equiv (p q:sig) : (eq_sig (meets p q) (meets_new p q)).
apply inc_sig_asym;[apply meets_equiv_l|apply meets_equiv_r].
Qed.


(*
 * MET
 *)
Definition met_new p q :=
  (Since p (and_sig (Beq (not_sig q) p) (and_sig (not_sig q) p))).
  
Lemma met_equiv_l (p q:sig) : (inc_sig (met p q) (met_new p q)).
intros t (I,(tIp,(J,(Jq,LR)))).
unfold MetBy in LR.
G (previous_right (eq_sym LR)). intros (t1,LI). rewrite LI in *.
exists (S t1).
split;[|split;[split;[split|split]|]].
- rewrite <- LI; apply (tas_le_left tIp).
- exists t1. split;[auto|split].
  + rewrite not_sig_def, not_sig_def, not_not.
    apply (has_before_right Jq (eq_sym LR)).
  + apply sing_slice_r.
    rewrite <- LI.
    apply (tas_p (tas_left tIp)).
- exists t1. split;[auto|split].
  + apply (previous_left_out (tas_sig tIp) LI).
  + apply sing_slice_r.
    apply (bounded_right_out Jq (eq_sym LR)).
- apply (bounded_right_out Jq (eq_sym LR)).
- rewrite <- LI; apply (tas_p (tas_left tIp)).
- apply close_lr_l.
  apply (tas_in_slice_left tIp). rewrite LI; auto.
Qed.

    
Lemma met_equiv_r (p q:sig) : (inc_sig (met_new p q) (met p q)).
intros t (t0,(LE0,((((t1,(LE1,(nnQt1,On1))),(t2,(LE2,(nPt2,On2)))),(NQt0,Pt0)),ON))).
G nnQt1.
rewrite not_sig_def, not_sig_def, not_not. intros Qt1.
unfold met, MetBy.
G (get_sig Pt0); intros (I,t0Ip).
exists I. split.
- apply (tas_move_on_right t0Ip LE0 ON).
- G (get_sig Qt1); intros (J,t1Jq).
  exists J. split;[apply (tas_sig t1Jq)|].
  G (not_before_slice nPt2 LE2 On1). intros LE21.
  G (not_before_slice nnQt1 LE1 On2). intros LE12.
  G (le_antisym _ _ LE21 LE12). intros EQ21.
  rewrite EQ21 in *. clear LE21 LE12 EQ21.
  G (strict_border_right nPt2 Pt0 LE1). intros LT10.
  G (On1 (S t1) (ltS t1) (lt_leS LT10)). intros pSt1.
  rewrite (border_left t0Ip nPt2 pSt1 LT10 On1).
  G (On2 (S t1) (ltS t1) (lt_leS LT10)). intros nqSt1.
  rewrite (in_allen_last_is_right t1Jq nqSt1).
  auto.
Qed.

Lemma met_equiv (p q:sig) : (eq_sig (met p q) (met_new p q)).
apply inc_sig_asym;[apply met_equiv_l|apply met_equiv_r].
Qed.


                   
(*
 * CONTAINS
 *)
Definition contains_new p q :=
  (or_sig (Until p (during q p))
          (Since p (during q p)) ).

Lemma contains_during t I J p q :
  (tas t I p) ->
  (in_sig J q) ->
  ((left I) < (left J)) ->
  (ilt (right J) (right I)) ->
  (during q p (left J)).
intros tIp Jq LL RR.  
exists J. split.
- apply (in_sig_tas_left Jq).
- exists I. split;[apply (tas_sig tIp)|split;auto].
Qed.  

Lemma contains_equiv_l (p q:sig) : (inc_sig (contains p q) (contains_new p q)).
intros t (I,(tIp,(J,(Jq,(LL,RR))))).
G (left_right_inc_allen (lt_le LL) (ilt_ile RR)); intros IJ.  
G (nat_compare_le_lt t (left J)); intros [LE|LT].
- left.
  exists (left J). split;[auto|split].
  + apply (contains_during tIp Jq LL RR).
  + apply (tas_in_slice_right_right tIp (ilt_ile RR)).
- right.
  exists (left J). split;[(apply (lt_le LT))|split].
  + apply (contains_during tIp Jq LL RR).
  + apply (tas_in_slice_left_left tIp LL).
Qed.

  
Lemma until_contains t p q :
  (Until p (during q p) t) ->
  (contains p q t).
intros (t0,(LE0,((I,(t0Iq,(J,(Jp,(LL,RR))))),ON))).
exists J.
split.
- G (left_right_inc_allen (lt_le LL) (ilt_ile RR)); intros IJ.
  G (tas_inc_tas t0Iq Jp IJ). intros t0Ip.
  apply (tas_move_on_left t0Ip LE0 ON).
- exists I.
  split;[apply (tas_sig t0Iq)|].
  split; auto.
Qed.

Lemma since_contains t p q :
  (Since p (during q p) t) ->
  (contains p q t).
intros (t0,(LE0,((I,(t0Iq,(J,(Jp,(LL,RR))))),ON))).
exists J.
split.
- G (left_right_inc_allen (lt_le LL) (ilt_ile RR)); intros IJ.
  G (tas_inc_tas t0Iq Jp IJ). intros t0Ip.
  apply (tas_move_on_right t0Ip LE0 ON).
- exists I.
  split;[apply (tas_sig t0Iq)|split; auto].
Qed.

Lemma contains_equiv_r (p q:sig) : (inc_sig (contains_new p q) (contains p q)).
intros t [U|S].
- apply (until_contains U).
- apply (since_contains S).
Qed.

Lemma contains_equiv (p q:sig) : (eq_sig (contains p q) (contains_new p q)).
apply inc_sig_asym;[apply contains_equiv_l|apply contains_equiv_r].
Qed.


(*
 * HOLDS
 *)
Definition holds_new p q :=
  (and_sig (and_sig (brighteq p q) p)
           (and_sig q (frighteq p q)) ).

Lemma tas_frighteq t I p q :
  (tas t I q) ->
  (on I p) ->
  (frighteq p q t).
intros tIp On.
case_eq (right I); [intros rI RI;left | intros RI; right].
- exists rI. split;[|split].
  + apply lt_le.
    G (tas_ilt_right tIp).
    rewrite RI; auto.
  + apply (bounded_right_out (tas_sig tIp) RI).
  + intros x LE LT.
    apply On. split.
    * G LE. apply le_trans.
      apply (tas_le_left tIp).
    * rewrite RI; auto.
- intros x LE.
  apply On.
  split.
  + G LE. apply le_trans.
    apply (tas_le_left tIp).
  +  rewrite RI. apply ilt__inf.
Qed.

Lemma tas_brighteq t I p q :
  (tas t I q) ->
  (on I p) ->
  (brighteq p q t).
intros tIp On.
case_eq (left I); [intros LI;right | intros pli LI; left].
- intros x LE.
  apply On.
  split.
  +  rewrite LI. auto with arith.
  + G (tas_ilt_right tIp). apply ile_ilt_trans.
    apply (le_ile LE).
- exists pli. split;[|split].
  + G (tas_le_left tIp). apply le_trans.
    rewrite LI; auto.
  + apply (previous_left_out (tas_sig tIp) LI).
  + intros x LE LT.
    apply On. split.
    * rewrite LI; auto.
    * G (tas_ilt_right tIp). apply ile_ilt_trans.
      apply (le_ile LT).
Qed.

Lemma holds_equiv_l (p q:sig) : (inc_sig (holds p q) (holds_new p q)).
intros t (I,(tIq,On)).
split;[split|split].
- apply (tas_brighteq tIq On).
- apply (On _ (tas_allen tIq)).
- apply (tas_p tIq).
- apply (tas_frighteq tIq On).
Qed.

Lemma holds_equiv_r (p q:sig) : (inc_sig (holds_new p q) (holds p q)).
intros t ((BR,Pt),(Qt,FR)).
G (get_sig Qt); intros (J,tJq). exists J. split;[auto|].
G (get_sig Pt); intros (I,tIp).
intros x IN.
apply (tas_has tIp).
split.
- G (allen_left IN). apply le_trans.
  apply (tas_tas_brighteq tIp tJq BR).
- G (tas_tas_frighteq tIp tJq FR). apply ilt_ile_trans.
  apply (allen_right IN).
Qed.

Lemma holds_equiv (p q:sig) : (eq_sig (holds p q) (holds_new p q)).
apply inc_sig_asym;[apply holds_equiv_l|apply holds_equiv_r].
Qed.




(*
 * OCCURS
 *)
Definition occurs_new p q := (or_sig (possible p q) (occurred p q)).

Lemma occurs_equiv_l (p q:sig) : (inc_sig (occurs p q) (occurs_new p q)).
intros t (I,(tIq,(t',(t'I,Qt')))).
G (nat_compare_le_lt t t'); intros [LE|LT].
- left.
  exists t'. split;[auto|split;[split;[auto|]|]].
  + apply (tas_p (tas_mov tIq t'I)).
  + apply (tas_in_slice_right tIq).
    apply (ilt_ile (allen_right t'I)).
- right.
  exists t'. split;[|split;[split;[auto|]|]].
  + apply (lt_le LT).
  + apply (tas_p (tas_mov tIq t'I)).
  + apply (tas_in_slice_left tIq).
    G (allen_left t'I). auto with arith.
Qed.

Lemma possible_occurs p q t : (possible p q t) -> (occurs p q t).
intros (t0,(LE0,((Pt0,Qt0),Onq))).
G (get_sig (extend_right_until LE0 Qt0 Onq)). intros (I,tIq).
exists I. split;[auto|].
exists t0. split;[split|auto].
- G LE0. apply le_trans.
  apply (tas_le_left tIq). 
- apply (tas_follow_right tIq).
  apply close_lr_l.
  apply (extend_slice_open_right Qt0 Onq).
Qed.

Lemma occurred_occurs p q t : (occurred p q t) -> (occurs p q t).
intros (t0,(LE0,((Pt0,Qt0),Onq))).
G (get_sig (extend_left_since LE0 Qt0 Onq)). intros (I,tIq).
exists I. split;[auto|].
exists t0. split;[split|auto].
- apply (tas_follow_left tIq).
  intros x LE LT.
  rewrite le_fix_def in LE. G LE. clear LE.
  intros [LT2|EQ].
  + apply Onq; [|apply lt_le]; auto.
  + rewrite <- EQ; auto.   
- G (tas_ilt_right tIq). apply ile_ilt_trans.
  apply (le_ile LE0).
Qed.

Lemma occurs_equiv_r (p q:sig) : (inc_sig (occurs_new p q) (occurs p q)).
intros t [P|O]; [apply (possible_occurs P) | apply (occurred_occurs O)].
Qed.

Lemma occurs_equiv (p q:sig) : (eq_sig (occurs p q) (occurs_new p q)).
apply inc_sig_asym;[apply occurs_equiv_l|apply occurs_equiv_r].
Qed.
                            

      


End spec.

