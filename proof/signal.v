Set Implicit Arguments.
Unset Strict Implicit.

Require Import basics.
Require Import enat.
Require Import allen.


Section signal.

Ltac G x := generalize x.

Ltac BAD := intros BAD; inversion BAD.

Ltac INC_CMP CV1 CV2 :=
  intros I J (LL,RR);
  apply (inc_allen_by_comp2 (CV1 _ _ LL) (CV2 _ _ RR)).

Ltac RINC_CMP CV1 CV2 :=
  intros I J (LL,RR);
  apply (inc_allen_by_comp2 (CV1 _ _ LL) (CV2 _ _ RR)).


(*
 * Signals
 *)
Definition sig := nat -> Prop.

(*
 * EQ_SIG
 *)
Definition eq_sig (p q:sig) := forall (t:nat), (p t)<->(q t).

Lemma eq_sig_sym (p q:sig) : (eq_sig p q) <-> (eq_sig q p).
split;intros EQ;intros t;rewrite (EQ t);tauto.
Qed.


(*
 * NOT
 *)
Definition not_sig (p:sig) : sig := fun t => ~(p t).

Lemma not_sig_def (p:sig) (t:nat) : ((not_sig p) t) = ~(p t).
auto.
Qed.

Lemma not_not_sig_def (p:sig) (t:nat) : (~((not_sig p) t)) <-> (p t).
rewrite not_sig_def.
apply not_not.
Qed.

Lemma eq_sig_not_not (p:sig) : (eq_sig (not_sig (not_sig p)) p).
intros t.
repeat rewrite not_sig_def.
rewrite not_not.
tauto.
Qed.


(*
 * On/Off
 *)
Definition on (I:allen) (p:sig) := (forall t, (in_allen t I) -> (p t)).

Definition off (I:allen) (p:sig) := (forall t, (in_allen t I) -> ~(p t)).

Lemma on_left (p:sig) (I:allen) : (on I p) -> (p (left I)).
intros IInp.
apply (IInp _ (in_allen_left I)).
Qed.

Lemma inc_allen_on (p:sig) (I J:allen) :
 (inc_allen I J) ->
 (on J p) ->
 (on I p).
intros INC JInp t tInI.
apply (JInp t (INC _ tInI)).
Qed.

(*
 * in_sig
 *)
Definition in_sig  (I:allen) (p:sig) : Prop := 
    (match (left I) with 0 => True | (S t) => ~(p t) end)
 /\ (match (right I) with Inf => True | Fix t => ~(p t) end)
 /\ (on I p).

Lemma eq_allen_in_sig p I J :
 (eq_allen I J) ->
 (in_sig I p) ->
 (in_sig J p).
intros (EQL,EQR) (LEFT,(RIGHT,SLICE)).
split;[|split];
unfold in_sig.
- rewrite <- EQL; auto.
- rewrite <- EQR; auto.
- intros t tInJ.
  apply SLICE.
  apply inc_allen_refl with (I:=J) (J:=I); auto.
  apply eq_allen_sym; split; auto.
Qed.


(* Basic borders *)
Lemma previous_left_out (p:sig) (I:allen) (pl:nat) :
 (in_sig I p) ->
 (left I) = (S pl) ->
 ~(p pl).
intros (OK,_) LI.
rewrite LI in OK; auto.  
Qed.

Lemma bounded_right_out p I r :
 (in_sig I p) ->
 (right I)=(Fix r) ->
 ~(p r).
intros (_,(OK,_)) RI.
rewrite RI in OK; auto.
Qed.

Lemma in_sig_slice I p :
 (in_sig I p) ->
 (on I p).
intros (_,(_,OK)); auto.
Qed.

Lemma in_left (p:sig) (I:allen) : (in_sig I p) -> (p (left I)).
intros IInp.
apply (in_sig_slice IInp (in_allen_left I)).
Qed.

Lemma previous_right_in (I:allen) (p:sig) (r:nat) :
 (in_sig I p) ->
 (right I) = (Fix (S r)) ->
 (p r).
intros IInp RI.
apply (in_sig_slice IInp).
split.
- G (wf I).
  rewrite RI; simpl; auto with arith.
- rewrite RI; simpl; auto.
Qed.


(* safe *)
Definition safe_allen_relation (R:(allen->allen->Prop)) := forall I1 I2 J1 J2,
 (eq_allen I1 I2) ->
 (eq_allen J1 J2) ->
 (R I1 J1) ->
 (R I2 J2).

Lemma safe_allen_fun_extend (R:(allen -> allen -> Prop)) (q:sig) :
 (safe_allen_relation R) ->
 (safe_allen_fun (fun I => (exists J, (in_sig J q) /\ (R I J)))).
intros SR I1 I2 EQ (J,(Jq,R1)).
exists J. split;[auto|].
apply (SR _ _ _ _ EQ (eq_allen_refl J) R1).
Qed.

(*
 * ORDERS
 * inc_sig p q : (p t) -> (q t)
 * inc_sig_allen p q : I\in p -> I\in q
 *)

Definition inc_sig (p q:sig) := forall (t:nat),
  (p t) -> (q t).

Lemma inc_sig_trans (p q r:sig) : (inc_sig p q) -> (inc_sig q r) -> (inc_sig p r).
intros PQ QR t Pt.
apply (QR t (PQ t Pt)).
Qed.

Definition inc_sig_allen (p q:sig) := forall (I:allen),
 (in_sig I p) -> (in_sig I q).

Lemma in_sig_fixl_gt0 I : (ilt (Fix 0) (right I)).
generalize (wf I).
case (right I) as [t|]; simpl; auto.
intros LT.
apply (lt_0lt LT).
Qed.

(*
 * TON
 *)
Definition ton (t:nat) (I:allen) (p:sig) := (in_allen t I) /\ (on I p).

Lemma ton_def (t:nat) (I:allen) (p:sig) :
 (in_allen t I) -> (on I p) -> (ton t I p).
split; auto.
Qed.

Lemma ton_allen  (t:nat) (I:allen) (p:sig) : (ton t I p) -> (in_allen t I).
intros (OK,_); auto.
Qed.

Lemma ton_sig  (t:nat) (I:allen) (p:sig) : (ton t I p) -> (on I p).
intros (_,OK); auto.
Qed.

Lemma ton_p (t:nat) (I:allen) (p:sig) : (ton t I p) -> (p t).
intros (tI,IN).
apply (IN _ tI).
Qed.



(*
 * TAS
 *)
Definition tas (t:nat) (I:allen) (p:sig) := (in_allen t I) /\ (in_sig I p).

Lemma tas_ton (t:nat) (I:allen) (p:sig) : (tas t I p) -> (ton t I p).
intros (tI,(_,(_,OK))). split; auto.
Qed.

Lemma tas_def (t:nat) (I:allen) (p:sig) :
 (in_allen t I) -> (in_sig I p) -> (tas t I p).
split; auto.
Qed.

Lemma tas_allen  (t:nat) (I:allen) (p:sig) : (tas t I p) -> (in_allen t I).
intros (OK,_); auto.
Qed.

Lemma tas_sig  (t:nat) (I:allen) (p:sig) : (tas t I p) -> (in_sig I p).
intros (_,OK); auto.
Qed.

Lemma tas_on (p:sig) (I:allen) (t:nat) : (tas t I p) -> (on I p).
intros (_,(_,(_,OK))); auto.
Qed.

Lemma tas_p (t:nat) (I:allen) (p:sig) : (tas t I p) -> (p t).
intros (tI,Ip).
apply (in_sig_slice Ip tI).
Qed.

Lemma in_sig_tas_left (p:sig) (I:allen) : (in_sig I p) -> (tas (left I) I p).
intros Ip. apply (tas_def (in_allen_left I) Ip).
Qed.

Lemma tas_left (p:sig) (I:allen) (t:nat) : (tas t I p) -> (tas (left I) I p).
intros tIp.
apply (in_sig_tas_left (tas_sig tIp)).
Qed.

Lemma tas_mov (p:sig) (I:allen) (t t':nat) :
 (tas t I p) ->
 (in_allen t' I) ->
 (tas t' I p).
intros tIp t'I.
apply (tas_def t'I (tas_sig tIp)).
Qed.

Lemma inc_in_on (p q:sig) (I:allen) :
 (inc_sig p q) ->
 (in_sig I p) ->
 (on I q).
intros INC Ip t tI.
apply (INC t (tas_p (tas_def tI Ip))).
Qed.

(* On successive points *)

Lemma in_allen_in_sig__on_succ (p:sig) (I:allen) (t:nat) :
 (tas t I p) ->
 (p (S t)) ->
 (in_allen (S t) I).
intros ((LEFT,RIGHT),IInp) PSt.
split;[auto|].
case_eq (right I); simpl; auto.
intros r RI.
rewrite RI in RIGHT; simpl in RIGHT.
G (nat_compare (S t) r);intros [LE|[EQ|GT]];[auto | | ].
- exfalso.
  G PSt. rewrite EQ.
  apply (bounded_right_out IInp RI).
- exfalso.
  apply (too_small_segment (x:=t)(y:=r)); auto.
Qed.

Lemma in_allen_in_sig__on_prev (p:sig) (I:allen) (t:nat) :
 (tas (S t) I p) ->
 (p t) ->
 (in_allen t I).
intros ((LEFT,RIGHT),IInp) Pt.
split;[|apply (ilt_succ RIGHT)].
case_eq (left I); [auto with arith | intros l LI].
rewrite LI in LEFT.
G (nat_compare (S l) t);intros [LE|[EQ|GT]];[auto with arith| | ].
- rewrite EQ; auto.
- exfalso.
  G (single_segment (le_succ_r LEFT) GT); intros EQ.
  G Pt. rewrite <- EQ.
  apply (previous_left_out IInp LI).
Qed.

Lemma in_allen_in_sig_follow_right (p:sig) (I:allen) (t t':nat) :
 (tas t I p) ->
 (forall x, (t<x) -> (x<=t') -> (p x)) ->
 (ilt (Fix t') (right I)).
intros (tInI,IInp) Slice.
case_eq (right I);simpl;[intros ri RI|auto].
rewrite <- not_not, <- le__not_lt.
intros LE.
cut (p ri);[apply (bounded_right_out IInp RI)|].
apply Slice;[|auto].
G (allen_right tInI). rewrite RI. auto.
Qed.

(* inc_sig *)
Lemma inc_sig_asym (p q:sig) :
 (inc_sig p q) ->
 (inc_sig q p) ->
 (eq_sig p q).
intros PInQ QInP t.
split; [intros Pt; apply (PInQ _ Pt)|intros Qt; apply (QInP _ Qt)].
Qed.

Lemma tas_inc_tas (p q:sig) (I J:allen) (t:nat) :
 (tas t I p) ->
 (in_sig J q) ->
 (inc_allen I J) ->
 (tas t J q).
intros tIp Jq INC.
apply (tas_def (INC _ (tas_allen tIp)) Jq).
Qed.

Lemma tas_by_include (p q:sig) (I J:allen) (t:nat) :
 (tas t I p) ->
 (in_sig J q) ->
 (inc_allen I J) ->
 (tas t J q).
intros (tInI,IInp) JInq INC.
split;[|auto].
apply (in_allen_by_include tInI (inc_allen_left INC) (inc_allen_right INC)).
Qed.

(* inc_allen *)
Lemma not_and_or_not (P Q:Prop) : ~(P /\Q) -> (~P \/ ~Q).
tauto.
Qed.

Lemma not_inc_allen (I J:allen) :
  (not (inc_allen I J)) ->
  (exists t, (in_allen t I) /\ (t<(left J) \/ (ile (right J) (Fix t)))).
intros NINC.
G (not_all_ex_not _ _ NINC). clear NINC. intros (t,NIMP).
exists t.
G (not_imply_and NIMP). clear NIMP. intros (tI,NIN).
split;[auto|].
G (not_and_or_not NIN). clear tI NIN. intros [LT | LE];[left|right].
- rewrite le__not_lt in LT.  tauto.
- rewrite ile__not_ilt. auto.
Qed.  

Lemma in_allen_in_sig_slice__inc_allen (p:sig) (I J:allen) (t:nat) :
 (in_allen t I) ->
 (in_allen t J) ->
 (in_sig J p) ->
 (on I p) ->
 (inc_allen I J).
intros tInI tInJ JInp SLIp.
apply left_right_inc_allen.
- (* use tas_tas_not_left_lt *)
  rewrite le__not_lt.
  case_eq (left J); [|intros pl];intros LJ.
  + apply nlt0.
  + G (previous_left_out JInp LJ).
    apply ncontra. intros LI.
    apply SLIp.
    split.
    * apply ltS__le; auto.
    * G (allen_left tInJ); rewrite LJ; intros LE.
      apply (lt_ilt_trans (leS_lt LE) (allen_right tInI)).
- case_eq (right J); [intros r|]; intros RJ.
  + rewrite ile__not_ilt.
    G (bounded_right_out JInp RJ).
    apply ncontra. intros LT.
    apply SLIp.
    split;[|auto].
    apply lt_le.
    G (allen_right tInJ); rewrite RJ; simpl.
    G (allen_left tInI).
    apply le_lt_trans.
  + apply ile_inf.
Qed.

Lemma in_allen_in_sig_slice__inc_allen2 (p:sig) (I J:allen) (t:nat) :
 (in_allen t I) ->
 (tas t J p) ->
 (on I p) ->
 (inc_allen I J).
intros tInI (tInJ,JInq) INC.
apply (in_allen_in_sig_slice__inc_allen tInI tInJ JInq INC).
Qed.

(* inc_sig_allen *)

Lemma inc_sig_allen_refl (p q:sig) :
 (eq_sig p q) ->
 (inc_sig_allen p q).
intros EQ I IInp.
split;[|split].
- case_eq (left I); auto; intros pl LI.
  rewrite <- (EQ pl).
  apply (previous_left_out IInp LI).
- case_eq (right I); auto; intros r RI.
  rewrite <- (EQ r).
  apply (bounded_right_out IInp RI).
- intros t tInI.
  G (in_sig_slice IInp tInI); rewrite <- (EQ t); auto.
Qed.

Lemma eq_sig_tas (p q:sig) (I:allen) (t:nat) :
 (eq_sig p q) ->
 (tas t I p) ->
 (tas t I q).
intros EQ (tInI,IInp).
split;[auto|].
apply (inc_sig_allen_refl EQ IInp).
Qed.






(*
 * finding the allen interval from a time point
 *)

Lemma dec_step (P NP:Prop) : (NP<->~P) -> (P\/NP).
tauto.
Qed.

Lemma not_for__ex_not (T:Type) (x:T) (P:T->Prop) :
 (~(forall x, (P x))) <-> (exists x, ~(P x)).
split.
- apply not_all_ex_not.
- apply ex_not_not_all.
Qed.

Lemma hole_in_left (f:nat->Prop) (t:nat) :
    (forall t', (t'<t) -> ((f t')<->(f t)))
 \/ (exists M, (M<t) /\ ~((f M) <-> (f t))).
apply dec_step.
rewrite not_for__ex_not; auto.
split; intros (x,P); exists x; tauto.
Qed.

Lemma hole_in_right (f:nat->Prop) (t:nat) :
    (forall t', (t<t') -> ((f t')<->(f t)))
 \/ (exists M, (t<M) /\ ~((f M) <-> (f t))).
apply dec_step.
rewrite not_for__ex_not; auto.
split; intros (x,P); exists x; tauto.
Qed.

Lemma sigf_compare (f:nat->Prop) (t1 t2:nat) :
 ((f t1) <-> (f t2)) \/ ((f t1) <-> ~(f t2)).
tauto.
Qed.


Lemma search_left (f:nat->Prop) (t:nat) :
 (   (forall t', t'<t -> ((f t') <-> (f t)))
  \/ (exists m, (m<t)
             /\ ~((f m) <-> (f t))
             /\ (forall t', (m<t'<t -> ((f t') <-> (f t)))) )).
induction t as [|t [SUS|(m,(LT,(NOT,SLICE)))]].
- left; intros t'; BAD.
- G (sigf_compare f t (S t)); intros [EQ|NEQ].
  + left; intros t' LT.
    rewrite <- EQ.
    G (ltSucc LT); intros [LT2|EQ2]; auto.
    rewrite EQ2; tauto.
  + right; exists t; split;[auto|split;[tauto|]].
    intros t' SEG.
    exfalso.
    apply (too_small_segment SEG).
- G (sigf_compare f t (S t)); intros [EQ|NEQ].
  + right; exists m.
    split;[auto with arith|split;[rewrite <-EQ;auto|]].
    intros t' (LT1,LT2).
    rewrite <- EQ.
    G (ltSucc LT2); intros [LT3|EQ3]; auto.
    rewrite EQ3; tauto.
  + right; exists t; split;[auto|split;[tauto|]].
    intros t' SEG.
    exfalso.
    apply (too_small_segment SEG).
Qed.

Lemma try_find_left (f:nat->Prop) (t:nat) :
 (f t) ->
 (   (forall t', t'<t -> (f t'))
  \/ (exists m, (m<t)
            /\ ~(f m)
            /\ (forall t', (m<t'<t -> (f t')))) ).
intros Ft.
G (search_left f t); intros [SUS|(m,(LT,(NOT,SLICE)))].
- left; intros t' LT.
  rewrite (SUS _ LT); auto.
- right.
  exists m; split;[auto|split;[tauto|]].
  intros t' SEG.
  rewrite (SLICE _ SEG); auto.
Qed.  

Lemma try_find_left2 (f:nat->Prop) (t:nat) :
 (f t) ->
 (   (forall t', t'<t -> (f t'))
  \/ (exists m, (m<t)
            /\ ~(f m)
            /\ (forall t', m<t' -> t'<=t -> (f t'))) ).
intros Ft.
G (search_left f t); intros [SUS|(m,(LT,(NOT,SLICE)))].
- left; intros t' LT.
  rewrite (SUS _ LT); auto.
- right.
  exists m; split;[auto|split;[tauto|]].
  intros t' SEG.
  rewrite le_fix_def.
  intros [GT|EQ]; [rewrite SLICE|rewrite EQ]; auto.
Qed.  

Lemma seg_choice_left_ind (f:nat->Prop) (m:nat) : forall n,
    (forall t, m<t<m+n -> ((f t) <-> (f m)))
 \/ (exists t, m<t<(m+n)
            /\ ~((f t) <-> (f m))
            /\ (forall x, m<x<t -> ((f x) <-> (f m))) ).
induction n as [|n [SL|(t,((LT,GT),(NEQ,SLI)))]].
- left.
  replace (m+0) with m; auto.
  intros t (B1,B2).
  exfalso.
  apply (lt_asym _ _ B1 B2).
- G (sigf_compare f m (m+n)); intros [EQ|DIFF].
  + left.
    intros t (LT,GT).
    G (nat_compare t (m+n)); intros [LT2|[EQ2|GT2]].
    * apply SL.
      split; auto with arith.
    * rewrite EQ2; tauto.
    * exfalso; apply (too_small_segment (x:=(m+n)) (y:=t)).
      replace (S (m+n)) with (m+(S n)); auto.
  + case n as [|n].
    * replace (m+0) with m in DIFF; auto.
      exfalso; tauto.
    * right.
      exists (m+(S n)).
      split; [|tauto].
      split; auto with arith.
      apply lt_add_S.
- right.
  exists t.
  split; [split;[auto|]|auto].
  apply (lt_trans _ _ _ GT).
  auto with arith.
Qed.


Lemma seg_choice_left (f:nat->Prop) (m M:nat) :
  (m < M) ->
    (forall t, m<t<M -> ((f t) <-> (f m)))
 \/ (exists t, m<t<M
            /\ ~((f t) <-> (f m))
            /\ (forall x, m<x<t -> ((f x) <-> (f m))) ).
intros LTS.
G (seg_choice_left_ind f m (M-m)); intros [SLI|(t,((LT,GT),(NEQ,SLE)))].
- replace (m+(M-m)) with M in SLI;[|auto with arith].
  left; auto.
- replace (m+(M-m)) with M in GT;[|auto with arith].
  right; exists t; auto.
Qed.

Lemma search_right (f:nat->Prop) (t:nat) :
    (forall t', t<t' -> ((f t')<->(f t)))
 \/ (exists M, t<M
            /\ ~((f M) <-> (f t))
            /\ (forall t', t<t'<M -> ((f t') <-> (f t))) ).
G (hole_in_right f t); intros [ALL|(H,(LT,HOLE))].
- left; auto.
- right; G (seg_choice_left f LT); intros [SLI|(M,((LTM,GTM),(NOT,SLI)))].
  + exists H; auto.
  + exists M; auto.
Qed.

Lemma try_find_right (f:nat->Prop) (t:nat) :
 (f t) ->
    (forall t', t<t' -> (f t'))
 \/ (exists M, t<M
            /\ ~(f M)
            /\ (forall t', t<t'<M -> (f t')) ).
intros Ft.
G (search_right f t); intros [SUS|(M,(LT,(NOT,SLICE)))].
- left; intros t' LT.
  rewrite (SUS _ LT); auto.
- right.
  exists M; split;[auto|split;[tauto|]].
  intros t' SEG.
  rewrite (SLICE _ SEG); auto.
Qed.

Lemma get_sig (p:sig) (t:nat) : (p t) -> (exists I, (tas t I p)).
intros Pt.
G (try_find_left Pt); intros [SUSL|(m,(LT,(LEFT,SL1)))];
 G (try_find_right Pt); intros [SUSR|(M,(GT,(RIGHT,SL2)))].
- exists (make_allen (m:=0) (M:=Inf) (ilt__inf 0)).
  split;[split;[auto with arith|simpl;auto]|split;[split|split;[split|]]].
  intros t' _.
  G (nat_compare t t'); intros [LE|[EQ|GT]];
    [apply (SUSR _ LE)|rewrite <- EQ|apply (SUSL _ GT)]; auto.
- exists (make_allen (m:=0) (M:=(Fix M)) (lt_0ilt GT)).
  split;[split;[auto with arith|simpl;auto]|split;[split|split;[auto|]]].
  intros t' (_,LT'). simpl in LT'.
  G (nat_compare t t'); intros [LE|[EQ|GT2]];
    [apply SL2|rewrite <- EQ|apply (SUSL _ GT2)]; auto.
- exists (make_allen (m:=(S m)) (M:=Inf) (ilt__inf (S m))).
  split;[split;[auto with arith|simpl;auto]|split;[auto|split;[split|]]].
  intros t' (LE2,_). simpl in LE2.
  G (nat_compare t t'); intros [LE|[EQ|GT2]];
    [apply SUSR|rewrite <- EQ|apply SL1]; auto.
- exists (make_allen (m:=(S m)) (M:=(Fix M)) (lt_iltS_trans LT GT)).
  split;[split;[auto with arith|simpl;auto]|split;[auto|split;[auto|]]].
  intros t' (LE2,LE3). simpl in LE2. simpl in LE3.
  G (nat_compare t t'); intros [LE|[EQ|GT2]];
    [apply SL2|rewrite <- EQ|apply SL1]; auto.
Qed.





End signal.
