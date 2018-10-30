(*
 * Formal specification of signals defined over set of Allen's intervals
 * Essentials lemmas
 * Proofs of equivalences between some basic signal functions
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



(*
 * Equivalences
 *)

(*
 * DN
 *)
Definition dn_new (p:sig) := (and_sig (not_sig p) (delay 1 p)).

Lemma dn_equiv_l (p:sig) : (inc_sig (dn p) (dn_new p)).
intros t (I,(Right,IInp)).
G (previous_right (eq_sym Right)). intros (pt,T). rewrite T in *. clear T t.
- split;[|split].
  + apply (bounded_right_out IInp (eq_sym Right)).
  + apply (le_succ (le_0 pt)).
  + replace (S pt - 1) with pt; auto with arith.
    apply (in_sig_slice IInp (t:=pt)).
    G (wf I); rewrite <- Right.
    split; [auto with arith|].
    rewrite <- Right; simpl; auto with arith.
Qed.

Lemma dn_equiv_r (p:sig) : (inc_sig (dn_new p) (dn p)).
intros t (NOT,(SUP1,ISUB)).
G (gt0_has_previous SUP1). intros (pt,T). rewrite T in *. clear T SUP1 t.
replace (S pt - 1) with pt in ISUB; [|auto with arith].
generalize (down_allen_left ISUB NOT); intros (I,(IN,RIGHT)).
exists I; auto.
Qed.

Lemma dn_equiv (p:sig) : (eq_sig (dn p) (dn_new p)).
apply inc_sig_asym;[apply dn_equiv_l|apply dn_equiv_r].
Qed.





(*
 * UP
 *)
Definition up_new (p:sig) := (dn (not_sig p)).

Lemma up_equiv_l (p:sig) : (inc_sig (up p) (up_new p)).
intros t (W,(I,(EQL,(Left,(Right,Slice))))).
G (gt0_has_previous W). intros (pt,T). rewrite T in *; clear T W t.
rewrite <- EQL in Left.
cut (p (S pt)).
- intros PS.
  generalize (up_allen_left Left PS); intros (I',(EQR,IN)).
  exists I'; auto.
- apply Slice; split.
  + rewrite EQL; auto.
  + G (wf I); rewrite EQL; auto.
Qed.

Lemma up_equiv_r (p:sig) : (inc_sig (up_new p) (up p)).
intros t (I,(EQR,(LEFT,(RIGHT,SLICE)))).
G (previous_right (eq_sym EQR)). intros (pt,T). rewrite T in *. clear T t.
apply up_succ.
- apply SLICE.
  split.
  + G (wf I). rewrite <- EQR. auto with arith.
  + rewrite <- EQR. simpl; auto.
- rewrite <- EQR in RIGHT.
  rewrite <- not_not_sig_def; auto.
Qed.

Lemma up_equiv (p:sig) : (eq_sig (up p) (up_new p)).
apply inc_sig_asym;[apply up_equiv_l|apply up_equiv_r].
Qed.








(*
 * MET
 *)
Definition met_new (p q:sig) := (occurs (and_sig (dn q) (up p)) p).

Lemma met_equiv_l (p q:sig) : (inc_sig (met p q) (met_new p q)).
intros t (I,(tIp,(J,(JInq,EQ)))).
unfold MetBy in EQ.
exists I. split;[auto|].
exists (left I). split;[apply in_allen_left|].
split.
- exists J; auto.
- split.
  + G (in_sig_fixl_gt0 J). rewrite <- EQ; auto.
  + exists I. split;[auto|apply (tas_sig tIp)].
Qed.    

Lemma met_equiv_r (p q:sig) : (inc_sig (met_new p q) (met p q)).
intros t (I,(tIp,(t',(t'InI,((J,(EQR,JInq)),(LT,(II,(EL,IIInp)))))))).
rewrite EL in *; clear EL.
exists I. split;[auto|].
exists J. split;[auto|].
unfold MetBy. rewrite <- EQR.
rewrite (tas_uniq_left (tas_mov tIp t'InI) (in_sig_tas_left IIInp)).
auto.
Qed.

Lemma met_equiv (p q:sig) : (eq_sig (met p q) (met_new p q)).
apply inc_sig_asym;[apply met_equiv_l|apply met_equiv_r].
Qed.







(*
 * OCCURS
 *)
Definition occurs_new (p q:sig) := (and_sig q (not_sig (holds (not_sig p) q))).

Lemma occurs_equiv_l (p q:sig) : (inc_sig (occurs p q) (occurs_new p q)).
intros t (I,(tIq,(t',(t'InI,Pt')))).
split.
- apply (tas_p tIq); auto.
- apply all_not_not_ex; intros J (tJq,F).
  apply (F t' (in_sig_inc_allen tIq tJq t'InI) Pt').
Qed.

Lemma occurs_equiv_r (p q:sig) : (inc_sig (occurs_new p q) (occurs p q)).
intros t (Qt,NEX).
G (get_sig Qt); intros (I,tIq).
exists I.
split;[auto|].
G (not_and_or _ _ (not_ex_all_not allen _ NEX I)). intros [O1|O2].
- exfalso; auto.
- G (not_all_ex_not _ _ O2); intros (t',P).
  G (not_imply_and P). rewrite not_not_sig_def. exists t'; auto.
Qed.

Lemma occurs_equiv (p q:sig) : (eq_sig (occurs p q) (occurs_new p q)).
apply inc_sig_asym;[apply occurs_equiv_l|apply occurs_equiv_r].
Qed.





(*
 * INIT
 *)
Definition init_new (p:sig) := (and_sig p (not_sig (met p (not_sig p)))).

Lemma init_equiv_l (p:sig) : (inc_sig (init p) (init_new p)).
intros t (I,(tIp,LI)).
split.
- apply (tas_p tIp).
- intros (K,(tKp,(L,(LInp,MET)))).
  G (allen_right_gt0 L).
  rewrite <- MET, <- (tas_uniq_left tIp tKp), LI.
  apply lt_irrefl.
Qed.

Lemma init_equiv_r (p:sig) : (inc_sig (init_new p) (init p)).
intros t (Pt,NM).
G (get_sig Pt). intros (I,tIp).
exists I. split;[auto|].
G NM. apply contra. rewrite not_sig_def, not_not.
intros LI. G (not0 LI). clear LI. intros (n,LI).
exists I. split;[auto|].
G (previous_left_out (tas_sig tIp) LI). intros NOTF.
G (in_left (tas_sig tIp)). rewrite LI. intros F.
G (up_allen_left NOTF F). intros (J,(JInNotp,Met)).
exists J. split;[auto|].
unfold MetBy. rewrite LI; auto.
Qed.

Lemma init_equiv (p:sig) : (eq_sig (init p) (init_new p)).
apply inc_sig_asym;[apply init_equiv_l|apply init_equiv_r].
Qed.






(*
 * FINAL
 *)
Definition final_new (p:sig) := (occurs (holds p (delay 1 p)) p).

Lemma final_equiv_l (p:sig) : (inc_sig (final p) (final_new p)).
intros t (I,(tIp,RI)).
exists I. split;[auto|].
exists (S (left I)). split;[|].
- split;[auto|rewrite RI;simpl;auto].
- cut (ilt (Fix (S (left I))) Inf);[intros WF|simpl;auto].
  exists (make_allen (m:=(S (left I))) (M:=Inf) WF).
  split;[split|].
  + split; auto.
  + G (in_sig_close_in_sig_delay 1 (tas_sig tIp)).
    apply eq_allen_in_sig.
    split; simpl; auto.
    rewrite RI; auto.
  + intros t' (LEFT,_). simpl in LEFT.
    apply (in_sig_slice (tas_sig tIp) (t:=t')).
    split;[|rewrite RI;simpl;auto].
    G LEFT; apply le_trans; auto.
Qed.

Lemma final_equiv_r (p:sig) : (inc_sig (final_new p) (final p)).
intros t (I,(tIp,(tt,(ttInI,(J,(ttJDY,SLI)))))).
exists I. split;[auto|].
apply contra_inf.
intros (t',RI).
G (bounded_right_out (tas_sig tIp) RI).
apply not_not.
apply SLI.
G (in_sig_close_in_sig_delay 1 (tas_sig tIp)). intros MAInDY.
apply (eq_allen_in_allen (I:=(make_allen (m:=1+left I) (M:=(fiadd 1 (right I))) (wf_shift 1 I)))).
- G (in_sig_delay1_eq_sig (tas_def ttInI (tas_sig tIp)) ttJDY).
  apply eq_allen_sym.
- apply in_allen_previous_right.
  simpl; rewrite RI; auto.
Qed.

Lemma final_equiv (p:sig) : (eq_sig (final p) (final_new p)).
apply inc_sig_asym;[apply final_equiv_l|apply final_equiv_r].
Qed.







(*
 * EQ
 *)
Definition eq_new (p q:sig) := (and_sig (holds p q) (holds q p)). 

Lemma eq_equiv_l (p q:sig) : (inc_sig (eq p q) (eq_new p q)).
intros t ext. G (ext_inc ext Eq_inc). intros (I,(tIp,(J,(tJq,EQ)))). clear ext.
split.
- exists J. split;[auto|].
  intros t' t'InJ.
  apply (tas_p (tas_def t'InJ (eq_allen_in_sig EQ (tas_sig tIp)))).
- exists I. split;[auto|].
  intros t' t'InI.
  apply (tas_p (tas_def (eq_allen_in_allen EQ t'InI) (tas_sig tJq))).
Qed.

Lemma eq_equiv_r (p q:sig) : (inc_sig (eq_new p q) (eq p q)).
intros t ((J,(tJq,SLJp)),(I,(tIp,SLIq))).
exists I. split;[auto|].
exists J. split;[(apply (tas_sig tJq))|].
G (in_allen_in_sig_slice__inc_allen2 (tas_allen tJq) tIp SLJp).
G (in_allen_in_sig_slice__inc_allen2 (tas_allen tIp) tJq SLIq).
apply inc_allen_asym.
Qed.

Lemma eq_equiv (p q:sig) : (eq_sig (eq p q) (eq_new p q)).
apply inc_sig_asym;[apply eq_equiv_l|apply eq_equiv_r].
Qed.






(*
 * OVER
 *)
Definition over_new (p q:sig) :=
  (and_sig (occurs (not_sig p) (occurs_up q p))
           (occurs (up_after p q) (and_sig p q)) ).

Lemma over_over_new_left (p q:sig) :
 (inc_sig (over p q) (occurs (not_sig p) (occurs_up q p))).
intros t (I,(tIp,(J,(tJq,(LIJ,RIJ))))).
G tIp; intros (tInI,IInp). G tJq; intros (tInJ,JInq).
G (allen_has_intersection tInJ tInI); intros LIRJ.
exists J. split;[|].
- apply (overlaps_occurs_up tIp tJq LIJ RIJ).
- G (ilt_left_is_fix RIJ); intros (r,RI). exists r.
  split.
  + split.
    * rewrite RI in LIRJ; simpl in LIRJ; apply (lt_le LIRJ).
    * rewrite <- RI; auto.
  + apply (bounded_right_out IInp RI).
Qed.

Lemma over_over_new_right (p q:sig) :
  (inc_sig (over p q) (occurs (up_after p q) (and_sig p q))).
intros t (I,(tIp,(J,(tJq,(LIJ,RIJ))))).
G (tas_has_intersection tJq tIp); intros WF.
exists (make_allen (m:=(left J)) (M:=(right I)) WF).
split.
  + apply (over_over_new_right_left WF tIp tJq LIJ RIJ).
  + exists (left J); split;[split;[auto|auto]|].
    apply (overlaps_up_after_left tIp tJq LIJ RIJ WF).
Qed.

Lemma over_equiv_l (p q:sig) : (inc_sig (over p q) (over_new p q)).
intros t OVR.
split.
- apply (over_over_new_left OVR).
- apply (over_over_new_right OVR).
Qed.

Lemma over_equiv_r (p q:sig) : (inc_sig (over_new p q) (over p q)).
intros t ((I,(tIO,(t',(t'InI,NPt')))),(J,(tJA,(u',(u'InJ,NPu'))))).
G (get_sig (and_left (tas_p tJA))). intros (K, tKp).
G tIO; intros (tInI,IInO).
G tJA; intros (tInJ,JInA).
G tKp; intros (tInK,KInp).
exists K. split;[auto|].
exists I. split;[|split].
- apply (tas_filter_tas_arg tIO).
- apply (occurs_up_after_on_left tIO tJA tKp u'InJ NPu').
- apply (on_right_before (tas_on tKp) t'InI NPt').
  apply lt_le.
  apply (occurs_up_after_on_left tIO tJA tKp u'InJ NPu').
Qed.

Lemma over_equiv (p q:sig) : (eq_sig (over p q) (over_new p q)).
apply inc_sig_asym;[apply over_equiv_l|apply over_equiv_r].
Qed.








(*
 * OVERLAPPED
 *)
Definition overlapped_new (p q:sig) := (occurs (over q p) p).

Lemma overlapped_equiv_l (p q:sig) :
 (inc_sig (overlapped p q) (overlapped_new p q)).
intros t (I,(tIp,(J,(JInQ,(LT_LL,(LT_LR,LT_RR)))))).
exists I. split;[auto|].
exists (left I). split;[apply in_allen_left|].
exists J. split;[split;[|auto]|].
  + split;[apply (lt_le LT_LL)|auto].
  + exists I. split;[apply (tas_left tIp)|split;auto].
Qed.

Lemma overlapped_equiv_r (p q:sig) :
 (inc_sig (overlapped_new p q) (overlapped p q)).
intros t (I,(tIp,(t',(t'InI,(J,(t'Jq,(K,(t'Kp,(LTLL,LTRR))))))))).
exists I. split;[auto|].
exists J. split;[apply (tas_sig t'Jq)|split;[|split]].
- rewrite (tas_uniq_left (tas_mov tIp t'InI) t'Kp); auto.
- apply (allen_has_intersection t'InI (tas_allen t'Jq)).
- rewrite (tas_uniq_right (tas_mov tIp t'InI) t'Kp); auto.
Qed.

Lemma overlapped_equiv (p q:sig) :
 (eq_sig (overlapped p q) (overlapped_new p q)).
apply inc_sig_asym;[apply overlapped_equiv_l|apply overlapped_equiv_r].
Qed.





(*
 * OVERLAPS
 *)
Definition overlaps_new (p q:sig) := (occurs (over p q) p).

Lemma overlaps_equiv_l (p q:sig) : (inc_sig (overlaps p q) (overlaps_new p q)).
intros t (I,(tIp,(J,(JInQ,(LT_LL,(LT_LR,LT_RR)))))).
exists I. split;[auto|].
exists (left J). split;[split;[apply (lt_le LT_LL)|auto]|].
exists I. split;[split;[split;[|]|apply (tas_sig tIp)]|];auto.
- apply (lt_le LT_LL).
- exists J. split;[apply (in_sig_tas_left JInQ)|auto].
Qed.

Lemma overlaps_equiv_r (p q:sig) : (inc_sig (overlaps_new p q) (overlaps p q)).
intros t (I,(tIp,(t',(t'InI,(J,(t'Jp,(K,(t'Kq,(LTLL,LTRR))))))))).
exists I. split;[auto|].
exists K. split;[apply (tas_sig t'Kq)|split;[|split]].
- rewrite (tas_uniq_left (tas_mov tIp t'InI) t'Jp); auto.
- apply (allen_has_intersection (tas_allen t'Kq) t'InI).
- rewrite (tas_uniq_right (tas_mov tIp t'InI) t'Jp); auto.
Qed.

Lemma overlaps_equiv (p q:sig) : (eq_sig (overlaps p q) (overlaps_new p q)).
apply inc_sig_asym;[apply overlaps_equiv_l|apply overlaps_equiv_r].
Qed.






(*
 * STARTS
 *)
Definition starts_new (p q:sig) :=
 (or_sig (and_sig (occurs (sync p q) p)
                  (occurs (not_sig p) (occurs (sync p q) q)) )
         (and_sig (and_sig (init p) (init q))
                  (occurs (not_sig p) q) )).

Lemma starts_equiv_l (p q:sig) : (inc_sig (starts p q) (starts_new p q)).
intros t (I,(tIp,(J,(JInq,STR)))).
G STR; intros (LL,RR).
G (tas_inc_tas tIp JInq (Starts_inc STR)); intros tJq.
case_eq (left I);[intros Z;right|intros li LI;left].
- split;[split;[|]|].
  + exists I. auto.
  + exists J. split;[auto|rewrite <- LL;auto].
  + exists J. split;[auto|].
    apply(ilt_right_down_point tIp tJq RR).
- split.
  + exists I. split;[auto|].
    exists (left I). split;[apply (in_allen_left I)|].
    apply (sync_left tIp tJq LL LI).
  + exists J. split;[|].
    * apply (filter_tas tJq).
      exists (left J). split;[apply in_allen_left|].
      rewrite <- LL.
      apply (sync_left tIp tJq LL LI).
    * apply(ilt_right_down_point tIp tJq RR).
Qed.

Lemma starts_new_left_starts (p q:sig) :
 (inc_sig (and_sig (occurs (sync p q) p)
                   (occurs (not_sig p) (occurs (sync p q) q)) )
          (starts p q) ).
intros t ((I,(tIp,(t1,(t1InI,SY)))),(J,(tJO,(t2,(t2InJ,Np2))))).
G (inc_sig_allen_filter (tas_sig tJO)); intros JInq.
exists I. split;[auto|].
exists J;split;[auto|].
G (sync_shared_left__starts tIp tJO t1InI SY); intros LE.
split;[auto|].
apply (on_right_before (tas_on tIp) t2InJ Np2 (eq_le LE)).
Qed.

Lemma starts_new_right_starts (p q:sig) :
 (inc_sig (and_sig (and_sig (init p) (init q)) (occurs (not_sig p) q))
          (starts p q) ).
intros t (((I,(tIp,LI)),(J,(tJq,LJ))),OCN).
exists I. split;[auto|].
exists J. split;[apply (tas_sig tJq)|split].
- rewrite LI; auto.
- apply (occurs_not_right tIp tJq OCN).
  rewrite LI, LJ; auto.
Qed.

Lemma starts_equiv_r (p q:sig) : (inc_sig (starts_new p q) (starts p q)).
intros t [LE|RI].
- apply (starts_new_left_starts LE).
-  apply (starts_new_right_starts RI).
Qed.

Lemma starts_equiv (p q:sig) : (eq_sig (starts p q) (starts_new p q)).
apply inc_sig_asym;[apply starts_equiv_l|apply starts_equiv_r].
Qed.







(*
 * STARTED : started(p,q) = occurs(starts(q,p),p)
 *)

Definition started_new (p q:sig) := (occurs (starts q p) p).

Lemma started_equiv_l (p q:sig) : (inc_sig (started p q) (started_new p q)).
intros t (I,(tIp,(J,(JInQ,STR)))).
exists I. split;[auto|].
exists (left I); split;[apply in_allen_left|].
exists J. split;[split;[rewrite (proj1 STR); apply in_allen_left|auto]|].
exists I. split;[apply (tas_sig tIp)|apply (startedBy_Starts STR)].
Qed.

Lemma started_equiv_r (p q:sig) : (inc_sig (started_new p q) (started p q)).
intros t (I,((tInI,IInp),(t',(t'InI,(J,((t'InJ,JInq),(K,(KInp,(LL,LTRR))))))))).
G (in_allen_by_include_right t'InJ LL LTRR); intros t'InK.
exists I;split;[split;auto|].
exists J;split;[auto|split;[auto|]].
- rewrite (tas_uniq_left (tas_def t'InI IInp) (tas_def t'InK KInp)); auto.
- rewrite (tas_uniq_right (tas_def t'InI IInp) (tas_def t'InK KInp)); auto.
Qed.

Lemma started_equiv (p q:sig) : (eq_sig (started p q) (started_new p q)).
apply inc_sig_asym;[apply started_equiv_l|apply started_equiv_r].
Qed.









(*
 * ENDS
 *)
Definition ends_new (p q:sig) :=
 (or_sig (and_sig (over q (imp_sig q p)) (not_sig (over q p)))
         (and_sig (final p) (and_sig (final q) (occurs (not_sig p) q))) ).

Lemma ends_equiv_l (p q:sig) : (inc_sig (ends p q) (ends_new p q)).
intros t (I,(tIp,(J,(JInq,ENDS)))).
G (tas_inc_tas tIp JInq (Ends_inc ENDS)). intros tJq.
G ENDS; intros (LL,RR).
case_eq (right I);[intros ri RI;left;split|intros RI; right;split;[|split]].
- apply (ends_fix_over tIp tJq LL RR RI).
- intros (K,((tInK,KInq),(L,((tInL,LInp),(_,RRKL))))).
  G RRKL.
  rewrite <- (tas_uniq_right tIp (tas_def tInL LInp)).
  rewrite <- (tas_uniq_right tJq (tas_def tInK KInq)).
  rewrite RR.
  apply ilt_irrefl.
- exists I. auto.
- rewrite RR in RI; exists J. split;[auto|auto].
- exists J. split;[auto|].
  case_eq (left I).
  + intros LI; exfalso; apply (lt_eq0_false LL LI).
  + intros pli LI.
    exists pli. split;[split|].
    * rewrite LI in LL.
      rewrite <- ltS__le; auto.
    * rewrite <- RR.
      G (wf I); rewrite LI.
      apply ilt_trans; simpl; auto with arith.
    * apply (previous_left_out (tas_sig tIp) LI).
Qed.

Lemma ends_new_left_ends (p q:sig) :
 (inc_sig (and_sig (over q (imp_sig q p)) (not_sig (over q p)))
          (ends p q) ).
intros t ((J,(tJq,(I,(tIO,(LL,RR))))),NOV).
cut (p t).
- intros Pt.
  G (get_sig Pt).
  intros (K,tKp).
  exists K. split;[auto|].
  exists J. split;[apply (tas_sig tJq)|split].
  + apply (in_sig_imply_left tJq tKp tIO LL).
  + G NOV. apply contra. rewrite not_sig_def, not_not.
    intros DIFF.
    exists J. split;[auto|].
    exists K. split;[auto|split].
    * apply (in_sig_imply_left tJq tKp tIO LL).
    * G (in_sig_imply_right tJq tKp tIO RR).
      apply (diff_ile_ilt DIFF).
- apply (or_sig_exclude_left (tas_p tIO)).
  rewrite not_sig_def, not_sig_def, not_not.
  apply (tas_p tJq).
Qed.

Lemma ends_new_right_ends (p q:sig) :
 (inc_sig (and_sig (final p) (and_sig (final q) (occurs (not_sig p) q)))
          (ends p q) ).
intros t ((I,(tIp,RI)),((J,(tJq,RJ)),
                                (JJ,(tJJq,(ot,(otInJJ,NPot)))))).
- exists I. split;[auto|].
  exists J. split;[apply (tas_sig tJq)|split;[|]].
  + G (eq_allen_in_allen (tas_uniq tJJq tJq) otInJJ). intros otInJ.
    G (nat_compare_le_lt (left I) (left J));intros [LE|GT]; [exfalso|auto].
    G (on_right_before (tas_on tIp) otInJ NPot LE).
    rewrite RI, RJ; auto.
  + rewrite RI, RJ; auto.
Qed.

Lemma ends_equiv_r (p q:sig) : (inc_sig (ends_new p q) (ends p q)).
intros t [LE|RI].
- apply (ends_new_left_ends LE).
- apply (ends_new_right_ends RI).
Qed.


Lemma ends_equiv (p q:sig) : (eq_sig (ends p q) (ends_new p q)).
apply inc_sig_asym;[apply ends_equiv_l|apply ends_equiv_r].
Qed.




















(*
 * ENDED
 *)
Definition ended_new (p q:sig) := (occurs (ends q p) p).

Lemma ended_equiv_l (p q:sig) : (inc_sig (ended p q) (ended_new p q)).
intros t (I,(tIp,(J,(JInQ,EDB)))).
G EDB; intros (LTLL,RR).
exists I. split;[auto|].
exists (left J). split;[|].
- apply (inc_allen_has_left ((EndedBy_inc) EDB)).
- exists J. split;[split;[apply in_allen_left|auto]|].
  exists I. split;[apply (tas_sig tIp)|split;auto].
Qed.

Lemma ended_equiv_r (p q:sig) : (inc_sig (ended_new p q) (ended p q)).
intros t (I,((tInI,IInp),(t',(t'InI,(J,((t'InJ,JInq),(K,(KInp,(LTLL,RR))))))))).
G (in_allen_by_include_left t'InJ LTLL RR); intros t'InK.
exists I. split;[split;auto|].
exists J. split;[auto|split;[auto|]].
- rewrite (tas_uniq_left (tas_def t'InI IInp) (tas_def t'InK KInp)); auto.
- rewrite (tas_uniq_right (tas_def t'InI IInp) (tas_def t'InK KInp)); auto.
Qed.

Lemma ended_equiv (p q:sig) : (eq_sig (ended p q) (ended_new p q)).
apply inc_sig_asym;[apply ended_equiv_l|apply ended_equiv_r].
Qed.


(*
 * MEETS
 *)
Definition meets_new (p q:sig) := 
  (and_sig (not_sig (final p))
           (or_sig (ends p (not_sig q))
                   (or_sig (eq p (not_sig q)) (ended p (not_sig q))) )).

Lemma meets_equiv_l (p q:sig) : (inc_sig (meets p q) (meets_new p q)).
intros t (I,(tIp,(J,(JInQ,IJ)))).
G IJ; unfold Meets.
case_eq (right I);[intros ri RI|intros RI;BAD].
rewrite eq_fix; intros LJ.
G (previous_right RI); intros (pr,PR). rewrite PR in LJ.
G (previous_left_out JInQ (eq_sym LJ)). rewrite <- not_sig_def. intros NQpr.
G (get_sig NQpr); intros (K,(prInK,KInNq)).
split.
- intros (II,(tIIp,RII)).
  rewrite (tas_uniq_right tIp tIIp) in RI.
  rewrite RI in RII.
  inversion RII.
- cut ((right I)=(right K)).
  + G (nat_compare (left I) (left K)). intros [LT|[EQ|GT]].
    * right; right.
      exists I. split;[|exists K; split;[|split]];auto.
    * right; left.
      exists I. split;[|exists K; split;[|split]];auto.
    * left.
      exists I. split;[|exists K; split;[|split]];auto.
  + rewrite RI, PR, LJ.
    rewrite <- (not_sig_follow (p:=(not_sig q)) (I:=K) (J:=J) (pr:=pr)); auto.
    rewrite (eq_sig__in_sig J (eq_sig_not_not q)); auto.
Qed.

Lemma meets_equiv_r (p q:sig) : (inc_sig (meets_new p q) (meets p q)).
intros t (NotF,
         [(I,(tIp,(J,(JInNq,(LI,RI)))))|
         [(I,(tIp,(J,(JInNq,(LI,RI)))))|
          (I,(tIp,(J,(JInNq,(LI,RI)))))]]);
apply (meets_by_end tIp JInNq RI NotF).
Qed.

Lemma meets_equiv (p q:sig) : (eq_sig (meets p q) (meets_new p q)).
apply inc_sig_asym;[apply meets_equiv_l|apply meets_equiv_r].
Qed.




(*
 * DURING
 *)
Definition during_new (p q:sig) :=
 (and_sig (occurs_up p q)
          (and_sig (not_sig (occurs (not_sig q) (occurs_up p q)))
                   (not_sig (ends p q)) )).


Lemma during_occup (p q:sig) (t:nat) :
 (during p q t) ->
 (occurs_up p q t).
intros (I,(tIp,(J,(JInq,DRG)))).
exists I. split;[auto|].
G (During_in_allen_left DRG). intros LIInJ.
exists (left I). split;[apply in_allen_left|].
split.
 - G tIp; intros (_,IInp).
   split;[apply (lt_0lt (proj1 DRG))|exists I; auto].
 - split.
   + apply (in_sig_slice JInq LIInJ).
   + intros (_,(JJ,(LL,JJInq))).
     G (proj1 DRG). rewrite LL.
     apply (tas_uniq_left_wrong (tas_def LIInJ JInq)).
     rewrite LL; apply (in_sig_tas_left JJInq).
Qed.

Lemma during_Noccocc (p q:sig) :
 (inc_sig (during p q)
          (not_sig (occurs (not_sig q) (occurs_up p q))) ).
intros t (I,(tIp,(J,(JInq,DRG)))).
intros (K,((tInK,KInOU),(tt,(ttInK,NotQtt)))).
G NotQtt. apply not_not.
apply (tas_p (I:=J) (p:=q)).
split;[|auto].
apply (inc_allen_in_allen (I:=I)).
- apply (During_inc_allen DRG).
- G ttInK; apply eq_allen_in_allen.
  apply eq_allen_sym.
  apply (tas_uniq tIp).
  split;[auto|].
  apply ((inc_sig_allen_occurs_up (p:=p) (q:=q)) _ KInOU).
Qed.
 
Lemma during_Nends (p q:sig) : (inc_sig (during p q) (not_sig (ends p q))).
intros t Drg Ends. G Ends. G Drg.
apply (contra_extend ends_safe During_inc Ends_inc).
intros I J (LL1,RR1) (LL2,RR2).
G RR1. apply tilde; rewrite <- ile__not_ilt.
right; auto.
Qed.

Lemma during_equiv_l (p q:sig) : (inc_sig (during p q) (during_new p q)).
intros t drg.
split;[|split;[|]].
- apply (during_occup drg).
- apply (during_Noccocc drg).
- apply (during_Nends drg).
Qed.

Lemma during_equiv_r (p q:sig) : (inc_sig (during_new p q) (during p q)).
intros t.
intros ((I,(tIp,(tt,(ttI,((GT0,(II,(LI,IIp))),(Qtt,NUPQtt)))))),(NOCC,NENDS)).
rewrite LI in *. clear LI tt.
exists I. split;[assumption|].
G (get_sig Qtt). intros (J,ttJq). clear Qtt.
exists J. split;[apply (tas_sig ttJq)|].
rewrite <- (tas_uniq_left (tas_def ttI (tas_sig tIp))
                          (in_sig_tas_left IIp)) in *.
clear ttI IIp.
split.
- apply (in_allen_NoUp_left ttJq NUPQtt GT0).
- G(inat_compare (right J) (right I)); intros [LT|[EQ|GT]];
  [exfalso|exfalso|auto].
  + G NOCC. apply tilde. rewrite not_sig_def, not_not. clear NOCC.
    apply (occoccup tIp ttJq GT0 NUPQtt LT).
  + G NENDS; apply tilde. apply not_not. clear NENDS.
    exists I. split;[assumption|].
    exists J. split;[apply (tas_sig ttJq)|split;[|auto]]. 
    apply (in_allen_NoUp_left ttJq NUPQtt GT0).
Qed.

Lemma during_equiv (p q:sig) : (eq_sig (during p q) (during_new p q)).
apply inc_sig_asym;[apply during_equiv_l|apply during_equiv_r].
Qed.




(*
 * CONTAINS
 *)
Definition contains_new (p q:sig) := (occurs (during q p) p).

Lemma contains_equiv_l (p q:sig) : (inc_sig (contains p q) (contains_new p q)).
intros t (I,(tIp,(J,(JQ,CNT)))).
exists I. split;[assumption|].
exists (left J). split;[|].
- apply (contains_has_left CNT).
- exists J. split.
  + apply (in_sig_tas_left JQ).
  + exists I. split.
    * apply (tas_sig tIp).
    * apply (Contains_During CNT).
Qed.

Lemma contains_equiv_r (p q:sig) : (inc_sig (contains_new p q) (contains p q)).
intros t (I,(tIp,(t',(t'InI,(J,(t'Jq,(K,(KInp,DRG)))))))).
exists I. split;[assumption|].
exists J. split;[apply (tas_sig t'Jq)|].
apply During_Contains.
G DRG; apply eq_right_during.
G (tas_mov tIp t'InI); apply tas_uniq.
G KInp; apply tas_def.
apply ((During_inc_allen DRG) t' (tas_allen t'Jq)).
Qed.

Lemma contains_equiv (p q:sig) : (eq_sig (contains p q) (contains_new p q)).
apply inc_sig_asym;[apply contains_equiv_l|apply contains_equiv_r].
Qed.








End spec.

