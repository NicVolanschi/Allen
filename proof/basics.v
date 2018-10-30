Set Implicit Arguments.
Unset Strict Implicit.

Require Export Bool List Peano Arith Bool_nat.
Require Export Compare.
Require Export Omega Recdef.
Require Export Classical.
Require Export Decidable.

Section basics.

Ltac G x := generalize x.

Ltac BAD := intros BAD; inversion BAD.

(*
 * Props
 *)
Lemma contra (P Q : Prop) : (~Q -> ~P) -> P -> Q.
tauto.
Qed.

Lemma ncontra (P Q : Prop) : (Q -> P) -> ~P -> ~Q.
tauto.
Qed.

Lemma not_not : forall P, (~~P) <-> P.
intros P.
tauto.
Qed.

Lemma not_and__or_not (P Q:Prop) : ~(P /\Q) <-> (~P \/ ~Q).
tauto.
Qed.

Lemma or_not_not_and (P Q:Prop) : (~P \/ ~Q) -> ~(P /\Q).
tauto.
Qed.

Lemma tilde P : ~P -> P -> False.
tauto.
Qed.

Lemma P_compare (P Q:Prop) : (P<->Q) \/ ~(P<->Q).
tauto.
Qed.

Lemma p1 (P Q:Prop) : (P<->Q) -> (P->Q).
tauto.
Qed.

Lemma pcheck (P:Prop) : P \/ ~P.
tauto.
Qed.

Lemma dec_imp (A B C:Prop) : (A -> B) -> ((~A) -> C) -> (B \/ C).
tauto.
Qed.

Lemma not_imply2 (P Q R:Prop) : ~(P -> Q -> R) -> (P /\ Q /\ ~R).
tauto.
Qed.

Lemma not_imply_and (P Q:Prop) : ~(P -> Q) -> (P /\ ~Q).
tauto.
Qed.

Lemma andP (P1 P2:Prop) : P1 -> P2 -> (P1 /\ P2).
auto.
Qed.


(*
 * nat
 *)

Lemma lt_le x y : (x<y) -> (x<=y).
auto with arith.
Qed.

Lemma eq_le x y : (x=y) -> (x<=y).
intros EQ; rewrite EQ; apply le_refl.
Qed.

Lemma eq_le2 x y : (y=x) -> (x<=y).
intros EQ; rewrite EQ; apply le_refl.
Qed.

Lemma nat_compare x y : (x<y) \/ (x=y) \/ (y<x).
G (lt_eq_lt_dec x y).
intros [[A|B]|C]; [left|right;left|right;right]; auto.
Qed.

Lemma nat_compare_lt_le x y : (x<y) \/ (y<=x).
G (nat_compare x y);intros [LT|[EQ|GT]];
[left|right;rewrite EQ|right;apply lt_le]; auto.
Qed.

Lemma not0 x : (x<>0) -> (exists n, x = (S n)).
case x as [|x].
- intros BAD. exfalso. apply BAD; auto.
- exists x; auto.
Qed.

Lemma nat_compare_et x y : (x<=y) \/ (y<x).
G (nat_compare x y); intros[LE|[EQ|GT]];[left|left;auto|right;auto].
 - apply (lt_le LE).
- rewrite EQ; apply le_refl.
Qed.

Lemma nat_compare_le_lt x y : (x<=y) \/ (y<x).
G (nat_compare x y);intros [LT|[EQ|GT]];
[left;apply lt_le|left;rewrite EQ|right]; auto.
Qed.

Lemma nlt0 x : ~(x<0).
auto with arith.
Qed.

Lemma lt_0lt x y : (x < y) -> (0 < y).
case y as [|y]; auto with arith.
BAD.
Qed.
      
Lemma lt_add_S x y : x < x + (S y).
replace (x + (S y)) with (S (x+y)); auto.
auto with arith.
Qed.

(* le *)
Lemma le_fix_def x y : x<=y <-> (x<y \/ x=y).
split.
- intros LE.
  generalize (le_le_S_eq _ _ LE); intros [LT | EQ]; [left |right]; auto.
-intros [LT | EQ]; [ | rewrite EQ]; auto with arith.
Qed.

Lemma diff_le_lt x y :
 (y<>x) ->
 (x<=y) ->
 (x<y).
rewrite le_fix_def. intros DI [LT|EQ]; [auto|exfalso]; auto.
Qed.

Lemma le__not_lt x y : (x <= y) <-> ~(y < x).
split.
- apply le_not_lt.
- intros NLT. rewrite le_fix_def. 
  G (nat_compare x y); intros [LT|[EQ|GT]]; [left; auto | right; auto |exfalso].
  apply (NLT GT).
Qed.

Lemma le_0 (x:nat) : (0<=x).
auto with arith.
Qed.

Lemma le__le_succ x y : (x<=y) <-> ((S x)<=(S y)).
split; auto with arith.
Qed.

Lemma le_succ (x y : nat) : (x<=y) -> (S x)<=(S y).
apply (proj1 (le__le_succ x y)).
Qed.

Lemma le_succ_r (x y:nat) : (S x)<=(S y) -> (x<=y).
apply (proj2 (le__le_succ x y)).
Qed.

Lemma ltS__le x y : (x<(S y)) <-> (x<=y).
split; auto with arith.
Qed.

Lemma ltSucc x y : x < (S y) -> x < y \/ x=y.
rewrite ltS__le, le_fix_def; auto.
Qed.

Lemma ltS_lt_false x y : x < (S y) -> ~(y < x).
rewrite <- le__not_lt, ltS__le; auto.
Qed.

Lemma lt_leS x y : (x<y) -> (S x)<=y.
auto.
Qed.

Lemma leS_lt x y : (S x)<=y -> (x<y).
auto.
Qed.

Lemma le_add_le x y d : x+d<=y -> x<=y.
G (le_plus_l x d).
apply le_trans.
Qed.

Lemma le_add_le_sub x y d : (d+x)<=y -> x<=y-d.
intros LE.
G (minus_le_compat_r _ _ d LE).
replace (d+x-d) with x; [auto|auto with arith].
Qed.

Lemma Sle x y : ((S x) <= y) -> (x <= (y-1)).
case y;[BAD|].
intros n; replace (S n - 1) with n;auto with arith.
Qed.

Lemma lt_add_lt_sub_left t T r :
 0<r ->
 t < T+r ->
 t - T < r.
omega.
Qed.

Lemma le_lt_trans x y z : (x<=y) -> (y<z) -> (x<z).
rewrite le_fix_def.
intros [LT1|EQ] LT2.
- apply (lt_trans _ _ _ LT1 LT2).
- rewrite EQ; auto.
Qed.

Lemma too_small_segment x y :  ~(x<y<(S x)).
intros (LT,LTS).
G (ltSucc LTS); intros [LT2|EQ].
- apply (lt_asym _ _ LT LT2).
- rewrite EQ in LT.
  apply (lt_irrefl _ LT).
Qed.

Lemma single_segment x y : (x<=y) -> y<(S x) -> x=y.
intros LE LT.
generalize (le_le_S_eq _ _ LE); intros [LT2 | EQ]; auto.
generalize (le_not_gt _ _ LT2).
replace (S x > y) with (y < S x); auto.
intros BAD; exfalso; auto.
Qed.

Lemma add_sub_same x y : x = x + y - y.
replace (x+y) with (y+x);[rewrite minus_plus; auto|auto with arith].
Qed.

Lemma addSsubS x y : x = y + S x - S y.
replace (y+(S x)) with ((S y)+x);[rewrite minus_plus; auto|].
replace (S y + x) with (S (y+x)); auto.
Qed.

Lemma lt_getS x y : (x < y) -> (exists py, y=(S py)).
case_eq y;[intros _;BAD|intros n Y _; exists n; auto].
Qed.

Lemma lt_eq0_false x y : (x < y) -> (y=0) -> False.
intros LT EQ; rewrite EQ in LT; inversion LT.
Qed.

Lemma gt0_has_previous (x y:nat) :
 (x < y) ->
 (exists py, y=(S py)).
intros LL.
case_eq y;[intros EQ; exfalso; rewrite EQ in LL; inversion LL|].
intros py Y; exists py; auto.
Qed.

End basics.
