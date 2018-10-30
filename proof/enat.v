Set Implicit Arguments.
Unset Strict Implicit.

Require Export basics.

Section enat.

Ltac G x := generalize x.

Ltac BAD := intros BAD; inversion BAD.

(*
 * extended nat
 *)
Inductive inat :=
 | Fix : nat -> inat
 | Inf : inat
.

Lemma not_inf_eq_fix x : (Inf = Fix x) <-> False.
split; [BAD|tauto].
Qed.

Lemma eq_fix x y: (Fix x)=(Fix y) <-> x=y.
split; auto.
intros EQ; inversion EQ; auto.
Qed.

Lemma fix_eq_fix x y : (Fix x)=(Fix y) <-> (x=y).
split; intros EQ; inversion EQ; auto.
Qed.

Lemma contra_inf x : ~(exists t, x=(Fix t)) -> x=Inf.
apply contra.
rewrite not_not.
case x; [|intros BAD;exfalso; apply BAD; auto].
intros n _; exists n; auto.
Qed.

(* ilt *)
Definition ilt (x y : inat) : Prop := match x,y with
 | (Fix n),(Fix m) => n<m
 | (Fix n),Inf => True
 | Inf,_ => False
end.

Lemma inat_compare x y : (ilt x y) \/ (x=y) \/ (ilt y x).
case x; case y; intros; simpl; auto.
G (nat_compare n0 n); intros [LT|[EQ|GT]].
- left; auto.
- right; left; auto.
- right; right; auto.
Qed.

Lemma ilt__0 (x:inat) : ~(ilt x (Fix 0)).
case x as [x|]; simpl; [auto with arith|auto].
Qed.

Lemma ilt_left_is_fix x y :  (ilt x y) -> (exists n, x=(Fix n)).
case x;[intros n _|BAD].
exists n; auto.
Qed.

Lemma ilt__inf x : (ilt (Fix x) Inf).
simpl; auto.
Qed.

Lemma not_ilt_inf_left x : ~(ilt Inf x).
case x; auto.
Qed.

Lemma ilt_irrefl x : ~(ilt x x).
case x; [apply lt_irrefl|auto].
Qed.

Lemma ilt_asym x y : (ilt x y) -> (ilt y x) -> False.
case x as [x |]; case y as [y |]; simpl; auto.
apply lt_asym.
Qed.

Lemma lt_ilt x y : (x < y) -> (ilt (Fix x) (Fix y)).
auto.
Qed.

Lemma lt_0ilt x y : (x < y) -> (ilt (Fix 0) (Fix y)).
intros LT.
apply (lt_ilt (lt_0lt LT)).
Qed.

(* ile *)
Definition ile (x y : inat) : Prop := (ilt x y) \/ (x=y).

Lemma ile__not_ilt x y : (ile x y) <-> ~(ilt y x).
unfold ile; case x as [x|]; case y as [y|]; simpl; auto; try tauto.
- rewrite eq_fix, <- le_fix_def.
  apply le__not_lt.
- rewrite not_inf_eq_fix; tauto.
Qed.

Lemma ile0 (x:inat) : (ile (Fix 0) x).
case x as [n|]; [|left;simpl;auto].
case n; [right|left];simpl;[auto|auto with arith].
Qed.

Lemma ile_inf x : (ile x Inf).
unfold ile.
case x as [|x];[left | right]; simpl; auto.
Qed.

Lemma ile_refl x : (ile x x).
unfold ile; case x as [n|]; simpl; auto.
Qed.

Lemma ile_antisym x y : (ile x y) -> (ile y x) -> x=y.
unfold ile.
intros [LT1 | EQ1] [LT2|EQ2]; auto.
exfalso; apply (ilt_asym LT1 LT2).
Qed.

Lemma eq_ile x y : (x=y) -> (ile x y).
intros EQ; rewrite EQ; apply ile_refl.
Qed.

Lemma eq_ile2 x y : (y=x) -> (ile x y).
intros EQ; rewrite EQ; apply ile_refl.
Qed.

Lemma ile_fix x y : (ile (Fix x) (Fix y)) <-> (x<=y).
unfold ile. simpl. 
rewrite fix_eq_fix, le_fix_def; tauto.
Qed.

Lemma ilt_ile x y : (ilt x y) -> (ile x y).
unfold ile; auto.
Qed.

Lemma ilt__not_ile x y : (ilt x y) <-> ~(ile y x).
rewrite ile__not_ilt, not_not; tauto.
Qed.

Lemma not_ile_inf_left x : ~ (ile Inf (Fix x)).
unfold ile.
intros [LT|EQ]; auto.
inversion EQ.
Qed.

Lemma diff_ile_ilt x y :
 (y<>x) ->
 (ile x y) ->
 (ilt x y).
unfold ile. intros DI [LT|EQ]; [auto|exfalso]; auto.
Qed.

Lemma inat_compare_lt_le x y : (ilt x y) \/ (ile y x).
G (inat_compare x y);intros [LT|[EQ|GT]];
[left|right;rewrite EQ;apply ile_refl|right;apply ilt_ile]; auto.
Qed.

Lemma ilt_ileS x y : (ilt (Fix x) y) -> (ile (Fix (S x)) y).
unfold ile; case y as [y|]; simpl; auto.
rewrite eq_fix.
rewrite <- le_fix_def.
auto with arith.
Qed.

Lemma ilt_succ (x:nat) (y:inat) : (ilt (Fix (S x)) y) -> (ilt (Fix x) y).
case y as [y|]; auto; simpl; auto with arith.
Qed.

Lemma ilt_trans  x y z : (ilt x y) -> (ilt y z) -> (ilt x z).
case x; case y; case z; simpl; auto; intros a b c.
- apply lt_trans.
- BAD.
Qed.

Lemma ile_trans x y z : (ile x y) -> (ile y z) -> (ile x z).
unfold ile.
intros [LT1 | EQ1] [LT2 | EQ2];[left|left|left|right].
- apply (ilt_trans LT1 LT2).
- rewrite <- EQ2; auto.
- rewrite EQ1; auto.
- rewrite EQ1; auto.
Qed.

Lemma ile_ilt_trans x y z : (ile x y) -> (ilt y z) -> (ilt x z).
unfold ile.
intros [LT | EQ].
- apply ilt_trans; auto.
- rewrite EQ; auto.
Qed.

Lemma le_ilt_trans x y z : (x <= y) -> (ilt (Fix y) z) -> (ilt (Fix x) z).
unfold ilt.
case z; auto.
apply le_lt_trans.
Qed.

Lemma lt_ilt_trans x y z : (x<y) -> (ilt (Fix y) z) -> (ilt (Fix x) z).
case z as [z|]; [apply lt_trans | auto].
Qed.

Lemma le_ile_trans x y z : (le x y) -> (ile (Fix y) z) -> (ile (Fix x) z).
unfold ile; rewrite le_fix_def.
intros [LT1 | EQ1] [LT2 | EQ2];[left|left|left|right].
- apply (lt_ilt_trans LT1 LT2).
- rewrite <- EQ2; auto.
- rewrite EQ1; auto.
- rewrite EQ1; auto.
Qed.

Lemma ilt_ile_trans x y z : (ilt x y) -> (ile y z) -> (ilt x z).
unfold ile.
intros LT1 [LT | EQ].
- apply (ilt_trans LT1 LT); auto.
- rewrite <- EQ; auto.
Qed.

Lemma lt_iltS_trans x y z :
(x < y) ->
(y < z) ->
(ilt (Fix (S x)) (Fix z)).
simpl.
intros LT1 LT2.
apply (le_lt_trans (lt_leS LT1) LT2).
Qed.

(* fiadd *)
Definition fiadd (x:nat) (y:inat) := match y with
 | (Fix y) => (Fix (x+y))
 | Inf => Inf
end.

End enat.
