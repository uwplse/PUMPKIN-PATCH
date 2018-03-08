Require Import List.
Require Import Nat.
Require Import PeanoNat.

(******************************************************************************)
(******************************************************************************)
(* This modules defines explicitly typed syntax and static semantics for the  *)
(* simply typed lambda calculus, along with associated utilities. The lower-  *)
(* level details of the module --- relating to deBruijn indices, for instance *)
(* --- are not critical for understanding the main tutorial.                  *)
(******************************************************************************)
(******************************************************************************)

Module Syntax.

(* Simple types for the lambda-calculus: one base type and arrow types *)
Inductive type : Set :=
| Base : type
| Arrow : type -> type -> type.

(* Explicitly typed lambda-expressions using deBruijn indices *)
Inductive expr : Set :=
| Var : nat -> expr
| Fun : type -> expr -> expr
| App : expr -> expr -> expr.

(* Value predicate on lambda-expressions (for closed evaluation) *)
Inductive value : expr -> Prop :=
| FunV t e : value (Fun t e).

(* Shield an open expression from i bindings after j bindings *)
Fixpoint shield (e : expr) (i j : nat) : expr :=
  match e with
  | Var k => Var (if k <? j then k else i + k)
  | Fun t e => Fun t (shield e i (succ j))
  | App e1 e2 => App (shield e1 i j) (shield e2 i j)
  end.
Notation "e >> i" := (shield e i 0) (at level 20, no associativity).

(* Capture-avoiding substitution of open expression e' for index i *)
Fixpoint subst (e : expr) (i : nat) (e' : expr) : expr :=
  match e with
  | Var j =>
    if i =? j
    then e' >> i (* Substitute after shielding variables from capture *)
    else Var (if j <? i then j else pred j) (* Delete the substituted index *)
  | Fun t e => Fun t (subst e (succ i) e') (* Track newly "free" variable *)
  | App e1 e2 => App (subst e1 i e') (subst e2 i e')
  end.
Notation "e1 [ i \ e2 ]" := (subst e1 i e2) (at level 30, no associativity).
Notation "e1 <- e2" := (subst e1 0 e2) (at level 28, no associativity).

End Syntax.

Module Typing.

Import Syntax.

(* Helper function *)
Fixpoint onth {A : Type} (xs : list A) (i : nat) : option A :=
  match xs, i with
  | _ :: xs', S i' => onth xs' i'
  | x :: _, O => Some x
  | _, _ => None
  end.

Lemma onth_app_r {A : Type} (xs ys : list A) (i : nat) :
  onth (xs ++ ys) (length xs + i) = onth ys i.
Proof. induction xs; try reflexivity. assumption. Qed.

Lemma onth_app_l {A : Type} (xs ys : list A) (i : nat) :
  i < length xs -> onth (xs ++ ys) i = onth xs i.
Proof.
  revert i. induction xs; simpl; intros i H.
  - inversion H.
  - destruct i; try reflexivity. apply IHxs, Lt.lt_S_n. assumption.
Qed.

(* Typing rules *)
Inductive typing : list type -> expr -> type -> Prop :=
| VarTy G i t :
    onth G i = Some t ->
    typing G (Var i) t
| FunTy G e t1 t2 :
    typing (t1 :: G) e t2 ->
    typing G (Fun t1 e) (Arrow t1 t2)
| AppTy G e1 e2 t2 t1 :
    typing G e1 (Arrow t2 t1) -> typing G e2 t2 ->
    typing G (App e1 e2) t1.

(* Type equality *)
Fixpoint type_eq (t1 t2 : type) : bool :=
  match t1, t2 with
  | Base, Base => true
  | Arrow t1 t2, Arrow t3 t4 => type_eq t1 t3 && type_eq t2 t4
  | _, _ => false
  end.

(* Correctness of type equality *)
Lemma type_eq_ok (t1 t2 : type) : type_eq t1 t2 = true <-> t1 = t2.
Proof.
  revert t2. induction t1 as [|t11 IHt11 t12 IHt12]; destruct t2 as [|t21 t22].
  - split; reflexivity.
  - split; discriminate.
  - split; discriminate.
  - simpl. rewrite Bool.andb_true_iff, IHt11, IHt12.
    split; inversion 1; subst; auto.
Qed.

Theorem type_eq_refl (t : type) : type_eq t t = true.
Proof. rewrite type_eq_ok. reflexivity. Qed.

(* Type inference *)
Fixpoint type_of (G : list type) (e : expr) : option type :=
  match e with
  | Var i => onth G i
  | Fun t e =>
    match type_of (t :: G) e with
    | Some t' => Some (Arrow t t')
    | None => None
    end
  | App e1 e2 =>
    match type_of G e1, type_of G e2 with
    | Some (Arrow t2 t), Some t2' => if type_eq t2 t2' then Some t else None
    | _, _ => None
    end
  end.

(* Correctness of type inference *)
Lemma type_of_ok (G : list type) (e : expr) (t : type) :
  type_of G e = Some t <-> typing G e t.
Proof.
  revert t G. induction e as [i|t0|]; intros t G; split; simpl.
  - constructor. assumption.
  - inversion 1. subst. assumption.
  - destruct (type_of (t0 :: G) e) eqn:H; try discriminate.
    inversion 1. subst. rewrite IHe in H. constructor. assumption.
  - inversion 1. subst. rewrite <- IHe in H4. simpl. rewrite H4. reflexivity.
  - destruct (type_of G e1) eqn:He1; try discriminate.
    destruct t0 eqn:Ht0; try discriminate. rewrite IHe1 in He1.
    destruct (type_of G e2) eqn:He2; try discriminate. rewrite IHe2 in He2.
    destruct (type_eq t1_1 t1) eqn: Ht1; try discriminate.
    rewrite type_eq_ok in Ht1. inversion 1. subst. apply AppTy with (t2 := t1); assumption.
  - inversion 1. subst. rewrite <- IHe1 in H3. rewrite <- IHe2 in H5. rewrite H3, H5.
    rewrite type_eq_refl. reflexivity.
Qed.

(* Shielding preserves typing of open expressions *)
Lemma shield_typing e t : forall G1 G2 G3,
    typing (G1 ++ G3) e t ->
    typing (G1 ++ G2 ++ G3) (shield e (length G2) (length G1)) t.
Proof.
  revert t. induction e as [i|t0 e IHe|]; intros t G1 G2 G3 H; simpl.
  - constructor. inversion H; subst. destruct (i <? length G1) eqn:Hi.
    + rewrite Nat.ltb_lt in Hi. rewrite onth_app_l; rewrite onth_app_l in H2; assumption.
    + rewrite Nat.ltb_ge in Hi. apply Minus.le_plus_minus in Hi. rewrite Hi in *.
      rewrite onth_app_r in H2. rewrite Nat.add_shuffle3, !onth_app_r. assumption.
  - inversion H; subst. apply FunTy. exact (IHe t2 (t0 :: G1) G2 G3 H4).
  - inversion H; subst. apply AppTy with (t2 := t2).
    + apply IHe1. assumption.
    + apply IHe2. assumption.
Qed.

(* Well-typed substitution with an open expression preserves typing *)
Lemma subst_typing e t : forall G1 G2 e' t',
    typing G2 e' t' ->
    typing (G1 ++ t' :: G2) e t ->
    typing (G1 ++ G2) (e [ length G1 \ e' ]) t.
Proof.
  revert t. induction e as [i|t0|]; intros t G1 G2 e' t' He' He; simpl.
  - destruct (length G1 =? i) eqn:Hi.
    + rewrite Nat.eqb_eq in Hi. rewrite <- Hi in He. clear Hi i.
      apply shield_typing with (G1 := nil). inversion He; subst.
      rewrite (plus_n_O (length G1)), onth_app_r in H1. simpl in H1. inversion H1. subst.
      assumption.
    + destruct (i <? length G1) eqn:Hi'.
      * rewrite Nat.ltb_lt in Hi'. constructor. inversion He; subst.
        rewrite onth_app_l; try rewrite onth_app_l in H1; assumption.
      * rewrite Nat.ltb_antisym, Bool.negb_false_iff, Nat.leb_le, Nat.le_lteq in Hi'.
        rewrite Nat.eqb_neq in Hi. inversion Hi'; try contradiction. clear Hi Hi'.
        constructor. inversion He; subst. rewrite (Minus.le_plus_minus _ _ H) in *.
        simpl in *. rewrite plus_n_Sm in H2. rewrite onth_app_r. rewrite onth_app_r in H2.
        simpl in *. assumption.
  - inversion He; subst. constructor. apply IHe with (G1 := t0 :: G1) (t' := t'); assumption.
  - inversion He; subst. apply AppTy with (t2 := t2).
    + apply IHe1 with (t' := t'); assumption.
    + apply IHe2 with (t' := t'); assumption.
Qed.

(* Well-typed substitution with a closed expression preserves typing *)
Lemma subst_typing' e t : forall G e' t',
    typing nil e' t' ->
    typing (G ++ t' :: nil) e t ->
    typing G (e [ length G \ e']) t.
Proof.
  (* In this example, we're actually reusing the same implementation of
   * substitution, so we'll just apply the more general lemma.
   *)
  intros G e' t'. assert (H := subst_typing e t G nil e' t').
  rewrite app_nil_r in H. exact H.
Qed.

End Typing.

Export Syntax.
Export Typing.