(* https://github.com/coq/coq/commit/81c4c8bc418cdf42cc88249952dbba465068202c#diff-1c96c08a015db3ddaf186d60595064e9 *)

Require Export BinNums.
 Require Import BinPos RelationClasses (* Morphisms Setoid *)
  Equalities OrdersFacts GenericMinMax Bool NAxioms NProperties.
Require BinNatDef.

Definition divide p q := exists r, p*r = q.

Notation "( p | q )" := (divide p q) (at level 0).

Definition divide' p q := exists r, q = r*p.

 Notation "( p |' q )" := (divide' p q) (at level 0).

(* Admissable, not getting old versions of Coq just for this *)
 Axiom mul_comm : forall n m, n * m = m * n.

 Fixpoint divmod x y q u :=
   match x with
     | 0 => (q,u)
     | S x' => match u with
                 | 0 => divmod x' y (S q) y
                 | S u' => divmod x' y q u'
               end
   end.
 
 Definition div x y :=
   match y with
     | 0 => y
     | S y' => fst (divmod x y' 0 y')
end.

 Definition modulo x y :=
   match y with
     | 0 => y
     | S y' => y' - snd (divmod x y' 0 y')
   end.
 
Infix "/" := div : nat_scope.
Infix "mod" := modulo (at level 40, no associativity).

(* Good candidates *)

Require Import NZAxioms NZBase.
Axiom pred_succ : forall n, pred (S n) = n.
Axiom add_0_l : forall n, 0 + n = n.
Axiom add_succ_l : forall n m, (S n) + m = S (n + m).
Axiom mul_0_l : forall n, 0 * n = 0.
Axiom mul_succ_l : forall n m, (S n) * m = n * m + m.
Axiom sub_0_r : forall n, n - 0 = n.
Axiom sub_succ_r : forall n m, n - (S m) = pred (n - m).

Hint Rewrite
pred_succ add_0_l add_succ_l mul_0_l mul_succ_l sub_0_r sub_succ_r : nz.

Ltac nzsimpl := autorewrite with nz.
Axiom div_mod : forall x y, y<>0 -> x = y*(x/y) + x mod y.
Axiom mod_mul : forall a b, b<>0 -> (a*b) mod b = 0.

 Lemma mod_divide : forall a b, b <> 0 -> (a mod b = 0 <-> (b|a)).
 Proof.
  intros a b Hb. split.
  - intros Hab. exists (a/b). rewrite (div_mod a b Hb) at 2.
    rewrite Hab. now nzsimpl. 
  - intros (c,Hc). rewrite <- Hc, mul_comm. now apply mod_mul.
 Qed.

 Lemma mod_divide' : forall a b, b <> 0 -> (a mod b = 0 <-> (b|'a)).
 Proof.
  intros a b Hb. split.
  - intros Hab. exists (a/b). rewrite mul_comm.
    rewrite (div_mod a b Hb) at 1. rewrite Hab; now nzsimpl.
  - intros (c,Hc). rewrite Hc. now apply mod_mul.
 Qed.

 Lemma mod_divide_if : forall a b, b <> 0 -> a mod b = 0 -> (b|a).
 Proof.
  intros a b Hb.
  intros Hab. exists (a/b). rewrite (div_mod a b Hb) at 2.
  rewrite Hab. now nzsimpl. 
 Qed.

 Lemma mod_divide_if' : forall a b, b <> 0 -> a mod b = 0 -> (b|'a).
 Proof.
  intros a b Hb.
  intros Hab. exists (a/b). rewrite mul_comm. rewrite (div_mod a b Hb) at 1.
  rewrite Hab; now nzsimpl.
 Qed.

Require Import Patcher.Patch.

(*
Patch Proof mod_divide_if' mod_divide_if as patch_mod.
Print patch_mod.
*)
(* Above doesn't work because of rewrite location, but that's OK
  for now *)
(* We isolate to just the location we care about; this is an adaptation
   until PUMPKIN supports more features
 *)

Theorem mod_divide_if_2: forall a b, b <> 0 -> a mod b = 0 -> (b|'a).
Proof.
  intros a b Hb Hab. exists (a/b).
  rewrite mul_comm. symmetry. rewrite (div_mod a b Hb) at 2.
  rewrite Hab; now nzsimpl.
Qed.

Theorem mod_divide_if_2': forall a b, b <> 0 -> a mod b = 0 -> (b|a).
Proof.
  intros a b Hb Hab. exists (a/b).
  rewrite (div_mod a b Hb) at 2.
  rewrite Hab; now nzsimpl.
Qed.

Definition cut :=
  forall r a b,
    b * r = a ->
    a = r * b.

Patch Proof mod_divide_if_2 mod_divide_if_2' cut by (fun (H : cut) a b => H (a / b) a b) as patch.
Print patch.
Print patch_inv.

 Lemma Zmod_divides : forall a b, b<>0 ->
   (a mod b = 0 <-> exists c, a = b*c).
  Proof.
   intros. rewrite mod_divide; trivial.
   split; intros (c,Hc); exists c; auto.
  Qed.

Hint Resolve patch patch_inv.

Lemma Zmod_divides' : forall a b, b<>0 ->
   (a mod b = 0 <-> exists c, a = b*c).
  Proof.
   intros. rewrite mod_divide'; trivial.
   split; intros (c,Hc); exists c; auto.
  Qed.

(* Above proof goes through now! *)

(* Does iff case work th same way, if we rwrite in the same locaton? *)

Lemma mod_divide_2 : forall a b, b <> 0 -> (a mod b = 0 <-> (b|a)).
 Proof.
  intros a b Hb. split.
  - intros Hab. exists (a/b). rewrite (div_mod a b Hb) at 2.
    rewrite Hab. now nzsimpl. 
  - intros (c,Hc). rewrite <- Hc, mul_comm. now apply mod_mul.
 Qed.

 Lemma mod_divide_2' : forall a b, b <> 0 -> (a mod b = 0 <-> (b|'a)).
 Proof.
  intros a b Hb. split.
  - intros Hab. exists (a/b). rewrite mul_comm. symmetry.
    rewrite (div_mod a b Hb) at 2. rewrite Hab; now nzsimpl.
  - intros (c,Hc). rewrite Hc. now apply mod_mul.
 Qed.

(* Not yet, but not a big deal for now *)
(* all the adjustments we make are just because we don't handle changes
   in hypotheses yet, really *)
