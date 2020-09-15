Add LoadPath "coq".
Require Import Patcher.Patch.
Require Import PeanoNat List.
Import ListNotations.
Require Import Omega.

(* Basic apply *)
Decompile 3.

(* Intro(s) *)
Decompile (fun x => x).
Decompile (fun x y => x).
Decompile (fun _ y => y).
Decompile (fun x _ => x).
Decompile (fun _ _ x => x).

(* Reflexivity *)
Decompile @eq_refl.
Decompile (@eq_refl nat 0).
Decompile (eq_refl 0).

(* Rewrite *)
Decompile (@eq_rect nat).
Decompile (@eq_rect_r nat 0 (fun _ => unit) tt 0 eq_refl).

(* w.h.-reduce rewrite  *)
Decompile ((fun x => (fun T => @eq_rec T) nat 0 (fun _ => True) I 0 x) eq_refl).

(* Nested rewrites *)
Decompile (fun (x : nat) (H : x = 0) =>
eq_ind_r (fun x0 : nat => x0 = x0)
  (eq_ind x (fun n : nat => n = n) eq_refl 0 H) H).

(* Simple rewrite-in *)
Decompile (fun (a b : nat) (H : a = b) (H0 : b = a) =>
let H1 : a = a := eq_ind b (fun b0 : nat => a = b0) H a H0 in H1).

(* Nested rewrite-ins *)
Decompile (fun (a b : nat) (H : a = b) (H0 : b = a) =>
let H1 : a = a := eq_ind b (fun b0 : nat => a = b0) H a H0 in
let H2 : b = b := eq_ind_r (fun a0 : nat => a0 = a0) H1 H0 in
let H3 : a = a := eq_ind b (fun b0 : nat => b0 = b0) H2 a H0 in H3).

(* Let-in resembles rewrite-in, but hypothesis isn't a rel term *)
Decompile (fun (a b : nat) (H : a = b) (H0 : b = a) =>
let q : (fun b0 : nat => a = b0) a := 
  eq_ind b (fun b0 : nat => a = b0)
    ((fun x : a = b => x) H) a H0 in
 (eq_refl a)).

(* Let-in resembles rewrite-in, but H is used later in the proof *)
Decompile (fun (a b : nat) (H : a = b) (H0 : b = a) =>
let q : (fun b0 : nat => a = b0) a :=
  eq_ind b (fun b0 : nat => a = b0) H a H0 in
let q' : a = b := H in eq_refl a).

(* Left and Right *)
Decompile (fun (a b : Prop) (H : a) => or_introl H).
Decompile (fun (a b : Prop) (H : b) => or_intror H).

(* Split *)
Decompile (fun (a b : Prop) (H : a) (H0 : b) => conj H H0).
Decompile (conj (or_introl eq_refl) (or_intror eq_refl)).

(* Induction *)
(* forall x : nat, x + 0 = x *)
Decompile (fun x : nat =>
nat_ind (fun x0 : nat => x0 + 0 = x0) eq_refl
  (fun (x0 : nat) (IHx : x0 + 0 = x0) =>
   eq_ind_r (fun n : nat => S n = S x0) eq_refl IHx) x).

(* forall (X : Type) (xs ys zs : list X),
       xs ++ ys ++ zs = (xs ++ ys) ++ zs *)
Decompile (fun (X : Type) (xs ys zs : list X) =>
list_ind
  (fun xs0 : list X =>
   forall ys0 zs0 : list X,
   xs0 ++ ys0 ++ zs0 = (xs0 ++ ys0) ++ zs0)
  (fun ys0 zs0 : list X => eq_refl)
  (fun (a : X) (xs0 : list X)
     (IHxs : forall ys0 zs0 : list X,
             xs0 ++ ys0 ++ zs0 = (xs0 ++ ys0) ++ zs0)
     (ys0 zs0 : list X) =>
   eq_ind_r
     (fun l : list X => a :: l = a :: (xs0 ++ ys0) ++ zs0)
     eq_refl (IHxs ys0 zs0)) xs ys zs).

(* forall P Q : Prop, P \/ Q -> P \/ Q *)
Decompile (fun (P Q : Prop) (H : P \/ Q) =>
or_ind (fun H0 : P => or_introl H0)
  (fun H0 : Q => or_intror H0) H).

(* forall (A : Type) (l : list A), rev (rev l) = l *)
Decompile List.rev_involutive.

(* forall (n m : nat), n = 0 \/ n <> 0 *)
(* NOTICE: m is reverted and reintroduced *)
Decompile (fun n m : nat =>
nat_ind (fun n0 : nat => nat -> n0 = 0 \/ n0 <> 0)
  (fun _ : nat => or_introl eq_refl)
  (fun (n' : nat) (_ : nat -> n' = 0 \/ n' <> 0) (_ : nat)
   => or_intror (not_eq_sym (O_S n'))) n m).

Theorem explosion : forall P : Prop, False -> P.
Proof. intros P H. induction H as []. Qed.

Decompile explosion.

Decompile Decidable.dec_and.

(* Exists *)
Theorem exists_1 : 
  { x & x + 0 = 0 } ->
  { x & 0 + x = 0 }.
Proof.
intros H.
induction H as [x p]. 
- exists x.
  rewrite (Nat.add_comm x 0) in p.
  apply p.
Qed.
Decompile exists_1.

(* More complicated proof terms. *)
Theorem example_1 : forall (x : nat) (P : x = x), 
  x = x /\ x = x.
Proof.
intros x P.
split; apply (eq_sym P).
Qed.
Decompile example_1.

Theorem example_2 : 
  { _ : nat &
  (forall x y : nat, x = y -> x = y) /\
  (forall x y : nat, x = y -> y = x) }.
Proof.
exists 0.
split; intros x y H.
- apply H.
- symmetry. 
  apply H.
Qed.
Decompile example_2.

Theorem example_3 :
  forall (X : Type) (xs ys : list X),
    rev ys = xs -> rev xs = ys.
Proof.
intros X xs ys H.
revert xs ys H. (* should collapse intros/revert *)
induction xs; intros ys H;
 simpl; rewrite <- rev_involutive;
  rewrite H; reflexivity.
Qed.
Decompile example_3.

(* auto. *)
Decompile (fun x : nat => x) with "auto".
Decompile (fun (x : nat) (y : True) => x) with "auto".
Decompile (fun (x : False) => False_ind True x) with "auto".
Theorem auto_ex_1 : 0 = 0 \/ 1 = 1. Proof. auto. Qed.
Decompile auto_ex_1 with "auto".
Theorem auto_ex_2 : forall (A : Type) (x y : A), x = y -> y = x. Proof. auto. Qed.
Decompile auto_ex_2 with "auto".
Theorem auto_ex_3 : 
  (forall (P Q : Prop), P -> (P -> Q) -> Q) /\ 
  (forall (P Q R : Prop), (P -> Q) -> (Q -> R) -> (P -> R)).
Proof. auto. Qed.
Decompile auto_ex_3 with "auto".
Theorem auto_ex_4 : forall (x y z : nat), x + (y + z) = (x + y) + z.
Proof. intros. induction x. auto. simpl. rewrite IHx. auto. Qed.
Decompile auto_ex_4 with "auto".

(* omega. *)
Theorem omega_ex_1 : forall x : nat, x >= 0. Proof. intros. omega. Qed.
Decompile omega_ex_1 with "omega".
Theorem omega_ex_2 : forall x y : nat, x > y -> x <> y. Proof. intros. omega. Qed.
Decompile omega_ex_2 with "omega".

(* lia. *)
Open Scope Z_scope.
Require Import Lia.
Theorem lia_ex_1 : forall z : Z, z > 0 -> 2 * z + 1 > z.
Proof. intros. lia. Qed.
Decompile lia_ex_1 with "lia".

