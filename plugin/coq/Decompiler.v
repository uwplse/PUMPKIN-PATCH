Add LoadPath "coq".
Require Import Patcher.Patch.

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

