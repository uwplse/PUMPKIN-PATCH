(* Variants for second proof *)

Require Import Arith NPeano.

(*
   Things we can change:
   1. Outside/inside induction
   2. Apply to conclusion/apply to hypothesis/both
   3. Apply function/use hint or rewrite db/use special tactic
*)

(* Variant 1: Outside, conclusion, function *)

Theorem old2_v1:
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n <= S p.
Proof.
  intros. apply le_S. induction H0; auto.
Qed.

(* Variant 2: Inside, conclusion, function *)

Theorem old2_v2:
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n <= S p.
Proof.
  intros. induction H0; auto with arith.
Qed.

(* Variant 3: Outside, conclusion, rws [1] *)

Theorem old2_v3:
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n <= S p.
Proof.
  intros. rewrite le_S; auto. induction H0; auto.
Qed.

(* Variant 4: Inside, conclusion, rw [2] *)

Theorem old2_v4:
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n <= S p.
Proof.
  intros. induction H0.
  - rewrite le_S; auto.
  - constructor. auto.
Qed.
