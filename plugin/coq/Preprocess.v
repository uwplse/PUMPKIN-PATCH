Require Import Patcher.Patch.
Require List.

Open Scope list_scope.

Inductive vector (A : Type) : nat -> Type :=
| nilV : vector A 0
| consV : forall (n : nat), A -> vector A n -> vector A (S n).

(** Test a few hand-written functions on vector **)
Section VectorTests.

  Arguments nilV {A}.
  Arguments consV {A}.

  Definition emptyV (A : Type) (xs : {n:nat & vector A n}) : bool :=
    match projT2 xs with
    | consV _ _ _ => false
    | nilV => true
    end.
  Preprocess emptyV as emptyV'.

  Definition headV (A : Type) (n : nat) (xs : vector A (S n)) : A :=
    match xs in vector _ n return (match n with S _ => True | O => False end) -> A with
    | consV _ x _ => True_rect x
    | nilV => False_rect A
    end
      I.
  Preprocess headV as headV'.

  Definition tailV (A : Type) (n : nat) (xs : vector A (S n)) : vector A n :=
    match xs in vector _ (S n) return vector A n with
    | consV _ _ xs => xs
    end.
  Preprocess tailV as tailV'.

End VectorTests.

(** Test a sample of List functions and proofs **)
(* NOTE: Untranslated constants length, app, and List.* remain in many translated terms. *)
Section ListTests.

  Preprocess List.hd as actual_hd.
  Definition expected_hd (A : Type) (default : A) (l : list A) : A :=
    list_rect (fun _ : list A => A) default
              (fun (x : A) (_ : list A) (_ : A) => x) l.
  Lemma test_hd : actual_hd = expected_hd. Proof. reflexivity. Qed.

  Preprocess List.hd_error as actual_hd_error.
  Definition expected_hd_error (A : Type) (l : list A) : option A :=
    list_rect (fun _ : list A => option A) None
              (fun (x : A) (_ : list A) (_ : option A) => Some x) l.
  Lemma test_hd_error : actual_hd_error = expected_hd_error. Proof. reflexivity. Qed.

  Preprocess List.tl as actual_tl.
  Definition expected_tl (A : Type) (l : list A) : list A :=
    list_rect (fun _ : list A => list A) nil (fun (_ : A) (m _ : list A) => m) l.
  Lemma test_tl : actual_tl = expected_tl. Proof. reflexivity. Qed.

  Preprocess List.In as actual_In.
  Definition expected_In (A : Type) (a : A) (l : list A) : Prop :=
    list_rect (fun _ : list A => A -> Prop) (fun _ : A => False)
              (fun (a0 : A) (_ : list A) (In : A -> Prop) (a1 : A) => a0 = a1 \/ In a1) l
              a.
  Lemma test_In : actual_In = expected_In. Proof. reflexivity. Qed.

  Preprocess List.nil_cons as actual_nil_cons.
  Definition expected_nil_cons (A : Type) (x : A) (l : list A) : nil <> (x :: l) :=
    fun (H : nil = (x :: l)) =>
      let H0 : False :=
          eq_ind nil
                 (fun e : list A =>
                    list_rect (fun _ : list A => Prop) True
                              (fun (_ : A) (_ : list A) (_ : Prop) => False) e) I
                 (x :: l) H
      in
      False_ind False H0.
  Lemma test_nil_cons : actual_nil_cons = expected_nil_cons. Proof. reflexivity. Qed.

  Preprocess List.destruct_list as actual_destruct_list.
  Definition expected_destruct_list (A : Type) (l : list A) : {x : A & {tl : list A | l = (x :: tl)%list}} + {l = nil} :=
    list_rect
      (fun l0 : list A =>
         {x : A & {tl : list A | l0 = (x :: tl)}} + {l0 = nil})
      (inright eq_refl)
      (fun (a : A) (tail : list A)
           (_ : {x : A & {tl : list A | tail = (x :: tl)}} + {tail = nil}) =>
         inleft
           (existT (fun x : A => {tl : list A | (a :: tail) = (x :: tl)})
                   a
                   (exist (fun tl : list A => (a :: tail) = (a :: tl)) tail
                          eq_refl))) l.
  Lemma test_destruct_list : actual_destruct_list = expected_destruct_list. Proof. reflexivity. Qed.

  Preprocess List.hd_error_tl_repr as actual_hd_error_tl_repr.
  Definition expected_hd_error_tl_repr (A : Type) (l : list A) :
    forall (a : A) (r : list A),
      List.hd_error l = Some a /\ List.tl l = r <-> l = (a :: r)
    :=
      list_ind
        (fun l0 : list A =>
           forall (a : A) (r : list A),
             List.hd_error l0 = Some a /\ List.tl l0 = r <-> l0 = (a :: r))
        (fun (a : A) (r : list A) =>
           conj
             (fun H : None = Some a /\ nil = r =>
                and_ind
                  (fun (H0 : None = Some a) (_ : nil = r) =>
                     let H2 : False :=
                         eq_ind None
                                (fun e : option A =>
                                   option_rect (fun _ : option A => Prop)
                                               (fun _ : A => False) True e) I (Some a) H0 in
                     False_ind (nil = (a :: r)) H2) H)
             (fun H : nil = (a :: r) =>
                conj
                  (let H0 : False :=
                       eq_ind nil
                              (fun e : list A =>
                                 list_rect (fun _ : list A => Prop) True
                                           (fun (_ : A) (_ : list A) (_ : Prop) => False) e) I
                              (a :: r) H in
                   False_ind (None = Some a) H0)
                  (let H0 : False :=
                       eq_ind nil
                              (fun e : list A =>
                                 list_rect (fun _ : list A => Prop) True
                                           (fun (_ : A) (_ : list A) (_ : Prop) => False) e) I
                              (a :: r) H in
                   False_ind (nil = r) H0)))
        (fun (x : A) (xs : list A)
             (_ : forall (a : A) (r : list A),
                 List.hd_error xs = Some a /\ List.tl xs = r <-> xs = (a :: r))
             (a : A) (r : list A) =>
           conj
             (fun H : Some x = Some a /\ xs = r =>
                and_ind
                  (fun (H1 : Some x = Some a) (H2 : xs = r) =>
                     let H0 : Some a = Some a -> (x :: xs) = (a :: r) :=
                         eq_ind (Some x)
                                (fun y : option A =>
                                   y = Some a -> (x :: xs) = (a :: r))
                                (fun H0 : Some x = Some a =>
                                   (fun H3 : Some x = Some a =>
                                      let H4 : x = a :=
                                          f_equal
                                            (fun e : option A =>
                                               option_rect (fun _ : option A => A)
                                                           (fun a0 : A => a0) x e) H3 in
                                      (fun H5 : x = a =>
                                         let H6 : x = a := H5 in
                                         eq_ind_r (fun a0 : A => (a0 :: xs) = (a :: r))
                                                  (eq_ind_r
                                                     (fun xs0 : list A => (a :: xs0) = (a :: r))
                                                     eq_refl H2) H6) H4) H0) (Some a) H1 in
                     H0 eq_refl) H)
             (fun H : (x :: xs) = (a :: r) =>
                let H0 : (a :: r) = (a :: r) -> Some x = Some a /\ xs = r :=
                    eq_ind (x :: xs)
                           (fun y : list A => y = (a :: r) -> Some x = Some a /\ xs = r)
                           (fun H0 : (x :: xs) = (a :: r) =>
                              (fun H1 : (x :: xs) = (a :: r) =>
                                 let H2 : xs = r :=
                                     f_equal
                                       (fun e : list A =>
                                          list_rect (fun _ : list A => list A) xs
                                                    (fun (_ : A) (l0 _ : list A) => l0) e) H1 in
                                 (let H3 : x = a :=
                                      f_equal
                                        (fun e : list A =>
                                           list_rect (fun _ : list A => A) x
                                                     (fun (a0 : A) (_ : list A) (_ : A) => a0) e) H1 in
                                  (fun H4 : x = a =>
                                     let H5 : x = a := H4 in
                                     eq_ind_r (fun a0 : A => xs = r -> Some a0 = Some a /\ xs = r)
                                              (fun H6 : xs = r =>
                                                 let H7 : xs = r := H6 in
                                                 eq_ind_r (fun l0 : list A => Some a = Some a /\ l0 = r)
                                                          (eq_ind_r
                                                             (fun x0 : A =>
                                                                (x0 :: xs) = (a :: r) ->
                                                                Some a = Some a /\ r = r)
                                                             (fun H8 : (a :: xs) = (a :: r) =>
                                                                eq_ind_r
                                                                  (fun xs0 : list A =>
                                                                     (a :: xs0) = (a :: r) ->
                                                                     Some a = Some a /\ r = r)
                                                                  (fun _ : (a :: r) = (a :: r) =>
                                                                     conj eq_refl eq_refl) H6 H8) H4 H) H7) H5) H3) H2)
                                H0) (a :: r) H in
                H0 eq_refl)) l.
  Lemma test_hd_error_tl_repr : actual_hd_error_tl_repr = expected_hd_error_tl_repr. Proof. reflexivity. Qed.

  Preprocess List.length_zero_iff_nil as actual_length_zero_iff_nil.
  Definition expected_length_zero_iff_nil (A : Type) (l : list A) : (length l = 0 -> l = nil) /\ (l = nil -> length l = 0) :=
    conj
      (list_ind (fun l0 : list A => length l0 = 0 -> l0 = nil)
                (fun _ : length nil = 0 => eq_refl)
                (fun (a : A) (l0 : list A) (_ : length l0 = 0 -> l0 = nil)
                     (H : length (a :: l0) = 0) =>
                   let H0 : 0 = 0 -> (a :: l0) = nil :=
                       eq_ind (length (a :: l0))
                              (fun y : nat => y = 0 -> (a :: l0) = nil)
                              (fun H0 : length (a :: l0) = 0 =>
                                 (fun H1 : length (a :: l0) = 0 =>
                                    let H2 : False :=
                                        eq_ind (length (a :: l0))
                                               (fun e : nat =>
                                                  nat_rect (fun _ : nat => Prop) False
                                                           (fun (_ : nat) (_ : Prop) => True) e) I 0 H1 in
                                    False_ind ((a :: l0) = nil) H2) H0) 0 H in
                   H0 eq_refl) l)
      (fun H : l = nil => eq_ind_r (fun l0 : list A => length l0 = 0) (@eq_refl nat (length nil)) H).
  Lemma test_length_zero_iff_nil : actual_length_zero_iff_nil = expected_length_zero_iff_nil. Proof. reflexivity. Qed.

  Preprocess List.hd_error_nil as actual_hd_error_nil.
  Definition expected_hd_error_nil (A : Type) : List.hd_error (@nil A) = None :=
    eq_refl.
  Lemma test_hd_error_nil : actual_hd_error_nil = expected_hd_error_nil. Proof. reflexivity. Qed.

  Preprocess List.hd_error_cons as actual_hd_error_cons.
  Definition expected_hd_error_cons (A : Type) (l : list A) (x : A) : List.hd_error (x :: l) = Some x :=
    eq_refl.
  Lemma test_hd_error_cons : actual_hd_error_cons = expected_hd_error_cons. Proof. reflexivity. Qed.

  Preprocess List.in_eq as actual_in_eq.
  Definition expected_in_eq (A : Type) (a : A) (l : list A) : List.In a (a :: l) :=
    or_introl eq_refl.
  Lemma test_in_eq : actual_in_eq = expected_in_eq. Proof. reflexivity. Qed.

  Preprocess List.in_cons as actual_in_cons.
  Definition expected_in_cons (A : Type) (a b : A) (l : list A) (H : List.In b l) : List.In b (a :: l) :=
    or_intror H.
  Lemma test_in_cons : actual_in_cons = expected_in_cons. Proof. reflexivity. Qed.

  Preprocess List.not_in_cons as actual_not_in_cons.
  Definition expected_not_in_cons (A : Type) (x a : A) (l : list A) : ~ List.In x (a :: l) <-> x <> a /\ ~ List.In x l :=
    conj
      (fun H : ~ (a = x \/ List.In x l) =>
         let H0 : a = x -> False := fun H0 : a = x => H (or_introl H0) in
         let H1 : List.In x l -> False := fun H1 : List.In x l => H (or_intror H1)
         in
         conj (fun H2 : x = a => H0 (eq_sym H2))
              (fun H2 : List.In x l => let H3 : False := H1 H2 in False_ind False H3))
      (fun (H : x <> a /\ ~ List.In x l) (H0 : a = x \/ List.In x l) =>
         and_ind
           (fun (H1 : x <> a) (H2 : ~ List.In x l) =>
              or_ind (fun H3 : a = x => H1 (eq_sym H3))
                     (fun H3 : List.In x l =>
                        let H4 : False := H2 H3 in False_ind False H4) H0) H).
  Lemma test_not_in_cons : actual_not_in_cons = expected_not_in_cons. Proof. reflexivity. Qed.

  Preprocess List.in_nil as actual_in_nil.
  Definition expected_in_nil (A : Type) (a : A) : ~ List.In a nil :=
    fun (H : List.In a nil) =>
      let H0 : False := False_ind False H in H0.
  Lemma test_in_nil : actual_in_nil = expected_in_nil. Proof. reflexivity. Qed.

  Preprocess List.in_split as actual_in_split.
  Definition expected_in_split (A : Type) (x : A) (l : list A) : List.In x l -> exists l1 l2 : list A, l = (l1 ++ x :: l2) :=
    list_ind
      (fun l0 : list A =>
         List.In x l0 -> exists l1 l2 : list A, l0 = (l1 ++ x :: l2))
      (fun H : False =>
         False_ind (exists l1 l2 : list A, nil = (l1 ++ x :: l2)) H)
      (fun (a : A) (l0 : list A)
           (IHl : List.In x l0 -> exists l1 l2 : list A, l0 = (l1 ++ x :: l2))
           (H : a = x \/ List.In x l0) =>
         or_ind
           (fun H0 : a = x =>
              eq_ind_r
                (fun a0 : A =>
                   exists l1 l2 : list A, (a0 :: l0) = (l1 ++ x :: l2))
                (ex_intro
                   (fun l1 : list A =>
                      exists l2 : list A, (x :: l0) = (l1 ++ x :: l2)) nil
                   (ex_intro
                      (fun l2 : list A => (x :: l0) = (nil ++ x :: l2)) l0
                      eq_refl)) H0)
           (fun H0 : List.In x l0 =>
              let e : exists l1 l2 : list A, l0 = (l1 ++ x :: l2) := IHl H0 in
              ex_ind
                (fun (l1 : list A)
                     (H1 : exists l2 : list A, l0 = (l1 ++ x :: l2)) =>
                   ex_ind
                     (fun (l2 : list A) (H2 : l0 = (l1 ++ x :: l2)) =>
                        ex_intro
                          (fun l3 : list A =>
                             exists l4 : list A, (a :: l0) = (l3 ++ x :: l4))
                          (a :: l1)
                          (ex_intro
                             (fun l3 : list A =>
                                (a :: l0) = ((a :: l1) ++ x :: l3)) l2
                             (f_equal (cons a) H2))) H1) e) H) l.
  Lemma test_in_split : actual_in_split = expected_in_split. Proof. reflexivity. Qed.

  Preprocess List.in_dec as actual_in_dec.
  Definition expected_in_dec (A : Type) (H : forall x y : A, {x = y} + {x <> y}) (a : A) (l : list A) : {List.In a l} + {~ List.In a l} :=
    list_rec (fun l0 : list A => {List.In a l0} + {~ List.In a l0})
             (right (List.in_nil (a:=a)))
             (fun (a0 : A) (l0 : list A) (IHl : {List.In a l0} + {~ List.In a l0}) =>
                let s := H a0 a in
                sumbool_rec
                  (fun _ : {a0 = a} + {a0 <> a} =>
                     {List.In a (a0 :: l0)} + {~ List.In a (a0 :: l0)})
                  (fun e : a0 = a => left (or_introl e))
                  (fun n : a0 <> a =>
                     sumbool_rec
                       (fun _ : {List.In a l0} + {~ List.In a l0} =>
                          {a0 = a \/ List.In a l0} + {~ (a0 = a \/ List.In a l0)})
                       (fun i : List.In a l0 => left (or_intror i))
                       (fun n0 : ~ List.In a l0 =>
                          right
                            (fun H0 : a0 = a \/ List.In a l0 =>
                               or_ind (fun Hc1 : a0 = a => n Hc1)
                                      (fun Hc2 : List.In a l0 => n0 Hc2) H0)) IHl) s) l.
  Lemma test_in_dec : actual_in_dec = expected_in_dec. Proof. reflexivity. Qed.

  Preprocess List.app_cons_not_nil as actual_app_cons_not_nil.
  Definition expected_app_cons_not_nil (A : Type) (x : list A) : forall (y : list A) (a : A), nil <> (x ++ a :: y) :=
    list_ind
      (fun l : list A =>
         forall (y : list A) (a : A), nil = (l ++ a :: y) -> False)
      (fun (y : list A) (a : A) (H : nil = (a :: y)) =>
         let H0 : False :=
             eq_ind nil
                    (fun e : list A =>
                       list_rect (fun _ : list A => Prop) True
                                 (fun (_ : A) (_ : list A) (_ : Prop) => False) e) I
                    (a :: y) H in
         False_ind False H0)
      (fun (a : A) (l : list A)
           (_ : forall (y : list A) (a0 : A), nil = (l ++ a0 :: y) -> False)
           (y : list A) (a0 : A) (H : nil = (a :: l ++ a0 :: y)) =>
         let H0 : False :=
             eq_ind nil
                    (fun e : list A =>
                       list_rect (fun _ : list A => Prop) True
                                 (fun (_ : A) (_ : list A) (_ : Prop) => False) e) I
                    (a :: l ++ a0 :: y) H in
         False_ind False H0) x.
  Lemma test_app_cons_not_nil : actual_app_cons_not_nil = expected_app_cons_not_nil. Proof. reflexivity. Qed.

  Preprocess List.app_nil_l as actual_app_nil_l.
  Definition expected_app_nil_l (A : Type) (l : list A) : nil ++ l = l :=
    eq_refl.
  Lemma test_app_nil_l : actual_app_nil_l = expected_app_nil_l. Proof. reflexivity. Qed.

  Preprocess List.app_nil_r as actual_app_nil_r.
  Definition expected_app_nil_r (A : Type) (l : list A) : (l ++ nil) = l :=
    list_ind (fun l0 : list A => (l0 ++ nil) = l0)
             (let H : A = A := eq_refl in (fun _ : A = A => eq_refl) H)
             (fun (a : A) (l0 : list A) (IHl : (l0 ++ nil) = l0) =>
                let H : (l0 ++ nil) = l0 := IHl in
                (let H0 : a = a := eq_refl in
                 (let H1 : A = A := eq_refl in
                  (fun (_ : A = A) (_ : a = a) (H4 : (l0 ++ nil) = l0) =>
                     eq_trans
                       (f_equal (fun f : list A -> list A => f (l0 ++ nil)) eq_refl)
                       (f_equal (cons a) H4)) H1) H0) H) l.
  Lemma test_app_nil_r : actual_app_nil_r = expected_app_nil_r. Proof. reflexivity. Qed.

  Preprocess List.app_nil_end as actual_app_nil_end.
  Definition expected_app_nil_end (A : Type) (l : list A) : l = l ++ nil :=
    eq_sym (List.app_nil_r l).
  Lemma test_app_nil_end : actual_app_nil_end = expected_app_nil_end. Proof. reflexivity. Qed.

  Preprocess List.app_assoc as actual_app_assoc.
  Definition expected_app_assoc (A : Type) (l m n : list A) : l ++ m ++ n = (l ++ m) ++ n :=
    list_ind (fun l0 : list A => (l0 ++ m ++ n) = ((l0 ++ m) ++ n))
             (let H : n = n := eq_refl in
              (let H0 : m = m := eq_refl in
               (let H1 : A = A := eq_refl in
                (fun (_ : A = A) (_ : m = m) (_ : n = n) => eq_refl) H1) H0) H)
             (fun (a : A) (l0 : list A)
                  (IHl : (l0 ++ m ++ n) = ((l0 ++ m) ++ n)) =>
                let H : (l0 ++ m ++ n) = ((l0 ++ m) ++ n) := IHl in
                (let H0 : a = a := eq_refl in
                 (let H1 : A = A := eq_refl in
                  (fun (_ : A = A) (_ : a = a)
                       (H4 : (l0 ++ m ++ n) = ((l0 ++ m) ++ n)) =>
                     eq_trans
                       (f_equal (fun f : list A -> list A => f (l0 ++ m ++ n)) eq_refl)
                       (f_equal (cons a) H4)) H1) H0) H) l.
  Lemma test_app_assoc : actual_app_assoc = expected_app_assoc. Proof. reflexivity. Qed.

  Preprocess List.app_assoc_reverse as actual_app_assoc_reverse.
  Definition expected_app_assoc_reverse (A : Type) (l m n : list A) : ((l ++ m) ++ n) = (l ++ m ++ n) :=
    eq_sym (List.app_assoc l m n).
  Lemma test_app_assoc_reverse : actual_app_assoc_reverse = expected_app_assoc_reverse. Proof. reflexivity. Qed.

  Preprocess List.app_comm_cons as actual_app_comm_cons.
  Definition expected_app_comm_cons (A : Type) (x y : list A) (a : A) : a :: x ++ y = (a :: x) ++ y :=
    eq_refl.
  Lemma test_app_comm_cons : actual_app_comm_cons = expected_app_comm_cons. Proof. reflexivity. Qed.

  Preprocess List.app_eq_nil as actual_app_eq_nil.
  Definition expected_app_eq_nil (A : Type) (l : list A) : forall (l' : list A), l ++ l' = nil -> l = nil /\ l' = nil :=
    list_ind
      (fun l0 : list A =>
         forall l' : list A, (l0 ++ l') = nil -> l0 = nil /\ l' = nil)
      (fun l' : list A =>
         list_ind
           (fun l0 : list A => (nil ++ l0) = nil -> nil = nil /\ l0 = nil)
           (fun H : nil = nil => conj H H)
           (fun (y : A) (l'0 : list A)
                (_ : (nil ++ l'0) = nil -> nil = nil /\ l'0 = nil)
                (H : (y :: l'0) = nil) => conj eq_refl H) l')
      (fun (x : A) (l0 : list A)
           (_ : forall l' : list A, (l0 ++ l') = nil -> l0 = nil /\ l' = nil)
           (l' : list A) =>
         list_ind
           (fun l1 : list A =>
              ((x :: l0) ++ l1) = nil -> (x :: l0) = nil /\ l1 = nil)
           (fun H : (x :: l0 ++ nil) = nil =>
              let H0 : False :=
                  eq_ind (x :: l0 ++ nil)
                         (fun e : list A =>
                            list_rect (fun _ : list A => Prop) False
                                      (fun (_ : A) (_ : list A) (_ : Prop) => True) e) I nil H in
              False_ind ((x :: l0) = nil /\ nil = nil) H0)
           (fun (y : A) (l'0 : list A)
                (_ : ((x :: l0) ++ l'0) = nil ->
                     (x :: l0) = nil /\ l'0 = nil)
                (H : (x :: l0 ++ y :: l'0) = nil) =>
              let H0 : False :=
                  eq_ind (x :: l0 ++ y :: l'0)
                         (fun e : list A =>
                            list_rect (fun _ : list A => Prop) False
                                      (fun (_ : A) (_ : list A) (_ : Prop) => True) e) I nil H in
              False_ind ((x :: l0) = nil /\ (y :: l'0) = nil) H0) l') l.
  Lemma test_app_eq_nil : actual_app_eq_nil = expected_app_eq_nil. Proof. reflexivity. Qed.

  Preprocess List.app_eq_unit as actual_app_eq_unit.
  Definition expected_app_eq_unit (A : Type) (x : list A) :
    forall (y : list A) (a : A),
      x ++ y = a :: nil -> x = nil /\ y = a :: nil \/ x = a :: nil /\ y = nil
    :=
      list_ind
        (fun l : list A =>
           forall (y : list A) (a : A),
             (l ++ y) = (a :: nil) ->
             l = nil /\ y = (a :: nil) \/ l = (a :: nil) /\ y = nil)
        (fun y : list A =>
           list_ind
             (fun l : list A =>
                forall a : A,
                  (nil ++ l) = (a :: nil) ->
                  nil = nil /\ l = (a :: nil) \/ nil = (a :: nil) /\ l = nil)
             (fun (a : A) (H : nil = (a :: nil)) =>
                let H0 : False :=
                    eq_ind nil
                           (fun e : list A =>
                              list_rect (fun _ : list A => Prop) True
                                        (fun (_ : A) (_ : list A) (_ : Prop) => False) e) I
                           (a :: nil) H in
                False_ind
                  (nil = nil /\ nil = (a :: nil) \/
                                nil = (a :: nil) /\ nil = nil) H0)
             (fun (a : A) (l : list A)
                  (_ : forall a0 : A,
                      (nil ++ l) = (a0 :: nil) ->
                      nil = nil /\ l = (a0 :: nil) \/
                                   nil = (a0 :: nil) /\ l = nil) (a0 : A)
                  (H : (a :: l) = (a0 :: nil)) =>
                or_introl (conj eq_refl H)) y)
        (fun (a : A) (l : list A)
             (_ : forall (y : list A) (a0 : A),
                 (l ++ y) = (a0 :: nil) ->
                 l = nil /\ y = (a0 :: nil) \/ l = (a0 :: nil) /\ y = nil)
             (y : list A) =>
           list_ind
             (fun l0 : list A =>
                forall a0 : A,
                  ((a :: l) ++ l0) = (a0 :: nil) ->
                  (a :: l) = nil /\ l0 = (a0 :: nil) \/
                                    (a :: l) = (a0 :: nil) /\ l0 = nil)
             (fun (a0 : A) (H : (a :: l ++ nil) = (a0 :: nil)) =>
                or_intror
                  (conj
                     ((fun E : (l ++ nil) = l =>
                         eq_ind_r
                           (fun l0 : list A =>
                              (a :: l0) = (a0 :: nil) ->
                              (a :: l) = (a0 :: nil))
                           (fun H0 : (a :: l) = (a0 :: nil) => H0) E)
                        (List.app_nil_r l) H) eq_refl))
             (fun (a0 : A) (l0 : list A)
                  (_ : forall a1 : A,
                      ((a :: l) ++ l0) = (a1 :: nil) ->
                      (a :: l) = nil /\ l0 = (a1 :: nil) \/
                                        (a :: l) = (a1 :: nil) /\ l0 = nil)
                  (a1 : A) (H : (a :: l ++ a0 :: l0) = (a1 :: nil)) =>
                let H0 : (l ++ a0 :: l0) = nil :=
                    f_equal
                      (fun e : list A =>
                         list_rect (fun _ : list A => list A)
                                   ((fun l1 : list A =>
                                       list_rect (fun _ : list A => list A -> list A)
                                                 (fun m : list A => m)
                                                 (fun (a2 : A) (_ : list A) (app : list A -> list A)
                                                      (m : list A) => (a2 :: app m)) l1) l
                                                                                         (a0 :: l0)) (fun (_ : A) (l1 _ : list A) => l1) e) H in
                (let H1 : a = a1 :=
                     f_equal
                       (fun e : list A =>
                          list_rect (fun _ : list A => A) a
                                    (fun (a2 : A) (_ : list A) (_ : A) => a2) e) H in
                 (fun (_ : a = a1) (H3 : (l ++ a0 :: l0) = nil) =>
                    let H4 : nil = (l ++ a0 :: l0) := eq_sym H3 in
                    let H5 : False := List.app_cons_not_nil l l0 a0 H4 in
                    False_ind
                      ((a :: l) = nil /\ (a0 :: l0) = (a1 :: nil) \/
                                         (a :: l) = (a1 :: nil) /\ (a0 :: l0) = nil) H5) H1)
                  H0) y) x.
  Lemma test_app_eq_unit : actual_app_eq_unit = expected_app_eq_unit. Proof. reflexivity. Qed.

  Preprocess List.app_length as actual_app_length.
  Definition expected_app_length (A : Type) (l : list A) : forall (l' : list A), length (l ++ l') = length l + length l' :=
    list_ind
      (fun l0 : list A =>
         forall l' : list A, length (l0 ++ l') = length l0 + length l')
      (fun l' : list A => eq_refl)
      (fun (a : A) (l0 : list A)
           (IHl : forall l' : list A, length (l0 ++ l') = length l0 + length l')
           (l' : list A) =>
         f_equal_nat nat S (length (l0 ++ l')) (length l0 + length l') (IHl l')) l.
  Lemma test_app_length : actual_app_length = expected_app_length. Proof. reflexivity. Qed.

  Preprocess List.in_app_or as actual_in_app_or.
  Definition expected_in_app_or (A : Type) (l m : list A) (a : A) : List.In a (l ++ m) -> List.In a l \/ List.In a m :=
    list_ind
      (fun l0 : list A => List.In a (l0 ++ m) -> List.In a l0 \/ List.In a m)
      (fun H : List.In a m => or_intror H)
      (fun (a0 : A) (y : list A)
           (H : List.In a (y ++ m) -> List.In a y \/ List.In a m)
           (H0 : a0 = a \/ List.In a (y ++ m)) =>
         or_ind (fun H1 : a0 = a => or_introl (or_introl H1))
                (fun H1 : List.In a (y ++ m) =>
                   or_ind (fun H2 : List.In a y => or_introl (or_intror H2))
                          (fun H2 : List.In a m => or_intror H2) (H H1)) H0) l.
  Lemma test_in_app_or : actual_in_app_or = expected_in_app_or. Proof. reflexivity. Qed.

  Preprocess List.in_or_app as actual_in_or_app.
  Definition expected_in_or_app (A : Type) (l m : list A) (a : A) : List.In a l \/ List.In a m -> List.In a (l ++ m) :=
    list_ind
      (fun l0 : list A => List.In a l0 \/ List.In a m -> List.In a (l0 ++ m))
      (fun H : False \/ List.In a m =>
         or_ind (fun H0 : False => False_ind (List.In a m) H0)
                (fun H0 : List.In a m => H0) H)
      (fun (H : A) (y : list A)
           (H0 : List.In a y \/ List.In a m -> List.In a (y ++ m))
           (H1 : (H = a \/ List.In a y) \/ List.In a m) =>
         or_ind
           (fun H2 : H = a \/ List.In a y =>
              or_ind (fun H3 : H = a => or_introl H3)
                     (fun H3 : List.In a y => or_intror (H0 (or_introl H3))) H2)
           (fun H2 : List.In a m => or_intror (H0 (or_intror H2))) H1) l.
  Lemma test_in_or_app : actual_in_or_app = expected_in_or_app. Proof. reflexivity. Qed.

  Preprocess List.in_app_iff as actual_in_app_iff.
  Definition expected_in_app_iff (A : Type) (l l' : list A) (a : A) : List.In a (l ++ l') <-> List.In a l \/ List.In a l' :=
    conj (fun H : List.In a (l ++ l') => List.in_app_or l l' a H)
         (fun H : List.In a l \/ List.In a l' => List.in_or_app l l' a H).
  Lemma test_in_app_iff : actual_in_app_iff = expected_in_app_iff. Proof. reflexivity. Qed.

  Preprocess List.app_inv_head as actual_app_inv_head.
  Definition expected_app_inv_head (A : Type) (l : list A) : forall (l1 l2 : list A), (l ++ l1) = (l ++ l2) -> l1 = l2 :=
    list_ind
      (fun l0 : list A =>
         forall l1 l2 : list A, (l0 ++ l1) = (l0 ++ l2) -> l1 = l2)
      (fun (l1 l2 : list A) (H : l1 = l2) => H)
      (fun (a : A) (l0 : list A)
           (IHl : forall l1 l2 : list A,
               (l0 ++ l1) = (l0 ++ l2) -> l1 = l2)
           (l1 l2 : list A) (H : (a :: l0 ++ l1) = (a :: l0 ++ l2)) =>
         let H0 : (l0 ++ l1) = (l0 ++ l2) :=
             f_equal
               (fun e : list A =>
                  list_rect (fun _ : list A => list A)
                            ((fun l3 : list A =>
                                list_rect (fun _ : list A => list A -> list A)
                                          (fun m : list A => m)
                                          (fun (a0 : A) (_ : list A) (app : list A -> list A)
                                               (m : list A) => (a0 :: app m)) l3) l0 l1)
                            (fun (_ : A) (l3 _ : list A) => l3) e) H in
         (fun H1 : (l0 ++ l1) = (l0 ++ l2) => IHl l1 l2 H1) H0) l.
  Lemma test_app_inv_head : actual_app_inv_head = expected_app_inv_head. Proof. reflexivity. Qed.

  Preprocess List.app_inv_tail as actual_app_inv_tail.
  Definition expected_app_inv_tail (A : Type) (l l1 l2 : list A) : (l1 ++ l) = (l2 ++ l) -> l1 = l2 :=
    (fun l3 : list A =>
       list_ind
         (fun l4 : list A =>
            forall l5 l0 : list A, (l4 ++ l0) = (l5 ++ l0) -> l4 = l5)
         (fun l4 : list A =>
            list_ind
              (fun l0 : list A =>
                 forall l5 : list A, (nil ++ l5) = (l0 ++ l5) -> nil = l0)
              (fun (l0 : list A) (_ : l0 = l0) => eq_refl)
              (fun (x2 : A) (l5 : list A)
                   (_ : forall l0 : list A,
                       (nil ++ l0) = (l5 ++ l0) -> nil = l5)
                   (l0 : list A) (H : l0 = (x2 :: l5 ++ l0)) =>
                 False_ind (nil = (x2 :: l5))
                           (eq_ind_r (fun n : nat => ~ S n <= length l0)
                                     (Gt.gt_not_le (S (length l5 + length l0))
                                                   (length l0)
                                                   (Le.le_n_S (length l0) (length l5 + length l0)
                                                              (Plus.le_plus_r (length l5) (length l0))))
                                     (List.app_length l5 l0)
                                     (eq_ind l0 (fun l6 : list A => length l6 <= length l0)
                                             (le_n (length l0)) (x2 :: l5 ++ l0) H))) l4)
         (fun (x1 : A) (l4 : list A)
              (IHl1 : forall l5 l0 : list A,
                  (l4 ++ l0) = (l5 ++ l0) -> l4 = l5)
              (l5 : list A) =>
            list_ind
              (fun l0 : list A =>
                 forall l6 : list A,
                   ((x1 :: l4) ++ l6) = (l0 ++ l6) -> (x1 :: l4) = l0)
              (fun (l0 : list A) (H : (x1 :: l4 ++ l0) = l0) =>
                 False_ind ((x1 :: l4) = nil)
                           (eq_ind_r (fun n : nat => ~ S n <= length l0)
                                     (Gt.gt_not_le (S (length l4 + length l0))
                                                   (length l0)
                                                   (Le.le_n_S (length l0) (length l4 + length l0)
                                                              (Plus.le_plus_r (length l4) (length l0))))
                                     (List.app_length l4 l0)
                                     (eq_ind_r (fun l6 : list A => length l6 <= length l0)
                                               (le_n (length l0)) H)))
              (fun (x2 : A) (l6 : list A)
                   (_ : forall l0 : list A,
                       ((x1 :: l4) ++ l0) = (l6 ++ l0) ->
                       (x1 :: l4) = l6) (l0 : list A)
                   (H : (x1 :: l4 ++ l0) = (x2 :: l6 ++ l0)) =>
                 let H0 : (l4 ++ l0) = (l6 ++ l0) :=
                     f_equal
                       (fun e : list A =>
                          list_rect (fun _ : list A => list A)
                                    ((fun l7 : list A =>
                                        list_rect (fun _ : list A => list A -> list A)
                                                  (fun m : list A => m)
                                                  (fun (l8 : A) (_ : list A) (app : list A -> list A)
                                                       (m : list A) => (l8 :: app m)) l7) l4 l0)
                                    (fun (_ : A) (l7 _ : list A) => l7) e) H in
                 (let H1 : x1 = x2 :=
                      f_equal
                        (fun e : list A =>
                           list_rect (fun _ : list A => A) x1
                                     (fun (a : A) (_ : list A) (_ : A) => a) e) H in
                  (fun (H2 : x1 = x2) (H3 : (l4 ++ l0) = (l6 ++ l0)) =>
                     let H4 : l4 = l6 := IHl1 l6 l0 H3 in
                     (let H5 : x1 = x2 := H2 in
                      (let H6 : A = A := eq_refl in
                       (fun (_ : A = A) (H8 : x1 = x2) (H9 : l4 = l6) =>
                          eq_trans
                            (f_equal (fun f : list A -> list A => f l4)
                                     (eq_trans
                                        (f_equal (fun f : A -> list A -> list A => f x1) eq_refl)
                                        (f_equal cons H8))) (f_equal (cons x2) H9)) H6) H5) H4)
                    H1) H0) l5) l3) l1 l2 l.
  Lemma test_app_inv_tail : actual_app_inv_tail = expected_app_inv_tail. Proof. reflexivity. Qed.

  Preprocess List.nth as actual_nth.
  Definition expected_nth (A : Type) (n : nat) (l : list A) : A -> A :=
    list_rect (fun _ : list A => nat -> A -> A)
              (fun (n0 : nat) (default : A) =>
                 nat_rect (fun _ : nat => A) default (fun (_ : nat) (_ : A) => default) n0)
              (fun (a : A) (_ : list A) (nth : nat -> A -> A) (n0 : nat) (default : A) =>
                 nat_rect (fun _ : nat => A) a (fun (m : nat) (_ : A) => nth m default) n0)
              l n.
  Lemma test_actual_nth : actual_nth = expected_nth. Proof. reflexivity. Qed.

  Preprocess List.nth_ok as actual_nth_ok.
  Definition expected_nth_ok (A : Type) (n : nat) (l : list A) : A -> bool :=
    list_rect (fun _ : list A => nat -> A -> bool)
              (fun (n0 : nat) (_ : A) =>
                 nat_rec (fun _ : nat => bool) false (fun (_ : nat) (_ : bool) => false) n0)
              (fun (_ : A) (_ : list A) (nth_ok : nat -> A -> bool)
                   (n0 : nat) (default : A) =>
                 nat_rec (fun _ : nat => bool) true
                         (fun (m : nat) (_ : bool) => nth_ok m default) n0) l n.
  Lemma test_nth_ok : actual_nth_ok = expected_nth_ok. Proof. reflexivity. Qed.

  Preprocess List.nth_in_or_default as actual_nth_in_or_default.
  Definition expected_nth_in_or_default (A : Type) (n : nat) (l : list A) (d : A) : {List.In (List.nth n l d) l} + {List.nth n l d = d} :=
    list_rec
      (fun l0 : list A =>
         forall n0 : nat, {List.In (List.nth n0 l0 d) l0} + {List.nth n0 l0 d = d})
      (fun n0 : nat =>
         right
           (nat_ind (fun n1 : nat => List.nth n1 nil d = d) eq_refl
                    (fun (n1 : nat) (_ : List.nth n1 nil d = d) => eq_refl) n0))
      (fun (a : A) (l0 : list A)
           (IHl : forall n0 : nat,
               {List.In (List.nth n0 l0 d) l0} + {List.nth n0 l0 d = d})
           (n0 : nat) =>
         nat_rec
           (fun n1 : nat =>
              {List.In (List.nth n1 (a :: l0) d) (a :: l0)} +
              {List.nth n1 (a :: l0) d = d}) (left (or_introl eq_refl))
           (fun (n1 : nat)
                (_ : {List.In (List.nth n1 (a :: l0) d) (a :: l0)} +
                     {List.nth n1 (a :: l0) d = d}) =>
              let s := IHl n1 in
              sumbool_rec
                (fun _ : {List.In (List.nth n1 l0 d) l0} + {List.nth n1 l0 d = d} =>
                   {a = List.nth n1 l0 d \/ List.In (List.nth n1 l0 d) l0} +
                   {List.nth n1 l0 d = d})
                (fun i : List.In (List.nth n1 l0 d) l0 => left (or_intror i))
                (fun e : List.nth n1 l0 d = d => right e) s) n0) l n.
  Lemma test_nth_in_or_default : actual_nth_in_or_default = expected_nth_in_or_default. Proof. reflexivity. Qed.

  Preprocess List.nth_S_cons as actual_nth_S_cons.
  Definition expected_nth_S_cons (A : Type) (n : nat) (l : list A) (d a : A) (H : List.In (List.nth n l d) l) :
    List.In (List.nth (S n) (a :: l) d) (a :: l)
    :=
      or_intror H.
  Lemma test_nth_S_cons : actual_nth_S_cons = expected_nth_S_cons. Proof. reflexivity. Qed.

  Preprocess List.nth_error as actual_nth_error.
  Definition expected_nth_error (A : Type) (l : list A) (n : nat) : option A :=
    nat_rect (fun _ : nat => list A -> option A)
             (fun l0 : list A =>
                list_rect (fun _ : list A => option A) None
                          (fun (x : A) (_ : list A) (_ : option A) => Some x) l0)
             (fun (_ : nat) (nth_error : list A -> option A) (l0 : list A) =>
                list_rect (fun _ : list A => option A) None
                          (fun (_ : A) (l1 : list A) (_ : option A) => nth_error l1) l0) n l.
  Lemma test_nth_error : actual_nth_error = expected_nth_error. Proof. reflexivity. Qed.

  Preprocess List.nth_default as actual_nth_default.
  Definition expected_nth_default (A : Type) (default : A) (l : list A) (n : nat) : A :=
    option_rect (fun _ : option A => A) (fun x : A => x) default (List.nth_error l n).
  Lemma test_nth_default : actual_nth_default = expected_nth_default. Proof. reflexivity. Qed.

  Preprocess List.nth_default_eq as actual_nth_default_eq.
  Definition expected_nth_default_eq (A : Type) (n : nat) :
    forall (l : list A) (d : A), List.nth_default d l n = List.nth n l d
    :=
      nat_ind
        (fun n0 : nat =>
           forall (l : list A) (d : A),
             option_rect (fun _ : option A => A) (fun x : A => x) d
                         (List.nth_error l n0) = List.nth n0 l d)
        (fun l : list A =>
           list_ind
             (fun l0 : list A =>
                forall d : A,
                  option_rect (fun _ : option A => A) (fun x : A => x) d
                              (List.nth_error l0 0) = List.nth 0 l0 d) (fun d : A => eq_refl)
             (fun (a : A) (l0 : list A)
                  (_ : forall d : A,
                      option_rect (fun _ : option A => A) (fun x : A => x) d
                                  (List.nth_error l0 0) = List.nth 0 l0 d)
                  (d : A) => eq_refl) l)
        (fun (n0 : nat)
             (IHn : forall (l : list A) (d : A),
                 option_rect (fun _ : option A => A) (fun x : A => x) d
                             (List.nth_error l n0) = List.nth n0 l d)
             (l : list A) =>
           list_ind
             (fun l0 : list A =>
                forall d : A,
                  option_rect (fun _ : option A => A) (fun x : A => x) d
                              (List.nth_error l0 (S n0)) = List.nth (S n0) l0 d)
             (fun d : A => eq_refl)
             (fun (a : A) (l0 : list A)
                  (_ : forall d : A,
                      option_rect (fun _ : option A => A) (fun x : A => x) d
                                  (List.nth_error l0 (S n0)) = List.nth (S n0) l0 d)
                  (d : A) => IHn l0 d) l) n.
  Lemma test_nth_default_eq : actual_nth_default_eq = expected_nth_default_eq. Proof. reflexivity. Qed.

  Preprocess List.nth_overflow as actual_nth_overflow.
  Definition expected_nth_overflow (A : Type) (l : list A) :
    forall (n : nat) (d : A), length l <= n -> List.nth n l d = d
    :=
      list_ind
        (fun l0 : list A =>
           forall (n : nat) (d : A), length l0 <= n -> List.nth n l0 d = d)
        (fun n : nat =>
           nat_ind
             (fun n0 : nat => forall d : A, length nil <= n0 -> List.nth n0 nil d = d)
             (fun (d : A) (_ : 0 <= 0) => eq_refl)
             (fun (n0 : nat)
                  (_ : forall d : A, length nil <= n0 -> List.nth n0 nil d = d)
                  (d : A) (_ : 0 <= S n0) => eq_refl) n)
        (fun (a : A) (l0 : list A)
             (IHl : forall (n : nat) (d : A), length l0 <= n -> List.nth n l0 d = d)
             (n : nat) =>
           nat_ind
             (fun n0 : nat =>
                forall d : A, length (a :: l0) <= n0 -> List.nth n0 (a :: l0) d = d)
             (fun (d : A) (H : S (length l0) <= 0) =>
                let H0 : 0 = 0 -> a = d :=
                    le_ind (S (length l0)) (fun n0 : nat => n0 = 0 -> a = d)
                           (fun H0 : S (length l0) = 0 =>
                              (fun H1 : S (length l0) = 0 =>
                                 let H2 : False :=
                                     eq_ind (S (length l0))
                                            (fun e : nat =>
                                               nat_rect (fun _ : nat => Prop) False
                                                        (fun (_ : nat) (_ : Prop) => True) e) I 0 H1 in
                                 False_ind (a = d) H2) H0)
                           (fun (m : nat) (H0 : S (length l0) <= m)
                                (_ : m = 0 -> a = d) (H1 : S m = 0) =>
                              (fun H2 : S m = 0 =>
                                 let H3 : False :=
                                     eq_ind (S m)
                                            (fun e : nat =>
                                               nat_rect (fun _ : nat => Prop) False
                                                        (fun (_ : nat) (_ : Prop) => True) e) I 0 H2 in
                                 False_ind (S (length l0) <= m -> a = d) H3) H1 H0) 0 H in
                H0 eq_refl)
             (fun (n0 : nat)
                  (_ : forall d : A,
                      length (a :: l0) <= n0 -> List.nth n0 (a :: l0) d = d)
                  (d : A) (H : S (length l0) <= S n0) =>
                IHl n0 d (Gt.gt_S_le (length l0) n0 H)) n) l.
  Lemma test_nth_overflow : actual_nth_overflow = expected_nth_overflow. Proof. reflexivity. Qed.

  Preprocess List.nth_indep as actual_nth_indep.
  Definition expected_nth_indep (A : Type) (l : list A) :
    forall (n : nat) (d d' : A), n < length l -> List.nth n l d = List.nth n l d'
    :=
      list_ind
        (fun l0 : list A =>
           forall (n : nat) (d d' : A),
             n < length l0 -> List.nth n l0 d = List.nth n l0 d')
        (fun (n : nat) (d d' : A) (H : n < length nil) =>
           let H0 :
                 length nil = length nil -> List.nth n nil d = List.nth n nil d' :=
               le_ind (S n)
                      (fun n0 : nat =>
                         n0 = length nil -> List.nth n nil d = List.nth n nil d')
                      (fun H0 : S n = length nil =>
                         (fun H1 : S n = length nil =>
                            let H2 : False :=
                                eq_ind (S n)
                                       (fun e : nat =>
                                          nat_rect (fun _ : nat => Prop) False
                                                   (fun (_ : nat) (_ : Prop) => True) e) I
                                       (length nil) H1 in
                            False_ind (List.nth n nil d = List.nth n nil d') H2) H0)
                      (fun (m : nat) (H0 : S n <= m)
                           (_ : m = length nil -> List.nth n nil d = List.nth n nil d')
                           (H1 : S m = length nil) =>
                         (fun H2 : S m = length nil =>
                            let H3 : False :=
                                eq_ind (S m)
                                       (fun e : nat =>
                                          nat_rect (fun _ : nat => Prop) False
                                                   (fun (_ : nat) (_ : Prop) => True) e) I
                                       (length nil) H2 in
                            False_ind (S n <= m -> List.nth n nil d = List.nth n nil d') H3) H1
                                                                                             H0) (length nil) H in
           H0 eq_refl)
        (fun (a : A) (l0 : list A)
             (IHl : forall (n : nat) (d d' : A),
                 n < length l0 -> List.nth n l0 d = List.nth n l0 d')
             (n0 : nat) =>
           nat_ind
             (fun n : nat =>
                forall d d' : A,
                  n < length (a :: l0) ->
                  List.nth n (a :: l0) d = List.nth n (a :: l0) d')
             (fun (d d' : A) (_ : 0 < S (length l0)) => eq_refl)
             (fun (n : nat)
                  (_ : forall d d' : A,
                      n < length (a :: l0) ->
                      List.nth n (a :: l0) d = List.nth n (a :: l0) d')
                  (d d' : A) (H : S n < S (length l0)) =>
                IHl n d d' (Gt.gt_le_S n (length l0) (Lt.lt_S_n n (length l0) H))) n0)
        l.
  Lemma test_nth_indep : actual_nth_indep = expected_nth_indep. Proof. reflexivity. Qed.

  Preprocess List.app_nth1 as actual_app_nth1.
  Definition expected_app_nth1 (A : Type) (l : list A) :
    forall (l' : list A) (d : A) (n : nat),
      n < length l -> List.nth n (l ++ l') d = List.nth n l d
    :=
      list_ind
        (fun l0 : list A =>
           forall (l' : list A) (d : A) (n : nat),
             n < length l0 -> List.nth n (l0 ++ l') d = List.nth n l0 d)
        (fun (l' : list A) (d : A) (n : nat) (H : n < length nil) =>
           let H0 :
                 length nil = length nil -> List.nth n (nil ++ l') d = List.nth n nil d :=
               le_ind (S n)
                      (fun n0 : nat =>
                         n0 = length nil -> List.nth n (nil ++ l') d = List.nth n nil d)
                      (fun H0 : S n = length nil =>
                         (fun H1 : S n = length nil =>
                            let H2 : False :=
                                eq_ind (S n)
                                       (fun e : nat =>
                                          nat_rect (fun _ : nat => Prop) False
                                                   (fun (_ : nat) (_ : Prop) => True) e) I
                                       (length nil) H1 in
                            False_ind (List.nth n (nil ++ l') d = List.nth n nil d) H2) H0)
                      (fun (m : nat) (H0 : S n <= m)
                           (_ : m = length nil -> List.nth n (nil ++ l') d = List.nth n nil d)
                           (H1 : S m = length nil) =>
                         (fun H2 : S m = length nil =>
                            let H3 : False :=
                                eq_ind (S m)
                                       (fun e : nat =>
                                          nat_rect (fun _ : nat => Prop) False
                                                   (fun (_ : nat) (_ : Prop) => True) e) I
                                       (length nil) H2 in
                            False_ind (S n <= m -> List.nth n (nil ++ l') d = List.nth n nil d)
                                      H3) H1 H0) (length nil) H in
           H0 eq_refl)
        (fun (a : A) (l0 : list A)
             (IHl : forall (l' : list A) (d : A) (n : nat),
                 n < length l0 -> List.nth n (l0 ++ l') d = List.nth n l0 d)
             (l' : list A) (d : A) (n0 : nat) =>
           nat_ind
             (fun n : nat =>
                n < length (a :: l0) ->
                List.nth n ((a :: l0) ++ l') d = List.nth n (a :: l0) d)
             (fun _ : 0 < S (length l0) => eq_refl)
             (fun (n : nat)
                  (_ : n < length (a :: l0) ->
                       List.nth n ((a :: l0) ++ l') d = List.nth n (a :: l0) d)
                  (H : S n < S (length l0)) =>
                IHl l' d n (Gt.gt_le_S n (length l0) (Lt.lt_S_n n (length l0) H))) n0)
        l.
  Lemma test_app_nth1 : actual_app_nth1 = expected_app_nth1. Proof. reflexivity. Qed.

  Preprocess List.app_nth2 as actual_app_nth2.
  Definition expected_app_nth2 (A : Type) (l : list A) :
    forall (l' : list A) (d : A) (n : nat),
      n >= length l -> List.nth n (l ++ l') d = List.nth (n - length l) l' d
    :=
      list_ind
        (fun l0 : list A =>
           forall (l' : list A) (d : A) (n : nat),
             n >= length l0 -> List.nth n (l0 ++ l') d = List.nth (n - length l0) l' d)
        (fun (l' : list A) (d : A) (n0 : nat) =>
           nat_ind
             (fun n : nat =>
                n >= length nil ->
                List.nth n (nil ++ l') d = List.nth (n - length nil) l' d)
             (fun _ : 0 >= length nil => eq_refl)
             (fun (n : nat)
                  (_ : n >= length nil ->
                       List.nth n (nil ++ l') d = List.nth (n - length nil) l' d)
                  (_ : S n >= length nil) => eq_refl) n0)
        (fun (a : A) (l0 : list A)
             (IHl : forall (l' : list A) (d : A) (n : nat),
                 n >= length l0 ->
                 List.nth n (l0 ++ l') d = List.nth (n - length l0) l' d)
             (l' : list A) (d : A) (n0 : nat) =>
           nat_ind
             (fun n : nat =>
                n >= length (a :: l0) ->
                List.nth n ((a :: l0) ++ l') d = List.nth (n - length (a :: l0)) l' d)
             (fun H : 0 >= length (a :: l0) =>
                let H0 :
                      0 = 0 ->
                      List.nth 0 ((a :: l0) ++ l') d = List.nth (0 - length (a :: l0)) l' d :=
                    le_ind (length (a :: l0))
                           (fun n : nat =>
                              n = 0 ->
                              List.nth 0 ((a :: l0) ++ l') d =
                              List.nth (0 - length (a :: l0)) l' d)
                           (fun H0 : length (a :: l0) = 0 =>
                              (fun H1 : length (a :: l0) = 0 =>
                                 let H2 : False :=
                                     eq_ind (length (a :: l0))
                                            (fun e : nat =>
                                               nat_rect (fun _ : nat => Prop) False
                                                        (fun (_ : nat) (_ : Prop) => True) e) I 0 H1 in
                                 False_ind
                                   (List.nth 0 ((a :: l0) ++ l') d =
                                    List.nth (0 - length (a :: l0)) l' d) H2) H0)
                           (fun (m : nat) (H0 : length (a :: l0) <= m)
                                (_ : m = 0 ->
                                     List.nth 0 ((a :: l0) ++ l') d =
                                     List.nth (0 - length (a :: l0)) l' d)
                                (H1 : S m = 0) =>
                              (fun H2 : S m = 0 =>
                                 let H3 : False :=
                                     eq_ind (S m)
                                            (fun e : nat =>
                                               nat_rect (fun _ : nat => Prop) False
                                                        (fun (_ : nat) (_ : Prop) => True) e) I 0 H2 in
                                 False_ind
                                   (length (a :: l0) <= m ->
                                    List.nth 0 ((a :: l0) ++ l') d =
                                    List.nth (0 - length (a :: l0)) l' d) H3) H1 H0) 0 H in
                H0 eq_refl)
             (fun (n : nat)
                  (_ : n >= length (a :: l0) ->
                       List.nth n ((a :: l0) ++ l') d =
                       List.nth (n - length (a :: l0)) l' d)
                  (H : S n >= length (a :: l0)) =>
                eq_ind_r (fun a0 : A => a0 = List.nth (n - length l0) l' d) eq_refl
                         (IHl l' d n (Gt.gt_S_le (length l0) n H))) n0) l.
  Lemma test_app_nth2 : actual_app_nth2 = expected_app_nth2. Proof. reflexivity. Qed.

  Preprocess List.nth_split as actual_nth_split.
  Definition expected_nth_split (A : Type) (n : nat) (l : list A) (d : A) :
    n < length l -> exists l1 l2 : list A, l = (l1 ++ List.nth n l d :: l2) /\ length l1 = n
    :=
      nat_ind
        (fun n0 : nat =>
           forall l0 : list A,
             n0 < length l0 ->
             exists l1 l2 : list A,
               l0 = (l1 ++ List.nth n0 l0 d :: l2) /\ length l1 = n0)
        (fun l0 : list A =>
           list_ind
             (fun l1 : list A =>
                0 < length l1 ->
                exists l2 l3 : list A,
                  l1 = (l2 ++ List.nth 0 l1 d :: l3) /\ length l2 = 0)
             (fun H : 0 < length nil =>
                let H0 :
                      length nil = length nil ->
                      exists l1 l2 : list A,
                        nil = (l1 ++ List.nth 0 nil d :: l2) /\ length l1 = 0 :=
                    le_ind 1
                           (fun n0 : nat =>
                              n0 = length nil ->
                              exists l1 l2 : list A,
                                nil = (l1 ++ List.nth 0 nil d :: l2) /\ length l1 = 0)
                           (fun H0 : 1 = length nil =>
                              (fun H1 : 1 = length nil =>
                                 let H2 : False :=
                                     eq_ind 1
                                            (fun e : nat =>
                                               nat_rect (fun _ : nat => Prop) False
                                                        (fun (_ : nat) (_ : Prop) => True) e) I
                                            (length nil) H1 in
                                 False_ind
                                   (exists l1 l2 : list A,
                                       nil = (l1 ++ List.nth 0 nil d :: l2) /\ length l1 = 0)
                                   H2) H0)
                           (fun (m : nat) (H0 : 1 <= m)
                                (_ : m = length nil ->
                                     exists l1 l2 : list A,
                                       nil = (l1 ++ List.nth 0 nil d :: l2) /\
                                       length l1 = 0) (H1 : S m = length nil) =>
                              (fun H2 : S m = length nil =>
                                 let H3 : False :=
                                     eq_ind (S m)
                                            (fun e : nat =>
                                               nat_rect (fun _ : nat => Prop) False
                                                        (fun (_ : nat) (_ : Prop) => True) e) I
                                            (length nil) H2 in
                                 False_ind
                                   (1 <= m ->
                                    exists l1 l2 : list A,
                                      nil = (l1 ++ List.nth 0 nil d :: l2) /\ length l1 = 0)
                                   H3) H1 H0) (length nil) H in
                H0 eq_refl)
             (fun (a : A) (l1 : list A)
                  (_ : 0 < length l1 ->
                       exists l2 l3 : list A,
                         l1 = (l2 ++ List.nth 0 l1 d :: l3) /\ length l2 = 0)
                  (_ : 0 < length (a :: l1)) =>
                ex_intro
                  (fun l2 : list A =>
                     exists l3 : list A,
                       (a :: l1) = (l2 ++ List.nth 0 (a :: l1) d :: l3) /\
                       length l2 = 0) nil
                  (ex_intro
                     (fun l2 : list A =>
                        (a :: l1) = (nil ++ List.nth 0 (a :: l1) d :: l2) /\
                        length nil = 0) l1 (conj eq_refl eq_refl))) l0)
        (fun (n0 : nat)
             (IH : forall l0 : list A,
                 n0 < length l0 ->
                 exists l1 l2 : list A,
                   l0 = (l1 ++ List.nth n0 l0 d :: l2) /\ length l1 = n0)
             (l0 : list A) =>
           list_ind
             (fun l1 : list A =>
                S n0 < length l1 ->
                exists l2 l3 : list A,
                  l1 = (l2 ++ List.nth (S n0) l1 d :: l3) /\ length l2 = S n0)
             (fun H : S n0 < length nil =>
                let H0 :
                      length nil = length nil ->
                      exists l1 l2 : list A,
                        nil = (l1 ++ List.nth (S n0) nil d :: l2) /\ length l1 = S n0 :=
                    le_ind (S (S n0))
                           (fun n1 : nat =>
                              n1 = length nil ->
                              exists l1 l2 : list A,
                                nil = (l1 ++ List.nth (S n0) nil d :: l2) /\
                                length l1 = S n0)
                           (fun H0 : S (S n0) = length nil =>
                              (fun H1 : S (S n0) = length nil =>
                                 let H2 : False :=
                                     eq_ind (S (S n0))
                                            (fun e : nat =>
                                               nat_rect (fun _ : nat => Prop) False
                                                        (fun (_ : nat) (_ : Prop) => True) e) I
                                            (length nil) H1 in
                                 False_ind
                                   (exists l1 l2 : list A,
                                       nil = (l1 ++ List.nth (S n0) nil d :: l2) /\
                                       length l1 = S n0) H2) H0)
                           (fun (m : nat) (H0 : S (S n0) <= m)
                                (_ : m = length nil ->
                                     exists l1 l2 : list A,
                                       nil = (l1 ++ List.nth (S n0) nil d :: l2) /\
                                       length l1 = S n0) (H1 : S m = length nil) =>
                              (fun H2 : S m = length nil =>
                                 let H3 : False :=
                                     eq_ind (S m)
                                            (fun e : nat =>
                                               nat_rect (fun _ : nat => Prop) False
                                                        (fun (_ : nat) (_ : Prop) => True) e) I
                                            (length nil) H2 in
                                 False_ind
                                   (S (S n0) <= m ->
                                    exists l1 l2 : list A,
                                      nil = (l1 ++ List.nth (S n0) nil d :: l2) /\
                                      length l1 = S n0) H3) H1 H0) (length nil) H in
                H0 eq_refl)
             (fun (a : A) (l1 : list A)
                  (_ : S n0 < length l1 ->
                       exists l2 l3 : list A,
                         l1 = (l2 ++ List.nth (S n0) l1 d :: l3) /\
                         length l2 = S n0) (H : S n0 < length (a :: l1)) =>
                let e :
                      exists l2 l3 : list A,
                        l1 = (l2 ++ List.nth n0 l1 d :: l3) /\ length l2 = n0 :=
                    IH l1 (Gt.gt_le_S n0 (length l1) (Gt.gt_S_le (S n0) (length l1) H))
                in
                ex_ind
                  (fun (l2 : list A)
                       (H0 : exists l3 : list A,
                           l1 = (l2 ++ List.nth n0 l1 d :: l3) /\ length l2 = n0)
                   =>
                     ex_ind
                       (fun (l3 : list A)
                            (H1 : l1 = (l2 ++ List.nth n0 l1 d :: l3) /\
                                  length l2 = n0) =>
                          and_ind
                            (fun (Hl : l1 = (l2 ++ List.nth n0 l1 d :: l3))
                                 (Hl1 : length l2 = n0) =>
                               ex_intro
                                 (fun l4 : list A =>
                                    exists l5 : list A,
                                      (a :: l1) =
                                      (l4 ++ List.nth (S n0) (a :: l1) d :: l5) /\
                                      length l4 = S n0) (a :: l2)
                                 (ex_intro
                                    (fun l4 : list A =>
                                       (a :: l1) =
                                       ((a :: l2) ++ List.nth (S n0) (a :: l1) d :: l4) /\
                                       length (a :: l2) = S n0) l3
                                    (conj
                                       (let H2 : l1 = (l2 ++ List.nth n0 l1 d :: l3) :=
                                            Hl in
                                        (let H3 : a = a := eq_refl in
                                         (let H4 : A = A := eq_refl in
                                          (fun (_ : A = A) (_ : a = a)
                                               (H7 : l1 = (l2 ++ List.nth n0 l1 d :: l3))
                                           =>
                                             eq_trans
                                               (f_equal (fun f : list A -> list A => f l1)
                                                        eq_refl) (f_equal (cons a) H7)) H4) H3) H2)
                                       (let H2 : length l2 = n0 := Hl1 in
                                        (fun H3 : length l2 = n0 =>
                                           eq_trans
                                             (f_equal (fun f : nat -> nat => f (length l2))
                                                      eq_refl) (f_equal S H3)) H2)))) H1) H0) e) l0)
        n l.
  Lemma test_nth_split : actual_nth_split = expected_nth_split. Proof. reflexivity. Qed.

  Preprocess List.nth_error_In as actual_nth_error_In.
  Definition expected_nth_error_In (A : Type) (l : list A) (n : nat) (x : A) : List.nth_error l n = Some x -> List.In x l :=
    list_ind
      (fun l0 : list A =>
         forall n0 : nat, List.nth_error l0 n0 = Some x -> List.In x l0)
      (fun n0 : nat =>
         nat_ind (fun n1 : nat => List.nth_error nil n1 = Some x -> List.In x nil)
                 (fun H : None = Some x =>
                    let H0 : Some x = Some x -> False :=
                        eq_ind None (fun y : option A => y = Some x -> False)
                               (fun H0 : None = Some x =>
                                  (fun H1 : None = Some x =>
                                     let H2 : False :=
                                         eq_ind None
                                                (fun e : option A =>
                                                   option_rect (fun _ : option A => Prop)
                                                               (fun _ : A => False) True e) I
                                                (Some x) H1 in
                                     False_ind False H2) H0) (Some x) H in
                    H0 eq_refl)
                 (fun (n1 : nat) (_ : List.nth_error nil n1 = Some x -> List.In x nil)
                      (H : None = Some x) =>
                    let H0 : Some x = Some x -> False :=
                        eq_ind None (fun y : option A => y = Some x -> False)
                               (fun H0 : None = Some x =>
                                  (fun H1 : None = Some x =>
                                     let H2 : False :=
                                         eq_ind None
                                                (fun e : option A =>
                                                   option_rect (fun _ : option A => Prop)
                                                               (fun _ : A => False) True e) I
                                                (Some x) H1 in
                                     False_ind False H2) H0) (Some x) H in
                    H0 eq_refl) n0)
      (fun (a : A) (l0 : list A)
           (IH : forall n0 : nat, List.nth_error l0 n0 = Some x -> List.In x l0)
           (n0 : nat) =>
         nat_ind
           (fun n1 : nat =>
              List.nth_error (a :: l0) n1 = Some x -> List.In x (a :: l0))
           (fun H : Some a = Some x =>
              let H0 : a = x :=
                  f_equal
                    (fun e : option A =>
                       option_rect (fun _ : option A => A) (fun a0 : A => a0) a e) H in
              (fun H1 : a = x => or_introl H1) H0)
           (fun (n1 : nat)
                (_ : List.nth_error (a :: l0) n1 = Some x -> List.In x (a :: l0))
                (H : List.nth_error l0 n1 = Some x) => or_intror (IH n1 H)) n0) l n.
  Lemma test_nth_error_In : actual_nth_error_In = expected_nth_error_In. Proof. reflexivity. Qed.

  Preprocess List.nth_error_None as actual_nth_error_None.
  Definition expected_nth_error_None (A : Type) (l : list A) (n : nat) : List.nth_error l n = None <-> length l <= n :=
    list_ind
      (fun l0 : list A =>
         forall n0 : nat, List.nth_error l0 n0 = None <-> length l0 <= n0)
      (fun n0 : nat =>
         nat_ind
           (fun n1 : nat => List.nth_error nil n1 = None <-> length nil <= n1)
           (conj (fun _ : None = None => le_n 0) (fun _ : 0 <= 0 => eq_refl))
           (fun (n1 : nat) (_ : List.nth_error nil n1 = None <-> length nil <= n1)
            =>
              conj (fun _ : None = None => le_S 0 n1 (PeanoNat.Nat.le_0_l n1))
                   (fun _ : 0 <= S n1 => eq_refl)) n0)
      (fun (a : A) (l0 : list A)
           (IHl : forall n0 : nat, List.nth_error l0 n0 = None <-> length l0 <= n0)
           (n0 : nat) =>
         nat_ind
           (fun n1 : nat =>
              List.nth_error (a :: l0) n1 = None <-> length (a :: l0) <= n1)
           (conj
              (fun H : Some a = None =>
                 let H0 : None = None -> S (length l0) <= 0 :=
                     eq_ind (Some a)
                            (fun y : option A => y = None -> S (length l0) <= 0)
                            (fun H0 : Some a = None =>
                               (fun H1 : Some a = None =>
                                  let H2 : False :=
                                      eq_ind (Some a)
                                             (fun e : option A =>
                                                option_rect (fun _ : option A => Prop)
                                                            (fun _ : A => True) False e) I None H1 in
                                  False_ind (S (length l0) <= 0) H2) H0) None H in
                 H0 eq_refl)
              (fun H : S (length l0) <= 0 =>
                 let H0 : 0 = 0 -> Some a = None :=
                     le_ind (S (length l0)) (fun n1 : nat => n1 = 0 -> Some a = None)
                            (fun H0 : S (length l0) = 0 =>
                               (fun H1 : S (length l0) = 0 =>
                                  let H2 : False :=
                                      eq_ind (S (length l0))
                                             (fun e : nat =>
                                                nat_rect (fun _ : nat => Prop) False
                                                         (fun (_ : nat) (_ : Prop) => True) e) I 0 H1 in
                                  False_ind (Some a = None) H2) H0)
                            (fun (m : nat) (H0 : S (length l0) <= m)
                                 (_ : m = 0 -> Some a = None) (H1 : S m = 0) =>
                               (fun H2 : S m = 0 =>
                                  let H3 : False :=
                                      eq_ind (S m)
                                             (fun e : nat =>
                                                nat_rect (fun _ : nat => Prop) False
                                                         (fun (_ : nat) (_ : Prop) => True) e) I 0 H2 in
                                  False_ind (S (length l0) <= m -> Some a = None) H3) H1 H0) 0 H
                 in
                 H0 eq_refl))
           (fun (n1 : nat)
                (_ : List.nth_error (a :: l0) n1 = None <-> length (a :: l0) <= n1)
            =>
              (fun lemma : List.nth_error l0 n1 = None <-> length l0 <= n1 =>
                 Morphisms.trans_co_eq_inv_impl_morphism RelationClasses.iff_Transitive
                                                         (List.nth_error l0 n1 = None) (length l0 <= n1) lemma
                                                         (S (length l0) <= S n1) (S (length l0) <= S n1)
                                                         (Morphisms.eq_proper_proxy (S (length l0) <= S n1)))
                (IHl n1)
                (conj
                   (fun H : length l0 <= n1 =>
                      Gt.gt_le_S (length l0) (S n1) (Le.le_n_S (length l0) n1 H))
                   (fun H : S (length l0) <= S n1 => Gt.gt_S_le (length l0) n1 H)))
           n0) l n.
  Lemma test_nth_error_None : actual_nth_error_None = expected_nth_error_None. Proof. reflexivity. Qed.

  Preprocess List.nth_error_Some as actual_nth_error_Some.
  Definition expected_nth_error_Some (A : Type) (l : list A) (n : nat) : List.nth_error l n <> None <-> n < length l :=
    list_ind
      (fun l0 : list A =>
         forall n0 : nat, List.nth_error l0 n0 <> None <-> n0 < length l0)
      (fun n0 : nat =>
         nat_ind
           (fun n1 : nat => List.nth_error nil n1 <> None <-> n1 < length nil)
           (conj
              (fun H : None <> None =>
                 let n1 : False := H eq_refl in False_ind (0 < 0) n1)
              (fun H : 0 < 0 =>
                 let H0 : 0 = 0 -> None <> None :=
                     le_ind 1 (fun n1 : nat => n1 = 0 -> None <> None)
                            (fun H0 : 1 = 0 =>
                               (fun H1 : 1 = 0 =>
                                  let H2 : False :=
                                      eq_ind 1
                                             (fun e : nat =>
                                                nat_rect (fun _ : nat => Prop) False
                                                         (fun (_ : nat) (_ : Prop) => True) e) I 0 H1 in
                                  False_ind (None <> None) H2) H0)
                            (fun (m : nat) (H0 : 1 <= m) (_ : m = 0 -> None <> None)
                                 (H1 : S m = 0) =>
                               (fun H2 : S m = 0 =>
                                  let H3 : False :=
                                      eq_ind (S m)
                                             (fun e : nat =>
                                                nat_rect (fun _ : nat => Prop) False
                                                         (fun (_ : nat) (_ : Prop) => True) e) I 0 H2 in
                                  False_ind (1 <= m -> None <> None) H3) H1 H0) 0 H in
                 H0 eq_refl))
           (fun (n1 : nat) (_ : List.nth_error nil n1 <> None <-> n1 < length nil)
            =>
              conj
                (fun H : None <> None =>
                   let n2 : False := H eq_refl in False_ind (S n1 < 0) n2)
                (fun H : S n1 < 0 =>
                   let H0 : 0 = 0 -> None <> None :=
                       le_ind (S (S n1)) (fun n2 : nat => n2 = 0 -> None <> None)
                              (fun H0 : S (S n1) = 0 =>
                                 (fun H1 : S (S n1) = 0 =>
                                    let H2 : False :=
                                        eq_ind (S (S n1))
                                               (fun e : nat =>
                                                  nat_rect (fun _ : nat => Prop) False
                                                           (fun (_ : nat) (_ : Prop) => True) e) I 0 H1 in
                                    False_ind (None <> None) H2) H0)
                              (fun (m : nat) (H0 : S (S n1) <= m) (_ : m = 0 -> None <> None)
                                   (H1 : S m = 0) =>
                                 (fun H2 : S m = 0 =>
                                    let H3 : False :=
                                        eq_ind (S m)
                                               (fun e : nat =>
                                                  nat_rect (fun _ : nat => Prop) False
                                                           (fun (_ : nat) (_ : Prop) => True) e) I 0 H2 in
                                    False_ind (S (S n1) <= m -> None <> None) H3) H1 H0) 0 H in
                   H0 eq_refl)) n0)
      (fun (a : A) (l0 : list A)
           (IHl : forall n0 : nat, List.nth_error l0 n0 <> None <-> n0 < length l0)
           (n0 : nat) =>
         nat_ind
           (fun n1 : nat =>
              List.nth_error (a :: l0) n1 <> None <-> n1 < length (a :: l0))
           (conj
              (fun _ : Some a <> None =>
                 Gt.gt_le_S 0 (S (length l0))
                            (Lt.lt_le_S 0 (S (length l0)) (PeanoNat.Nat.lt_0_succ (length l0))))
              (fun (_ : 0 < S (length l0)) (H0 : Some a = None) =>
                 let H1 : None = None -> False :=
                     eq_ind (Some a) (fun y : option A => y = None -> False)
                            (fun H1 : Some a = None =>
                               (fun H2 : Some a = None =>
                                  let H3 : False :=
                                      eq_ind (Some a)
                                             (fun e : option A =>
                                                option_rect (fun _ : option A => Prop)
                                                            (fun _ : A => True) False e) I None H2 in
                                  False_ind False H3) H1) None H0 in
                 H1 eq_refl))
           (fun (n1 : nat)
                (_ : List.nth_error (a :: l0) n1 <> None <-> n1 < length (a :: l0))
            =>
              (fun lemma : List.nth_error l0 n1 <> None <-> n1 < length l0 =>
                 Morphisms.trans_co_eq_inv_impl_morphism RelationClasses.iff_Transitive
                                                         (List.nth_error l0 n1 <> None) (n1 < length l0) lemma
                                                         (S n1 < S (length l0)) (S n1 < S (length l0))
                                                         (Morphisms.eq_proper_proxy (S n1 < S (length l0))))
                (IHl n1)
                (conj
                   (fun H : n1 < length l0 =>
                      Gt.gt_le_S (S n1) (S (length l0)) (Lt.lt_n_S n1 (length l0) H))
                   (fun H : S n1 < S (length l0) =>
                      Gt.gt_le_S n1 (length l0) (Gt.gt_S_le (S n1) (length l0) H)))) n0)
      l n.
  Lemma test_nth_error_Some : actual_nth_error_Some = expected_nth_error_Some. Proof. reflexivity. Qed.

  Preprocess List.nth_error_split as actual_nth_error_split.
  Definition expected_nth_error_split (A : Type) (l : list A) (n : nat) (a : A) :
    List.nth_error l n = Some a -> exists l1 l2 : list A, l = (l1 ++ a :: l2) /\ length l1 = n
    :=
      nat_ind
        (fun n0 : nat =>
           forall l0 : list A,
             List.nth_error l0 n0 = Some a ->
             exists l1 l2 : list A, l0 = (l1 ++ a :: l2) /\ length l1 = n0)
        (fun l0 : list A =>
           list_ind
             (fun l1 : list A =>
                List.nth_error l1 0 = Some a ->
                exists l2 l3 : list A, l1 = (l2 ++ a :: l3) /\ length l2 = 0)
             (fun H : List.nth_error nil 0 = Some a =>
                let H0 :
                      Some a = Some a ->
                      exists l1 l2 : list A, nil = (l1 ++ a :: l2) /\ length l1 = 0 :=
                    eq_ind (List.nth_error nil 0)
                           (fun y : option A =>
                              y = Some a ->
                              exists l1 l2 : list A, nil = (l1 ++ a :: l2) /\ length l1 = 0)
                           (fun H0 : None = Some a =>
                              (fun H1 : None = Some a =>
                                 let H2 : False :=
                                     eq_ind None
                                            (fun e : option A =>
                                               option_rect (fun _ : option A => Prop)
                                                           (fun _ : A => False) True e) I
                                            (Some a) H1 in
                                 False_ind
                                   (exists l1 l2 : list A,
                                       nil = (l1 ++ a :: l2) /\ length l1 = 0) H2) H0)
                           (Some a) H in
                H0 eq_refl)
             (fun (x : A) (l1 : list A)
                  (_ : List.nth_error l1 0 = Some a ->
                       exists l2 l3 : list A,
                         l1 = (l2 ++ a :: l3) /\ length l2 = 0)
                  (H : List.nth_error (x :: l1) 0 = Some a) =>
                ex_intro
                  (fun l2 : list A =>
                     exists l3 : list A,
                       (x :: l1) = (l2 ++ a :: l3) /\ length l2 = 0) nil
                  (ex_intro
                     (fun l2 : list A =>
                        (x :: l1) = (nil ++ a :: l2) /\ length nil = 0) l1
                     (let H0 : x = a :=
                          f_equal
                            (fun e : option A =>
                               option_rect (fun _ : option A => A) (fun a0 : A => a0) x e)
                            H in
                      (fun H1 : x = a =>
                         eq_ind_r
                           (fun x0 : A =>
                              (x0 :: l1) = (nil ++ a :: l1) /\ length nil = 0)
                           (conj eq_refl eq_refl) H1) H0))) l0)
        (fun (n0 : nat)
             (IH : forall l0 : list A,
                 List.nth_error l0 n0 = Some a ->
                 exists l1 l2 : list A, l0 = (l1 ++ a :: l2) /\ length l1 = n0)
             (l0 : list A) =>
           list_ind
             (fun l1 : list A =>
                List.nth_error l1 (S n0) = Some a ->
                exists l2 l3 : list A, l1 = (l2 ++ a :: l3) /\ length l2 = S n0)
             (fun H : List.nth_error nil (S n0) = Some a =>
                let H0 :
                      Some a = Some a ->
                      exists l1 l2 : list A, nil = (l1 ++ a :: l2) /\ length l1 = S n0 :=
                    eq_ind (List.nth_error nil (S n0))
                           (fun y : option A =>
                              y = Some a ->
                              exists l1 l2 : list A,
                                nil = (l1 ++ a :: l2) /\ length l1 = S n0)
                           (fun H0 : None = Some a =>
                              (fun H1 : None = Some a =>
                                 let H2 : False :=
                                     eq_ind None
                                            (fun e : option A =>
                                               option_rect (fun _ : option A => Prop)
                                                           (fun _ : A => False) True e) I
                                            (Some a) H1 in
                                 False_ind
                                   (exists l1 l2 : list A,
                                       nil = (l1 ++ a :: l2) /\ length l1 = S n0) H2) H0)
                           (Some a) H in
                H0 eq_refl)
             (fun (x : A) (l1 : list A)
                  (_ : List.nth_error l1 (S n0) = Some a ->
                       exists l2 l3 : list A,
                         l1 = (l2 ++ a :: l3) /\ length l2 = S n0)
                  (H : List.nth_error (x :: l1) (S n0) = Some a) =>
                let e :
                      exists l2 l3 : list A, l1 = (l2 ++ a :: l3) /\ length l2 = n0 :=
                    IH l1 H in
                ex_ind
                  (fun (l2 : list A)
                       (H0 : exists l3 : list A,
                           l1 = (l2 ++ a :: l3) /\ length l2 = n0) =>
                     ex_ind
                       (fun (l3 : list A)
                            (H1 : l1 = (l2 ++ a :: l3) /\ length l2 = n0) =>
                          and_ind
                            (fun (H2 : l1 = (l2 ++ a :: l3)) (H3 : length l2 = n0) =>
                               ex_intro
                                 (fun l4 : list A =>
                                    exists l5 : list A,
                                      (x :: l1) = (l4 ++ a :: l5) /\ length l4 = S n0)
                                 (x :: l2)
                                 (ex_intro
                                    (fun l4 : list A =>
                                       (x :: l1) = ((x :: l2) ++ a :: l4) /\
                                       length (x :: l2) = S n0) l3
                                    (conj
                                       (let H4 : l1 = (l2 ++ a :: l3) := H2 in
                                        (let H5 : x = x := eq_refl in
                                         (let H6 : A = A := eq_refl in
                                          (fun (_ : A = A) (_ : x = x)
                                               (H9 : l1 = (l2 ++ a :: l3)) =>
                                             eq_trans
                                               (f_equal (fun f : list A -> list A => f l1)
                                                        eq_refl) (f_equal (cons x) H9)) H6) H5) H4)
                                       (let H4 : length l2 = n0 := H3 in
                                        (fun H5 : length l2 = n0 =>
                                           eq_trans
                                             (f_equal (fun f : nat -> nat => f (length l2))
                                                      eq_refl) (f_equal S H5)) H4)))) H1) H0) e) l0)
        n l.
  Lemma test_nth_error_split : actual_nth_error_split = expected_nth_error_split. Proof. reflexivity. Qed.

  Preprocess List.nth_error_app1 as actual_nth_error_app1.
  Definition expected_nth_error_app1 (A : Type) (l l' : list A) (n : nat) :
    n < length l -> List.nth_error (l ++ l') n = List.nth_error l n
    :=
      nat_ind
        (fun n0 : nat =>
           forall l0 : list A,
             n0 < length l0 -> List.nth_error (l0 ++ l') n0 = List.nth_error l0 n0)
        (fun l0 : list A =>
           list_ind
             (fun l1 : list A =>
                0 < length l1 -> List.nth_error (l1 ++ l') 0 = List.nth_error l1 0)
             (fun H : 0 < length nil =>
                let H0 :
                      length nil = length nil ->
                      List.nth_error (nil ++ l') 0 = List.nth_error nil 0 :=
                    le_ind 1
                           (fun n0 : nat =>
                              n0 = length nil ->
                              List.nth_error (nil ++ l') 0 = List.nth_error nil 0)
                           (fun H0 : 1 = length nil =>
                              (fun H1 : 1 = length nil =>
                                 let H2 : False :=
                                     eq_ind 1
                                            (fun e : nat =>
                                               nat_rect (fun _ : nat => Prop) False
                                                        (fun (_ : nat) (_ : Prop) => True) e) I
                                            (length nil) H1 in
                                 False_ind (List.nth_error (nil ++ l') 0 = List.nth_error nil 0)
                                           H2) H0)
                           (fun (m : nat) (H0 : 1 <= m)
                                (_ : m = length nil ->
                                     List.nth_error (nil ++ l') 0 = List.nth_error nil 0)
                                (H1 : S m = length nil) =>
                              (fun H2 : S m = length nil =>
                                 let H3 : False :=
                                     eq_ind (S m)
                                            (fun e : nat =>
                                               nat_rect (fun _ : nat => Prop) False
                                                        (fun (_ : nat) (_ : Prop) => True) e) I
                                            (length nil) H2 in
                                 False_ind
                                   (1 <= m -> List.nth_error (nil ++ l') 0 = List.nth_error nil 0)
                                   H3) H1 H0) (length nil) H in
                H0 eq_refl)
             (fun (a : A) (l1 : list A)
                  (_ : 0 < length l1 ->
                       List.nth_error (l1 ++ l') 0 = List.nth_error l1 0)
                  (_ : 0 < length (a :: l1)) => eq_refl) l0)
        (fun (n0 : nat)
             (IHn : forall l0 : list A,
                 n0 < length l0 ->
                 List.nth_error (l0 ++ l') n0 = List.nth_error l0 n0)
             (l0 : list A) =>
           list_ind
             (fun l1 : list A =>
                S n0 < length l1 ->
                List.nth_error (l1 ++ l') (S n0) = List.nth_error l1 (S n0))
             (fun H : S n0 < length nil =>
                let H0 :
                      length nil = length nil ->
                      List.nth_error (nil ++ l') (S n0) = List.nth_error nil (S n0) :=
                    le_ind (S (S n0))
                           (fun n1 : nat =>
                              n1 = length nil ->
                              List.nth_error (nil ++ l') (S n0) = List.nth_error nil (S n0))
                           (fun H0 : S (S n0) = length nil =>
                              (fun H1 : S (S n0) = length nil =>
                                 let H2 : False :=
                                     eq_ind (S (S n0))
                                            (fun e : nat =>
                                               nat_rect (fun _ : nat => Prop) False
                                                        (fun (_ : nat) (_ : Prop) => True) e) I
                                            (length nil) H1 in
                                 False_ind
                                   (List.nth_error (nil ++ l') (S n0) = List.nth_error nil (S n0))
                                   H2) H0)
                           (fun (m : nat) (H0 : S (S n0) <= m)
                                (_ : m = length nil ->
                                     List.nth_error (nil ++ l') (S n0) =
                                     List.nth_error nil (S n0)) (H1 : S m = length nil) =>
                              (fun H2 : S m = length nil =>
                                 let H3 : False :=
                                     eq_ind (S m)
                                            (fun e : nat =>
                                               nat_rect (fun _ : nat => Prop) False
                                                        (fun (_ : nat) (_ : Prop) => True) e) I
                                            (length nil) H2 in
                                 False_ind
                                   (S (S n0) <= m ->
                                    List.nth_error (nil ++ l') (S n0) = List.nth_error nil (S n0))
                                   H3) H1 H0) (length nil) H in
                H0 eq_refl)
             (fun (a : A) (l1 : list A)
                  (_ : S n0 < length l1 ->
                       List.nth_error (l1 ++ l') (S n0) = List.nth_error l1 (S n0))
                  (H : S n0 < length (a :: l1)) =>
                IHn l1 (Gt.gt_le_S n0 (length l1) (Gt.gt_S_le (S n0) (length l1) H)))
             l0) n l.
  Lemma test_nth_error_app1 : actual_nth_error_app1 = expected_nth_error_app1. Proof. reflexivity. Qed.

  Preprocess List.nth_error_app2 as actual_nth_error_app2.
  Definition expected_nth_error_app2 (A : Type) (l l' : list A) (n : nat) :
    length l <= n -> List.nth_error (l ++ l') n = List.nth_error l' (n - length l)
    :=
      nat_ind
        (fun n0 : nat =>
           forall l0 : list A,
             length l0 <= n0 ->
             List.nth_error (l0 ++ l') n0 = List.nth_error l' (n0 - length l0))
        (fun l0 : list A =>
           list_ind
             (fun l1 : list A =>
                length l1 <= 0 ->
                List.nth_error (l1 ++ l') 0 = List.nth_error l' (0 - length l1))
             (fun _ : length nil <= 0 => eq_refl)
             (fun (a : A) (l1 : list A)
                  (_ : length l1 <= 0 ->
                       List.nth_error (l1 ++ l') 0 = List.nth_error l' (0 - length l1))
                  (H : length (a :: l1) <= 0) =>
                let H0 :
                      0 = 0 ->
                      List.nth_error ((a :: l1) ++ l') 0 =
                      List.nth_error l' (0 - length (a :: l1)) :=
                    le_ind (length (a :: l1))
                           (fun n0 : nat =>
                              n0 = 0 ->
                              List.nth_error ((a :: l1) ++ l') 0 =
                              List.nth_error l' (0 - length (a :: l1)))
                           (fun H0 : length (a :: l1) = 0 =>
                              (fun H1 : length (a :: l1) = 0 =>
                                 let H2 : False :=
                                     eq_ind (length (a :: l1))
                                            (fun e : nat =>
                                               nat_rect (fun _ : nat => Prop) False
                                                        (fun (_ : nat) (_ : Prop) => True) e) I 0 H1 in
                                 False_ind
                                   (List.nth_error ((a :: l1) ++ l') 0 =
                                    List.nth_error l' (0 - length (a :: l1))) H2) H0)
                           (fun (m : nat) (H0 : length (a :: l1) <= m)
                                (_ : m = 0 ->
                                     List.nth_error ((a :: l1) ++ l') 0 =
                                     List.nth_error l' (0 - length (a :: l1)))
                                (H1 : S m = 0) =>
                              (fun H2 : S m = 0 =>
                                 let H3 : False :=
                                     eq_ind (S m)
                                            (fun e : nat =>
                                               nat_rect (fun _ : nat => Prop) False
                                                        (fun (_ : nat) (_ : Prop) => True) e) I 0 H2 in
                                 False_ind
                                   (length (a :: l1) <= m ->
                                    List.nth_error ((a :: l1) ++ l') 0 =
                                    List.nth_error l' (0 - length (a :: l1))) H3) H1 H0) 0 H in
                H0 eq_refl) l0)
        (fun (n0 : nat)
             (IHn : forall l0 : list A,
                 length l0 <= n0 ->
                 List.nth_error (l0 ++ l') n0 = List.nth_error l' (n0 - length l0))
             (l0 : list A) =>
           list_ind
             (fun l1 : list A =>
                length l1 <= S n0 ->
                List.nth_error (l1 ++ l') (S n0) = List.nth_error l' (S n0 - length l1))
             (fun _ : length nil <= S n0 => eq_refl)
             (fun (a : A) (l1 : list A)
                  (_ : length l1 <= S n0 ->
                       List.nth_error (l1 ++ l') (S n0) =
                       List.nth_error l' (S n0 - length l1))
                  (H : length (a :: l1) <= S n0) =>
                IHn l1 (Gt.gt_S_le (length l1) n0 H)) l0) n l.
  Lemma test_nth_error_app2 : actual_nth_error_app2 = expected_nth_error_app2. Proof. reflexivity. Qed.

  Preprocess List.remove as actual_remove.
  Definition expected_remove (A : Type) (eq_dec : forall x y : A, {x = y} + {x <> y}) (x : A) (l : list A) : list A :=
    list_rect (fun _ : list A => A -> list A) (fun _ : A => nil)
              (fun (r : A) (_ : list A) (remove : A -> list A) (x0 : A) =>
                 sumbool_rect (fun _ : {x0 = r} + {x0 <> r} => list A)
                              (fun _ : x0 = r => remove x0) (fun _ : x0 <> r => (r :: remove x0))
                              (eq_dec x0 r)) l x.
  Lemma test_remove : actual_remove = expected_remove. Proof. reflexivity. Qed.

  Preprocess List.last as actual_last.
  Definition expected_last (A : Type) (l : list A) : A -> A :=
    list_rect (fun _ : list A => A -> A) (fun d : A => d)
              (fun (a : A) (l0 : list A) (last : A -> A) (d : A) =>
                 list_rect (fun _ : list A => A) a
                           (fun (_ : A) (_ : list A) (_ : A) => last d) l0) l.
  Lemma test_last : actual_last = expected_last. Proof. reflexivity. Qed.

  Preprocess List.removelast as actual_removelast.
  Definition expected_removelast (A : Type) (l : list A) : list A :=
    list_rect (fun _ : list A => list A) nil
              (fun (a : A) (l0 removelast : list A) =>
                 list_rect (fun _ : list A => list A) nil
                           (fun (_ : A) (_ _ : list A) => (a :: removelast)) l0) l.
  Lemma test_removelast : actual_removelast = expected_removelast. Proof. reflexivity. Qed.

  Preprocess List.app_removelast_last as actual_app_removelast_last.
  Definition expected_app_removelast_last (A : Type) (l : list A) :
    forall (d : A), l <> nil -> l = (List.removelast l ++ List.last l d :: nil)
    :=
      list_ind
        (fun l0 : list A =>
           forall d : A,
             l0 <> nil -> l0 = (List.removelast l0 ++ List.last l0 d :: nil))
        (fun (d : A) (H : nil <> nil) =>
           let n : False := H eq_refl in
           False_ind (nil = (List.removelast nil ++ List.last nil d :: nil)) n)
        (fun (a : A) (l0 : list A)
             (IHl : forall d : A,
                 l0 <> nil ->
                 l0 = (List.removelast l0 ++ List.last l0 d :: nil))
             (d : A) (_ : (a :: l0) <> nil) =>
           list_ind
             (fun l1 : list A =>
                (forall d0 : A,
                    l1 <> nil -> l1 = (List.removelast l1 ++ List.last l1 d0 :: nil)) ->
                (a :: l1) =
                (List.removelast (a :: l1) ++ List.last (a :: l1) d :: nil))
             (fun
                 _ : forall d0 : A,
                   nil <> nil ->
                   nil = (List.removelast nil ++ List.last nil d0 :: nil) =>
                 eq_refl)
             (fun (a0 : A) (l1 : list A)
                  (_ : (forall d0 : A,
                           l1 <> nil ->
                           l1 = (List.removelast l1 ++ List.last l1 d0 :: nil)) ->
                       (a :: l1) =
                       (List.removelast (a :: l1) ++ List.last (a :: l1) d :: nil))
                  (IHl0 : forall d0 : A,
                      (a0 :: l1) <> nil ->
                      (a0 :: l1) =
                      (List.removelast (a0 :: l1) ++ List.last (a0 :: l1) d0 :: nil))
              =>
                eq_ind_r
                  (fun l2 : list A =>
                     (a :: l2) =
                     (List.removelast (a :: a0 :: l1) ++
                                      List.last (a :: a0 :: l1) d :: nil)) eq_refl
                  (IHl0 d
                        (fun H : (a0 :: l1) = nil =>
                           let H0 : False :=
                               eq_ind (a0 :: l1)
                                      (fun e : list A =>
                                         list_rect (fun _ : list A => Prop) False
                                                   (fun (_ : A) (_ : list A) (_ : Prop) => True) e) I nil H
                           in
                           False_ind False H0))) l0 IHl) l.
  Lemma test_app_removelast_last : actual_app_removelast_last = expected_app_removelast_last. Proof. reflexivity. Qed.

  Preprocess List.exists_last as actual_exists_last.
  Definition expected_exists_last (A : Type) (l : list A) : l <> nil -> {l' : list A & {a : A | l = (l' ++ a :: nil)}} :=
    list_rect
      (fun l0 : list A =>
         l0 <> nil -> {l' : list A & {a : A | l0 = (l' ++ a :: nil)}})
      (fun H : nil <> nil =>
         let n : False := H eq_refl in
         False_rect {l' : list A & {a : A | nil = (l' ++ a :: nil)}} n)
      (fun (a : A) (l0 : list A)
           (IHl : l0 <> nil ->
                  {l' : list A & {a0 : A | l0 = (l' ++ a0 :: nil)}})
           (_ : (a :: l0) <> nil) =>
         list_rect
           (fun l1 : list A =>
              (l1 <> nil -> {l' : list A & {a0 : A | l1 = (l' ++ a0 :: nil)}}) ->
              {l' : list A & {a0 : A | (a :: l1) = (l' ++ a0 :: nil)}})
           (fun
               _ : nil <> nil ->
                   {l' : list A & {a0 : A | nil = (l' ++ a0 :: nil)}} =>
               existT
                 (fun l' : list A =>
                    {a0 : A | (a :: nil) = (l' ++ a0 :: nil)}) nil
                 (exist (fun a0 : A => (a :: nil) = (nil ++ a0 :: nil)) a
                        eq_refl))
           (fun (a0 : A) (l1 : list A)
                (_ : (l1 <> nil ->
                      {l' : list A & {a1 : A | l1 = (l' ++ a1 :: nil)}}) ->
                     {l' : list A &
                           {a1 : A | (a :: l1) = (l' ++ a1 :: nil)}})
                (IHl0 : (a0 :: l1) <> nil ->
                        {l' : list A &
                              {a1 : A | (a0 :: l1) = (l' ++ a1 :: nil)}}) =>
              let s :=
                  IHl0
                    (fun H : (a0 :: l1) = nil =>
                       let H0 : False :=
                           eq_ind (a0 :: l1)
                                  (fun e : list A =>
                                     list_rect (fun _ : list A => Prop) False
                                               (fun (_ : A) (_ : list A) (_ : Prop) => True) e) I nil H in
                       False_ind False H0) in
              sigT_rect
                (fun
                    _ : {l' : list A &
                              {a1 : A | (a0 :: l1) = (l' ++ a1 :: nil)}} =>
                    {l' : list A &
                          {a1 : A | (a :: a0 :: l1) = (l' ++ a1 :: nil)}})
                (fun (l' : list A)
                     (s0 : {a1 : A | (a0 :: l1) = (l' ++ a1 :: nil)}) =>
                   sig_rect
                     (fun _ : {a1 : A | (a0 :: l1) = (l' ++ a1 :: nil)} =>
                        {l'0 : list A &
                               {a1 : A | (a :: a0 :: l1) = (l'0 ++ a1 :: nil)}})
                     (fun (a' : A) (H : (a0 :: l1) = (l' ++ a' :: nil)) =>
                        eq_rect_r
                          (fun l2 : list A =>
                             {l'0 : list A &
                                    {a1 : A | (a :: l2) = (l'0 ++ a1 :: nil)}})
                          (existT
                             (fun l'0 : list A =>
                                {a1 : A |
                                 (a :: l' ++ a' :: nil) = (l'0 ++ a1 :: nil)})
                             (a :: l')
                             (exist
                                (fun a1 : A =>
                                   (a :: l' ++ a' :: nil) =
                                   ((a :: l') ++ a1 :: nil)) a' eq_refl)) H) s0) s) l0
           IHl) l.
  Lemma test_exists_last : actual_exists_last = expected_exists_last. Proof. reflexivity. Qed.

  Preprocess List.list_power as actual_list_power.
  Definition expected_list_power (A B : Type) (l : list A) : list B -> list (list (A * B)) :=
    list_rect
      (fun _ : list A => forall B0 : Type, list B0 -> list (list (A * B0)))
      (fun (B0 : Type) (_ : list B0) => (nil :: nil)%list)
      (fun (l0 : A) (_ : list A)
           (list_power : forall B0 : Type, list B0 -> list (list (A * B0)))
           (B0 : Type) (l' : list B0) =>
         List.flat_map
           (fun f : list (A * B0) =>
              List.map (fun y : B0 => ((l0, y) :: f)%list) l')
           (list_power B0 l')) l B.
  Lemma test_list_power : actual_list_power = expected_list_power. Proof. reflexivity. Qed.

End ListTests.
