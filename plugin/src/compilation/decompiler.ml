
open Names
open Constr
open Environ
open Envutils
open Tactics
open Pp
open Contextutils
open Equtils
open Apputils
   
(* Abstraction of Coq tactics supported by this decompiler.
   Serves as an intermediate representation that can be either
   transformed into a string or a sequence of actual tactics. *)
type tact =
  | Intro of Id.t
  | Intros of Id.t list
  | Apply of env * types
  (* Proof that x = y if true, y = x if false. *)
  | Rewrite of env * types * bool
        
(* Return the string representation of a single tactic. *)
let show_tact sigma tac : Pp.t =
  (match tac with
   | Intro n -> str ("intro " ^ Id.to_string n)
   | Intros ns ->
      let names = String.concat " " (List.map Id.to_string ns) in
      str ("intros " ^ names)
   | Apply (env, trm) ->
      let body_s = Printer.pr_constr_env env sigma trm in
      str "apply " ++ body_s
   | Rewrite (env, trm, left) ->
      let s = Printer.pr_constr_env env sigma trm in
      let arrow = if left then "<- " else "" in
      str ("rewrite " ^ arrow) ++ s)
  ++ str ".\n"

(* Converts "intro n. intro m. ..." into "intros n m ..." *)
let collapse_intros (tacs : tact list) : tact list =
  List.fold_right (fun tac acc ->
      match tac with
      | Intro n ->
         (match acc with
          | Intro m :: xs -> Intros [n; m] :: xs
          | Intros ns :: xs -> Intros (n :: ns) :: xs
          | _ -> Intro n :: acc)
      | t -> t :: acc) tacs []

(* Finds all rel names pushed onto an environment. *)
let get_pushed_names env =
  let names =
    List.map (fun x ->
        match x with
        | CRD.LocalAssum (n, _) -> n
        | CRD.LocalDef (n, _, _) -> n)
      (lookup_all_rels env) in
  Id.Set.of_list
    (List.map (fun x ->
         match x with
         | Anonymous ->
            failwith "Unexpected Anonymous in get_pushed_names."
         | Name n -> n) names)

(* Functions used with the rewrite tactic. *)
let is_rewrite_r trm : bool =
  let eq_term = equal trm in
  eq_term eq_ind_r || eq_term eq_rec_r (* || eq_term eq_rect_r *)
  
(* Rewrite functions using "<-". *)
let is_rewrite_l trm : bool =
  let eq_term = equal trm in
  eq_term eq_ind || eq_term eq_rec (* || eq_term eq_rect*)

(* Decompile a term into its equivalent tactic list. *)
let tac_from_term env trm : tact list =
  let rec first_pass env trm =
    match kind trm with
    (* "fun x => ..." -> "intro x." *)
    | Lambda (n, t, b) ->
       let name = match n with
         | Anonymous ->
            let in_env = get_pushed_names env in
            fresh_id_in_env in_env (Id.of_string "H") env
         | Name n -> n in
       let env = push_local (Name name, t) env in
       Intro name :: first_pass env b
    (* Match on well-known functions used in the proof. *)
    | App (f, args) ->
       (* Applying to something that *might* be in eta-expanded 
          form, try to reduce. *)
       if isLambda f then
         let app_one = mkApp (f, [|Array.get args 0|]) in
         let beta = Reduction.whd_betaiota env app_one in
         let app = mkApp (beta, Array.sub args 1 (Array.length args - 1)) in
         first_pass env app
       else
         let left = is_rewrite_l f in
         if left || is_rewrite_r f then
           let prf_eq = Array.get args 5 in
           let elem = Array.get args 3 in
           Rewrite (env, prf_eq, left) :: first_pass env elem
         else
           [Apply (env, trm)]
    (* Remainder of body, simply apply it. *)
    | _ -> [Apply (env, trm)] in
  (* Perform second pass to revise greedy tactic list. *)
  collapse_intros (first_pass env trm)
    
(* Convert a tactic list into its string representation. *)
let tac_to_string sigma (tacs : tact list) : Pp.t =
  seq (List.map (show_tact sigma) tacs)
    
    
