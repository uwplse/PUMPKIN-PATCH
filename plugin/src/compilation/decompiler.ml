
open Names
open Constr
open Environ
open Envutils
open Tactics
open Pp
open Contextutils

(* Abstraction of Coq tactics supported by this decompiler.
   Serves as an intermediate representation that can be either
   transformed into a string or a sequence of actual tactics. *)
type tact =
  | Intro of Id.t
  | Intros of Id.t list
  | Apply of env * types
        
(* Return the string representation of a single tactic. *)
let show_tact sigma tac : Pp.t =
  (match tac with
   | Intro n -> str ("intro " ^ Id.to_string n)
   | Intros ns ->
      let names = String.concat " " (List.map Id.to_string ns) in
      str ("intros " ^ names)
   | Apply (env, trm) ->
      let body_s = Printer.pr_constr_env env sigma trm in
      str "apply " ++ body_s)
  ++ str ".\n" (* maybe ";" in future *)

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
       (Intro name) :: first_pass env b
    (* Remainder of body, simply apply it. *)
    | _ -> [Apply (env, trm)] in
  (* Perform second pass to revise greedy tactic list. *)
  collapse_intros (first_pass env trm)
  
  
(* Convert a tactic list into its string representation. *)
let tac_to_string sigma (tacs : tact list) : Pp.t =
  seq (List.map (show_tact sigma) tacs)
    
    
