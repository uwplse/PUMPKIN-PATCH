
open Names
open Constr
open Environ
open Envutils
open Pp

(* Abstraction of Coq tactics supported by this decompiler. *)
type tact =
  | Intro of Id.t
  | Apply of env * types
        
(* Return the string representation of a single tactic.
   TODO: Indentation/bulleting
         Don't expose this in .mli *)
let show_tact sigma tac : Pp.t =
  match tac with
  | Intro n -> str ("intro " ^ Id.to_string n ^ ".")
  | Apply (env, trm) ->
     let body_s = Printer.pr_constr_env env sigma trm in
     str "apply " ++ body_s ++ str "."

(* Decompile a term into its equivalent tactic list. *)
let rec tac_from_term env trm : tact list =
  match kind trm with
  | Lambda (n, t, b) ->
     let name = match n with
       | Anonymous -> Id.of_string "H" (* TODO: Hn for each new name *)
       | Name n -> n in
     let env = push_local (Name name, t) env in
     (Intro name) :: tac_from_term env b
  | _ -> [Apply (env, trm)]

(* Convert a tactic list into its string representation. *)
let rec tac_to_string sigma (tacs : tact list) : Pp.t =
  match tacs with
  | tac :: tacs' ->
     let tac_s = show_tact sigma tac in
     tac_s ++ str "\n" ++ tac_to_string sigma tacs'
  | [] -> str ""
