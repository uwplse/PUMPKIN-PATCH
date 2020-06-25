
open Names
open Constr
open Environ
open Envutils
open Tactics
open Pp
open Contextutils
open Equtils
open Apputils
open Proputils
open Indutils
open Funutils
open Inference
open Vars
open Utilities
open Zooming
open Nameutils
   
(*
 * Only in OCaml 4.08.0 onward, so we implement ourselves
 *)
let filter_map f l =
  let f_somes = List.filter (fun o -> Option.has_some o) (List.map f l) in
  List.map Option.get f_somes
                    
    

(* Monadic bind on option types. *)
let (>>=) = Option.bind

(* Alternative (monad plus) operator on functions of
   the form a' -> b' -> c' option. *)
let (<|>) f g x y =
  match f x y, g x y with
  | Some z, _ -> Some z
  | None, z -> z

             
(* Abstraction of Coq tactics supported by this decompiler.
   Serves as an intermediate representation that can be either
   transformed into a string or a sequence of actual tactics. *)
type tact =
  | Intro of Id.t
  | Intros of Id.t list
  | Apply of env * types
  (* Proof that x = y if true, y = x if false. *)
  | Rewrite of env * types * bool
  (* Proof that y = x if true, etc. *)
  | RewriteIn of env * types * types * bool
  | ApplyIn of env * types * types
  | Pose of env * types * Id.t
  | Induction of env * types * Id.t list list * tact list list
  | Reflexivity
  | Simpl
  | Left
  | Right
  | Split of tact list * tact list
  | Revert of Id.t list
  

  

(* Option monad over function application. *)
let try_app (trm : constr) : (constr * constr array) option =
  match kind trm with
  | App (f, args) -> Some (f, args)
  | _ -> None

(* Option monad over relative indices. *)
let try_rel (trm : constr) : int option =
  match kind trm with
  | Rel i -> Some i
  | _ -> None

(* Monadic guard for option. *)
let guard (b : bool) : unit option =
  if b then Some () else None

(* Converts "intro n. intro m. ..." into "intros n m ..." *)
let rec collapse_intros (tacs : tact list) : tact list =
  List.fold_right (fun tac acc ->
      match tac with
      | Intro n ->
         (match acc with
          | Intro m :: xs -> Intros [n; m] :: xs
          | Intros ns :: xs -> Intros (n :: ns) :: xs
          | _ -> Intro n :: acc)
      | Induction (x, y, z, goals) ->
         [ Induction (x, y, z, List.map collapse_intros goals) ]
      | Split (goal1, goal2) ->
         [ Split (collapse_intros goal1, collapse_intros goal2) ]
      | t -> t :: acc) tacs []
  
(* Converts "apply eq_refl." into "reflexivity." *)
let rec reflexivity (tacs : tact list) : tact list =
  List.map (fun tac ->
      match tac with
      | Apply (env, term) ->
         Option.default tac
           (try_app term >>= fun (f, args) ->
            dest_eq_refl_opt (mkApp (f, args)) >>= fun _ ->
            Some Reflexivity)
      | Induction (x, y, z, goals) ->
         Induction (x, y, z, List.map reflexivity goals)
      | Split (goal1, goal2) ->
         Split (reflexivity goal1, reflexivity goal2)
      | _ -> tac) tacs

(* Inserts "simpl." before every rewrite. *)
let rec simpl tacs : tact list =
  match tacs with
  | [] -> []
  | Rewrite (e, t, l) :: tacs' ->
     Simpl :: Rewrite (e, t, l) :: simpl tacs'
  | tac :: tacs' -> tac :: simpl tacs'
  
(* Performs the bulk of decompilation on a proof term. 
   Returns a list of tactics. *)
let rec first_pass env sigma trm =
  (* Apply single beta reduction to terms that *might*
       be in eta expanded form. *)
  let trm = Reduction.whd_betaiota env trm in
  let choose f x = Option.default [Apply (env, trm)] (f x (env, sigma)) in
  match kind trm with
  (* "fun x => ..." -> "intro x." *)
  | Lambda (n, t, b) ->
     let name = fresh_name env n in
     let env = push_local (Name name, t) env in
     Intro name :: first_pass env sigma b
  (* Match on well-known functions used in the proof. *)
  | App (f, args) ->
     choose (rewrite <|> induction <|> left <|> right <|> split) (f, args)
  (* Hypothesis transformations or generation tactics. *)
  | LetIn (n, valu, typ, body) ->   
     choose (rewrite_in <|> apply_in <|> pose) (n, valu, typ, body)
  (* Remainder of body, simply apply it. *)
  | _ -> [Apply (env, trm)]

(* Application of a equality eliminator. *)
and rewrite (f, args) (env, sigma) : tact list option =
  dest_rewrite (mkApp (f, args)) >>= fun rewr -> 
  Some (Rewrite (env, rewr.eq, rewr.left) :: first_pass env sigma rewr.px)

(* Applying an eliminator for induction on a hypothesis in context. *)
and induction (f, args) (env, sigma) : tact list option =
  guard (is_elim env f) >>= fun _ ->
  guard (not (is_rewrite f)) >>= fun _ ->
  let app = mkApp (f, args) in
  let sigma, ind = deconstruct_eliminator env sigma app in
  let ind_args = ind.final_args in
  inductive_of_elim env (destConst f) >>= fun from_i ->
  let from_m = lookup_mind from_i env in
  let ari = arity (type_of_inductive env 0 from_m) in
  let ind_pos = ari - List.length ind.pms in
  if ind_pos >= List.length ind.final_args
  then let _ = Printing.debug_term env app "Failed to decompile induction: " in None
  else 
    let ind_var = List.nth ind.final_args ind_pos in
    let forget = List.length ind.final_args - ind_pos - 1 in
    Printf.printf "List.length ind.final_args = %d\n" (List.length ind.final_args);
    Printf.printf "ind_pos = %d\n" (ind_pos);
    Printf.printf "forget  = %d\n" (forget);
    Printf.printf "arity   = %d\n\n" (ari);
    (* Compute bindings and goals for each case. *)
    let zooms = List.map (zoom_lambda_names env forget) ind.cs in
    let names = List.map (fun (_, _, names) -> names) zooms in
    let cases = List.map (fun (env, trm, _) ->
                    simpl (first_pass env sigma trm)) zooms in
    (* Take final args after inducted value, and revert them if they're named. *)
    let rev_idx = filter_map try_rel (take forget (List.rev ind.final_args)) in
    let idx_to_name i = expect_name (fst (rel_name_type (lookup_rel i env))) in
    let reverts = List.map idx_to_name rev_idx in
    let ind = [ Induction (env, ind_var, names, cases) ] in
    Some (if reverts == [] then ind else Revert reverts :: ind)
    
(* Choose left proof to construct or. *)
and left (f, args) (env, sigma) : tact list option =
  dest_or_introl (mkApp (f, args)) >>= fun args ->
  Some (Left :: first_pass env sigma args.ltrm)

(* Choose right proof to construct or. *)
and right (f, args) (env, sigma) : tact list option =
  dest_or_intror (mkApp (f, args)) >>= fun args ->
  Some (Right :: first_pass env sigma args.rtrm)

(* Branch two goals as arguments to conj. *)
and split (f, args) (env, sigma) : tact list option =
  dest_conj (mkApp (f, args)) >>= fun args ->
  let lhs = first_pass env sigma args.ltrm in
  let rhs = first_pass env sigma args.rtrm in
  Some [ Split (lhs, rhs) ]

(* Value must be a rewrite on a hypothesis in context. *)
and rewrite_in (_, valu, _, body) (env, sigma) : tact list option =
  let valu = Reduction.whd_betaiota env valu in
  try_app valu                   >>= fun (f, args) ->
  dest_rewrite (mkApp (f, args)) >>= fun rewr -> 
  try_rel rewr.px                >>= fun idx ->
  guard (noccurn (idx + 1) body) >>= fun _ ->
  let n, t = rel_name_type (lookup_rel idx env) in
  let env' = push_local (n, t) env in
  Some (RewriteIn (env, rewr.eq, rewr.px, rewr.left) :: first_pass env' sigma body)

(* Value must be an application with last argument in context. *)
and apply_in (_, valu, _, body) (env, sigma) : tact list option =
  let valu = Reduction.whd_betaiota env valu in
  try_app valu >>= fun (f, args) ->
  let len = Array.length args in
  let hyp = args.(len - 1) in
  try_rel hyp >>= fun idx ->                       (* let _ := ... H *)
  guard (noccurn (idx + 1) body) >>= fun _ ->      (* H does not occur in body *)
  let n, t = rel_name_type (lookup_rel idx env) in (* "H" *)
  let env' = push_local (n, t) env in              (* change type of "H" *)
  let prf = mkApp (f, Array.sub args 0 (len - 1)) in
  let app_in = ApplyIn (env, prf, hyp) in
  
  if false (* arity f - len == 1          *)                  (* f : A -> B *)
  then Some (app_in :: first_pass env' sigma body)
  else (* For "apply f in a", Coq produces a goal for each argument of f. *)
    try_app body >>= fun (f', args') ->              (* let _ := ... H1 in ... H2 *)
    let args' = List.map (first_pass env' sigma) (Array.to_list args') in
    Some (app_in :: List.concat ((first_pass env' sigma f') :: args'))

(* Last resort decompile let-in as a pose.  *)
and pose (n, valu, t, body) (env, sigma) : tact list option =
  let n' = fresh_name env (Name (expect_name n)) in
  let env' = push_let_in (n, valu, t) env in
  let decomp_body = first_pass env' sigma body in
  (* If the binding is NEVER used, just skip this. *)
  if noccurn 1 body then Some decomp_body
  else Some (Pose (env, valu, n') :: decomp_body)
       
(* Decompile a term into its equivalent tactic list. *)
let tac_from_term env sigma trm : tact list =
  (* Perform second pass to revise greedy tactic list. *)
  reflexivity (collapse_intros (first_pass env sigma trm))

(* Generate indentation space before bullet. *)
let indent level =
  let spacing level = (level - 2) / 3 + 2 in
  let rec aux i = if i <= 1 then 0
                  else spacing i + aux (i - 1)
  in str (String.make (aux level) ' ')

(* Make bullets in order of: -, +, *, --, ++, **, ---, etc. *)
let bullet level =
  let num = (level + 2) / 3 in
  let blt = match level mod 3 with
    | 0 -> '*'
    | 1 -> '-'
    | 2 -> '+' in
  str (String.make num blt) ++ str " "
  
(* Indented string representation of a tactic list. *)
let rec show_tact_list level sigma (tacs : tact list) : Pp.t =
  let f i = show_tact (i == 0 && level > 0) level sigma in
  seq (List.mapi f tacs)
    
(* Return the string representation of a single tactic. *)
and show_tact (bulletted : bool) level sigma tac : Pp.t =
  let prnt = fun e -> Printer.pr_constr_env e sigma in
  let fin = str ".\n" in
  let full_indent = if bulletted
                    then indent level ++ bullet level
                    else indent (level + 1) in
  full_indent ++
    (match tac with
     | Intro n -> str ("intro " ^ Id.to_string n) ++ fin
     | Intros ns ->
        let names = String.concat " " (List.map Id.to_string ns) in
        str ("intros " ^ names) ++ fin
     | Apply (env, trm) ->
        let body_s = prnt env trm in
        str "apply " ++ body_s ++ fin
     | Rewrite (env, trm, left) ->
        let s = prnt env trm in
        let arrow = if left then "<- " else "" in
        str ("rewrite " ^ arrow) ++ s ++ fin
     | RewriteIn (env, prf, hyp, left) ->
        let prf_s, hyp_s = prnt env prf, prnt env hyp in
        let arrow = if left then "" else "<- " in
        str ("rewrite " ^ arrow) ++ prf_s ++ str " in " ++ hyp_s ++ fin
     | ApplyIn (env, prf, hyp) ->
        let prf_s, hyp_s = prnt env prf, prnt env hyp in
        str "apply " ++ prf_s ++ str " in " ++ hyp_s ++ fin
     | Pose (env, hyp, n) ->
        let n = str (Id.to_string n) in
        str "pose " ++ prnt env hyp ++ str " as " ++ n ++ fin
     | Induction (env, trm, names, goals) ->
        let to_s ns = String.concat " " (List.map Id.to_string ns) in
        let bindings = str (String.concat "|" (List.map to_s names)) in
        str "induction " ++ prnt env trm ++
          str " as [" ++ bindings ++ str "].\n" ++
          seq (List.map (show_tact_list (level + 1) sigma) goals)
     | Reflexivity -> str "reflexivity" ++ fin 
     | Simpl -> str "simpl" ++ fin
     | Left -> str "left" ++ fin
     | Right -> str "right" ++ fin
     | Split (goal1, goal2) ->
        str "split.\n" ++
          show_tact_list (level + 1) sigma goal1 ++
          show_tact_list (level + 1) sigma goal2
     | Revert ns ->
        let names = String.concat " " (List.rev_map Id.to_string ns) in
        str ("revert " ^ names) ++ fin)
    
(* Represent tactics as a string. *)
let tac_to_string = show_tact_list 0 
  
