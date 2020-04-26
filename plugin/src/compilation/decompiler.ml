
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
open Vars

type fun_args =
  {
    (* The function term. *)
    f : types;
    (* The number of arguments it accepts. *)
    count : int;
  }

let or_introl_args : fun_args = { f = or_introl ; count = 3 }
let or_intror_args : fun_args = { f = or_intror ; count = 3 }
let conj_args : fun_args = { f = conj ; count = 4 } 
  

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
  | Induction of env * types * Id.t list list
  | Reflexivity
  | Simpl
  | Left
  | Right
  | Split

(* Return the string representation of a single tactic. *)
let show_tact sigma tac : Pp.t =
  let prnt = fun e -> Printer.pr_constr_env e sigma in
  (match tac with
   | Intro n -> str ("intro " ^ Id.to_string n)
   | Intros ns ->
      let names = String.concat " " (List.map Id.to_string ns) in
      str ("intros " ^ names)
   | Apply (env, trm) ->
      let body_s = prnt env trm in
      str "apply " ++ body_s
   | Rewrite (env, trm, left) ->
      let s = prnt env trm in
      let arrow = if left then "<- " else "" in
      str ("rewrite " ^ arrow) ++ s
   | RewriteIn (env, prf, hyp, left) ->
      let prf_s, hyp_s = prnt env prf, prnt env hyp in
      let arrow = if left then "" else "<- " in
      str ("rewrite " ^ arrow) ++ prf_s ++ str " in " ++ hyp_s
   | ApplyIn (env, prf, hyp) ->
      let prf_s, hyp_s = prnt env prf, prnt env hyp in
      str "apply " ++ prf_s ++ str " in " ++ hyp_s
   | Pose (env, hyp, n) ->
      let n = str (Id.to_string n) in
      str "pose " ++ prnt env hyp ++ str " as " ++ n
   | Induction (env, trm, names) ->
      let to_s ns = String.concat " " (List.map Id.to_string ns) in
      let bindings = str (String.concat "|" (List.map to_s names)) in
      str "induction " ++ prnt env trm ++
        str " as [" ++ bindings ++ str "]" 
   | Reflexivity -> str "reflexivity"
   | Simpl -> str "simpl"
   | Left -> str "left"
   | Right -> str "right"
   | Split -> str "split")
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

(* Converts "apply eq_refl." into "reflexivity." *)
let reflexivity : tact list -> tact list =
  List.map (fun tac ->
      match tac with
      | Apply (env, term) ->
         (match kind term with
          | App (f, args) ->
             if Array.length args == 2 && equal f eq_refl
             then Reflexivity else tac
          | _ -> tac)
      | _ -> tac)

(* Inserts "simpl." before every rewrite. *)
let rec simpl tacs : tact list =
  match tacs with
  | [] -> []
  | Rewrite (e, t, l) :: tacs' ->
     Simpl :: Rewrite (e, t, l) :: simpl tacs'
  | tac :: tacs' -> tac :: simpl tacs'
  
(* Return a name-type pair from the given rel_declaration. *)
let rel_name_type rel : Name.t * types =
  match rel with
  | CRD.LocalAssum (n, t) -> (n, t)
  | CRD.LocalDef (n, _, t) -> (n, t)

(* Unwrap a Name.t expecting an Id.t. Fails if anonymous. *)
let expect_name (n : Name.t) : Id.t =
  match n with
  | Anonymous ->
     failwith "Unexpected Anonymous Name.t."
  | Name n -> n
            
(* Finds all rel names pushed onto an environment. *)
let get_pushed_names env : Id.Set.t =
  let names = List.map (fun x -> fst (rel_name_type x))
                (lookup_all_rels env) in
  Id.Set.of_list (List.map expect_name names)

(* If the given name is anonymous, generate a fresh one. *)
let fresh_name env n =
  let in_env = get_pushed_names env in
  let name = match n with
    | Anonymous -> Id.of_string "H"
    | Name n -> n in
  fresh_id_in_env in_env name env
           
(* Zoom all the way into a lambda term collecting names. *)
let rec zoom_lambda_names env trm : env * types * Id.t list =
  match kind trm with
  | Lambda (n, t, b) ->
     let name = fresh_name env n in
     let env, trm, names =
       zoom_lambda_names (push_local (Name name, t) env) b in
     (env, trm, name :: names)
  | _ ->
     (env, trm, [])   
  
(* Checks if we are applying function g, which
   is expected to have len arguments. *)
let try_fun f args (expect : fun_args) : (constr array) option =
  if Array.length args == expect.count && equal f expect.f then
    Some args
  else
    None
  
(* A proper rewrite must have 6 arguments and be one of the
   common eliminators for equality generated by coq. *)
let try_rewrite f args : (bool * constr * constr) option =
  if Array.length args == 6 && is_rewrite f then
    let left = is_rewrite_l f in
    let prf = Array.get args 5 in
    let hyp = Array.get args 3 in
    Some (left, prf, hyp)
  else
    None

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
  try_rewrite f args >>= fun (left, prf, hyp) ->
  Some (Rewrite (env, prf, left) :: first_pass env sigma hyp)

(* Applying an eliminator for induction on a hypothesis in context. *)
and induction (f, args) (env, sigma) : tact list option =
  guard (is_elim env f) >>= fun _ ->
  guard (not (is_rewrite f)) >>= fun _ ->
  let app = mkApp (f, args) in
  let sigma, ind = deconstruct_eliminator env sigma app in
  let ind_args = ind.final_args in
  (* Supports only 1 argument at the moment. *)
  guard (List.length ind_args == 1) >>= fun _ ->
  let ind_var = List.hd ind_args in
  try_rel ind_var >>= fun _ ->
  let zooms = List.map (zoom_lambda_names env) ind.cs in
  let names = List.map (fun (_, _, names) -> names) zooms in
  let cases = List.map (fun (env, trm, _) ->
                  simpl (first_pass env sigma trm)) zooms in
  Some (Induction (env, ind_var, names) :: List.flatten cases)

(* Choose left proof to construct or. *)
and left (f, args) (env, sigma) : tact list option =
  try_fun f args or_introl_args >>= fun args ->
  Some (Left :: first_pass env sigma (Array.get args 2))

(* Choose right proof to construct or. *)
and right (f, args) (env, sigma) : tact list option =
  try_fun f args or_intror_args >>= fun args ->
  Some (Right :: first_pass env sigma (Array.get args 2))

(* Branch two goals as arguments to conj. *)
and split (f, args) (env, sigma) : tact list option =
  try_fun f args conj_args >>= fun args ->
  let lhs = first_pass env sigma (Array.get args 2) in
  let rhs = first_pass env sigma (Array.get args 3) in
  Some (Split :: (lhs @ rhs))

(* Value must be a rewrite on a hypothesis in context. *)
and rewrite_in (_, valu, _, body) (env, sigma) : tact list option =
  let valu = Reduction.whd_betaiota env valu in
  try_app valu          >>= fun (f, args) ->
  try_rewrite f args    >>= fun (left, prf, hyp) ->
  try_rel hyp           >>= fun idx ->
  guard (noccurn (idx + 1) body) >>= fun _ ->
  let n, t = rel_name_type (lookup_rel idx env) in
  let env' = push_local (n, t) env in
  Some (RewriteIn (env, prf, hyp, left) :: first_pass env' sigma body)

(* Value must be an application with last argument in context. *)
and apply_in (_, valu, _, body) (env, sigma) : tact list option =
  let valu = Reduction.whd_betaiota env valu in
  try_app valu >>= fun (f, args) ->
  let len = Array.length args in
  let hyp = args.(len - 1) in
  try_rel hyp >>= fun idx ->
  guard (noccurn (idx + 1) body) >>= fun _ ->
  let n, t = rel_name_type (lookup_rel idx env) in
  let env' = push_local (n, t) env in
  let prf = mkApp (f, Array.sub args 0 (len - 1)) in
  Some (ApplyIn (env, prf, hyp) :: first_pass env' sigma body)

(* Last resort decompile let-in as a pose.  *)
and pose (n, valu, t, body) (env, sigma) : tact list option =
  match n with
  | Anonymous -> failwith "Unexpected anonymous in pose."
  | Name n' ->
     let env' = push_let_in (n, valu, t) env in
     Some (Pose (env, valu, n') :: first_pass env' sigma body)
       
(* Decompile a term into its equivalent tactic list. *)
let tac_from_term env sigma trm : tact list =
  (* Perform second pass to revise greedy tactic list. *)
  reflexivity (collapse_intros (first_pass env sigma trm))
  
(* Convert a tactic list into its string representation. *)
let tac_to_string sigma (tacs : tact list) : Pp.t =
  seq (List.map (show_tact sigma) tacs)
    
    
