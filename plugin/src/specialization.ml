(* --- Specialization Component --- *)

open Term
open Environ
open Coqterms

(* Specialize an applied function by its arguments *)
let rec specialize_application (env : env) (t : types) : types =
  match kind_of_term t with
  | Lambda (n, t, b) ->
     mkLambda (n, t, specialize_application (push_rel (n, None, t) env) b)
  | App (f, args) ->
     let f_body = unwrap_definition env f in
     Reduction.nf_betaiota env (mkApp (f_body, args))
  | _ ->
     failwith "Term should be of the form (fun args => f args)"
