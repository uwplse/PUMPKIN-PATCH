(* Reduction *)

open Environ
open Term

type reduction_strategy = env -> types -> types

(* Remove unused hypotheses *)
val remove_unused_hypos : reduction_strategy

(* Try to reduce, but let failure be OK *)
val try_reduce : reduction_strategy

(* Reduce and also delta-reduce definitions *)
val reduce_unfold : reduction_strategy

(* Reduce and also delta-reduce definitions, weak head *)
val reduce_unfold_hd : reduction_strategy

(* Reduce before applying abstraction *)
val reduce : reduction_strategy

(* Do not reduce before applying abstraction *)
val do_not_reduce : reduction_strategy

(* Reduce candidates using a reduction strategy *)
val reduce_candidates : reduction_strategy -> env -> types list -> types list
