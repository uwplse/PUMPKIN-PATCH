(* --- Type definitions for extension registry --- *)

type 'a registry

exception Registry_collision

(* Create a new extension registry with an initial capacity. *)
val create : ?size:int -> unit -> 'a registry

(* Register the item under the given key, raising Registry_collision if the
 * name is already in use.
 *)
val register : 'a registry -> string -> 'a -> unit

(* Remove the key from the registration table, if present. *)
val unregister : 'a registry -> string -> unit

(* Find the item registered under the given key, raising Not_found if no
 * item is registered under that name.
 *)
val lookup : 'a registry -> string -> 'a

(* Find all items in the registry that satisfy a predicate. *)
val filter : 'a registry -> ('a -> bool) -> 'a list
