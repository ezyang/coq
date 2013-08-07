open Term
open Evd
open Environ

type data = Val of (evar_map * constr) | Err of constr

val mkT : unit -> Term.constr

val run : (env * evar_map) -> constr -> data

val pretype_run : 
  (Evarutil.type_constraint -> Environ.env -> Evd.evar_map ref -> 'a -> 'b -> Environ.unsafe_judgment) ->
  (Loc.t -> Environ.env -> Evd.evar_map ref -> Environ.unsafe_judgment ->
   Term.types option -> Environ.unsafe_judgment) ->
  Term.types option ->
  Environ.env -> Evd.evar_map ref -> 'a -> Loc.t -> 'b -> Environ.unsafe_judgment


(* debug *)
val run' : (env * evar_map * int list ref list) -> constr -> data
val runmatch' :
  Environ.env * Evd.evar_map ->
  Term.constr -> Term.types -> Term.constr ->  int -> Evd.evar_map * Term.constr
