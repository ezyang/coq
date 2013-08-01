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
val to_string : env -> evar_map -> constr -> string
val to_ascii : env -> evar_map -> constr -> string
val run' : ?reentrant:bool -> (env * evar_map * int list ref list) -> constr -> data
val runmatch' : ?reentrant:bool -> int ->
           Environ.env * Evd.evar_map ->
           Term.constr -> Term.types -> Term.constr -> Evd.evar_map * Term.constr
