(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Pp
open Names
open Term
open Sign
open Environ
open Locus
open Univ

(** Universes *)
val new_univ_level : Names.dir_path -> universe_level
val new_univ : Names.dir_path -> universe
val new_Type : Names.dir_path -> types
val new_Type_sort : Names.dir_path -> sorts

val fresh_universe_instance : universe_context -> universe_list

(** Build a fresh instance for a given context, its associated substitution and 
    the instantiated constraints. *)

val fresh_instance_from_context : universe_context -> 
  (universe_list * universe_subst) constrained

val fresh_instance_from : universe_context -> 
  (universe_list * universe_subst) in_universe_context_set

val new_global_univ : unit -> universe in_universe_context_set
val new_sort_in_family : sorts_family -> sorts

val fresh_sort_in_family : env -> sorts_family -> 
  sorts in_universe_context_set
val fresh_constant_instance : env -> constant -> 
  pconstant in_universe_context_set
val fresh_inductive_instance : env -> inductive -> 
  pinductive in_universe_context_set
val fresh_constructor_instance : env -> constructor -> 
  pconstructor in_universe_context_set

val fresh_global_instance : env -> Globnames.global_reference -> 
  constr in_universe_context_set

val extend_context : 'a in_universe_context_set -> universe_context_set -> 
  'a in_universe_context_set

(** Simplification and pruning of constraints:
    
    Normalizes the context w.r.t. equality constraints, 
    choosing a canonical universe in each equivalence class and 
    transitively saturating the constraints w.r.t to it. *)

val normalize_context_set : universe_context_set -> universe_subst in_universe_context_set


(** Create a fresh global in the global environment, shouldn't be done while
    building polymorphic values as the constraints are added to the global
    environment already. *)

val constr_of_global : Globnames.global_reference -> constr

val type_of_global : Globnames.global_reference -> types in_universe_context_set
