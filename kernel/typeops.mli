(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Univ
open Term
open Environ
open Entries
open Declarations

type constrained_unsafe_judgment = unsafe_judgment * Univ.constraints

(** {6 Typing functions (not yet tagged as safe) } *)

val infer      : env -> universe_context_set -> constr       -> 
  unsafe_judgment * universe_context_set
val infer_v    : env -> universe_context_set -> constr array -> 
  unsafe_judgment array * universe_context_set
val infer_type : env -> universe_context_set -> types        -> 
  unsafe_type_judgment * universe_context_set

val infer_local_decls :
  env -> universe_context_set -> (Id.t * local_entry) list
    -> env * rel_context * universe_context_set

(** {6 Basic operations of the typing machine. } *)

(** If [j] is the judgement {% $ %}c:t{% $ %}, then [assumption_of_judgement env j]
   returns the type {% $ %}c{% $ %}, checking that {% $ %}t{% $ %} is a sort. *)

val assumption_of_judgment :  env -> unsafe_judgment -> types
val type_judgment          :  env -> unsafe_judgment -> unsafe_type_judgment

(** {6 Type of sorts. } *)
val judge_of_prop : unsafe_judgment
val judge_of_set  : unsafe_judgment
val judge_of_prop_contents  : contents -> unsafe_judgment
val judge_of_type           : universe -> unsafe_judgment

(** {6 Type of a bound variable. } *)
val judge_of_relative : env -> int -> unsafe_judgment

(** {6 Type of variables } *)
val judge_of_variable : env -> variable -> unsafe_judgment

(** {6 type of a constant } *)
val judge_of_constant : env -> constant puniverses -> constrained_unsafe_judgment

(* val judge_of_constant_knowing_parameters : *)
(*   env -> constant -> unsafe_judgment array -> unsafe_judgment *)

(** {6 Type of application. } *)
val judge_of_apply :
  env -> unsafe_judgment -> unsafe_judgment array
    -> constrained_unsafe_judgment

(** {6 Type of an abstraction. } *)
val judge_of_abstraction :
  env -> Name.t -> unsafe_type_judgment -> unsafe_judgment
    -> unsafe_judgment

(** {6 Type of a product. } *)
val judge_of_product :
  env -> Name.t -> unsafe_type_judgment -> unsafe_type_judgment
    -> unsafe_judgment

(** s Type of a let in. *)
val judge_of_letin :
  env -> Name.t -> unsafe_judgment -> unsafe_type_judgment -> unsafe_judgment
    -> unsafe_judgment

(** {6 Type of a cast. } *)
val judge_of_cast :
  env -> unsafe_judgment -> cast_kind -> unsafe_type_judgment ->
  constrained_unsafe_judgment

(** {6 Inductive types. } *)

val judge_of_inductive : env -> inductive puniverses -> constrained_unsafe_judgment

(* val judge_of_inductive_knowing_parameters : *)
(*   env -> inductive -> unsafe_judgment array -> unsafe_judgment *)

val judge_of_constructor : env -> constructor puniverses -> constrained_unsafe_judgment

(** {6 Type of Cases. } *)
val judge_of_case : env -> case_info
  -> unsafe_judgment -> unsafe_judgment -> unsafe_judgment array
    -> constrained_unsafe_judgment

(** Typecheck general fixpoint (not checking guard conditions) *)
val type_fixpoint : env -> Name.t array -> types array
    -> unsafe_judgment array -> constraints

(** Kernel safe typing but applicable to partial proofs *)
val typing : env -> universe_context_set -> constr -> 
  unsafe_judgment * universe_context_set

val type_of_constant : env -> constant puniverses -> types * constraints

