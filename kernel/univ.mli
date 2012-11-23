(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Universes. *)

module UniverseLevel :
sig
  type t
  (** Type of universe levels. A universe level is essentially a unique name
      that will be associated to constraints later on. *)

  val compare : t -> t -> int
  (** Comparison function *)

  val equal : t -> t -> bool
  (** Equality function *)

  val make : Names.Dir_path.t -> int -> t
  (** Create a new universe level from a unique identifier and an associated
      module path. *)

end

type universe_level = UniverseLevel.t
(** Alias name. *)

type universe_list = universe_level list

module Universe :
sig
  type t = 
    | Atom of universe_level
    | Max of universe_list * universe_list
  (** Type of universes. A universe is defined as a set of constraints w.r.t.
      other universes. *)

  val compare : t -> t -> int
  (** Comparison function *)

  val equal : t -> t -> bool
  (** Equality function *)

  val make : UniverseLevel.t -> t
  (** Create a constraint-free universe out of a given level. *)

end

type universe = Universe.t
(** Alias name. *)

module UniverseLSet : Set.S with type elt = universe_level
module UniverseLMap : Map.S with type key = universe_level

val empty_universe_list : universe_list

type universe_set = UniverseLSet.t
val empty_universe_set : universe_set

type 'a puniverses = 'a * universe_list
val out_punivs : 'a puniverses -> 'a

(** The universes hierarchy: Type 0- = Prop <= Type 0 = Set <= Type 1 <= ... 
   Typing of universes: Type 0-, Type 0 : Type 1; Type i : Type (i+1) if i>0 *)

val type0m_univ : universe  (** image of Prop in the universes hierarchy *)
val type0_univ : universe  (** image of Set in the universes hierarchy *)
val type1_univ : universe  (** the universe of the type of Prop/Set *)

val is_type0_univ : universe -> bool
val is_type0m_univ : universe -> bool
val is_univ_variable : universe -> bool

val universe_level : universe -> universe_level option
val compare_levels : universe_level -> universe_level -> int
val eq_levels : universe_level -> universe_level -> bool

(** Equality of formal universe expressions. *)
val equal_universes : universe -> universe -> bool

(** The type of a universe *)
val super : universe -> universe

(** The max of 2 universes *)
val sup   : universe -> universe -> universe

(** {6 Graphs of universes. } *)

type universes

type check_function = universes -> universe -> universe -> bool
val check_leq : check_function
val check_eq : check_function

(** The empty graph of universes *)
val initial_universes : universes
val is_initial_universes : universes -> bool

(** {6 Constraints. } *)

type constraint_type = Lt | Le | Eq
type univ_constraint = universe_level * constraint_type * universe_level

module Constraint : Set.S with type elt = univ_constraint

type constraints = Constraint.t

(** A value with universe constraints. *)
type 'a constrained = 'a * constraints

(** A list of universes with universe constraints,
    representiong local universe variables and constraints *)
type universe_context = universe_list constrained

(** A set of universes with universe constraints.
    We linearize the set to a list after typechecking. 
    Beware, representation could change.
*)
type universe_context_set = universe_set constrained

(** A value in a universe context (resp. context set). *)
type 'a in_universe_context = 'a * universe_context
type 'a in_universe_context_set = 'a * universe_context_set

(** A universe substitution, note that no algebraic universes are
    involved *)
type universe_subst = (universe_level * universe_level) list

(** A full substitution might involve algebraic universes *)
type universe_full_subst = (universe_level * universe) list

(** Constraints *)
val empty_constraint : constraints
val is_empty_constraint : constraints -> bool
val union_constraints : constraints -> constraints -> constraints

(** Constrained *)
val constraints_of : 'a constrained -> constraints

val universe_set_of_list : universe_list -> universe_set

(** Universe contexts (as lists) *)
val empty_universe_context : universe_context
val is_empty_universe_context : universe_context -> bool

(** Universe contexts (as sets) *)
val empty_universe_context_set : universe_context_set
val singleton_universe_context_set : universe_level -> universe_context_set
val universe_context_set_of_list : universe_list -> universe_context_set

val is_empty_universe_context_set : universe_context_set -> bool
val union_universe_context_set : universe_context_set -> universe_context_set -> 
  universe_context_set
val add_constraints_ctx : universe_context_set -> constraints -> universe_context_set

val add_universes_ctx : universe_list -> universe_context_set -> universe_context_set

(** [check_context_subset s s'] checks that [s] is implied by [s'] as a set of constraints,
    and shrinks [s'] to the set of variables declared in [s].
. *)
val check_context_subset : universe_context_set -> universe_context -> universe_context

(** Arbitrary choice of linear order of the variables 
    and normalization of the constraints *)
val context_of_universe_context_set : universe_context_set -> universe_context

(** Make a universe level substitution: the list must match the context variables. *)
val make_universe_subst : universe_list -> universe_context -> universe_subst

(** Get the instantiated graph. *)
val instantiate_univ_context : universe_subst -> universe_context -> constraints

(** Substitution of universes. *)
val subst_univs_level : universe_subst -> universe_level -> universe_level
val subst_univs_universe : universe_subst -> universe -> universe
val subst_univs_constraints : universe_subst -> constraints -> constraints
val subst_univs_context : universe_context_set -> universe_level -> universe_level -> 
  universe_context_set

val subst_univs_full_level : universe_full_subst -> universe_level -> universe

(** Fails with an anomaly if the substitution builds an algebraic universe. *)
val subst_univs_full_level_fail : universe_full_subst -> universe_level -> universe_level

val subst_univs_full_universe : universe_full_subst -> universe -> universe

(** Raises universe inconsistency if not compatible. *)
val check_consistent_constraints : universe_context_set -> constraints -> unit

type constraint_function = universe -> universe -> constraints -> constraints

val enforce_leq : constraint_function
val enforce_eq : constraint_function
val enforce_eq_level : universe_level -> universe_level -> constraints -> constraints
val enforce_leq_level : universe_level -> universe_level -> constraints -> constraints

(** {6 ... } *)
(** Merge of constraints in a universes graph.
  The function [merge_constraints] merges a set of constraints in a given
  universes graph. It raises the exception [UniverseInconsistency] if the
  constraints are not satisfiable. *)

(** Type explanation is used to decorate error messages to provide
  useful explanation why a given constraint is rejected. It is composed
  of a path of universes and relation kinds [(r1,u1);..;(rn,un)] means
   .. <(r1) u1 <(r2) ... <(rn) un (where <(ri) is the relation symbol
  denoted by ri, currently only < and <=). The lowest end of the chain
  is supposed known (see UniverseInconsistency exn). The upper end may
  differ from the second univ of UniverseInconsistency because all
  universes in the path are canonical. Note that each step does not
  necessarily correspond to an actual constraint, but reflect how the
  system stores the graph and may result from combination of several
  constraints...
*)
type explanation = (constraint_type * universe) list

exception UniverseInconsistency of
    constraint_type * universe * universe * explanation

val merge_constraints : constraints -> universes -> universes
val normalize_universes : universes -> universes
val sort_universes : universes -> universes

(** {6 Support for sort-polymorphism } *)

val solve_constraints_system : universe option array -> universe array ->
  universe array

val subst_large_constraint : universe -> universe -> universe -> universe

val subst_large_constraints :
  (universe * universe) list -> universe -> universe

val no_upper_constraints : universe -> constraints -> bool

(** Is u mentionned in v (or equals to v) ? *)

val univ_depends : universe -> universe -> bool

(** {6 Pretty-printing of universes. } *)

val pr_uni_level : universe_level -> Pp.std_ppcmds
val pr_uni : universe -> Pp.std_ppcmds
val pr_universes : universes -> Pp.std_ppcmds
val pr_constraints : constraints -> Pp.std_ppcmds
val pr_universe_list : universe_list -> Pp.std_ppcmds
val pr_universe_set : universe_set -> Pp.std_ppcmds
val pr_universe_context : universe_context -> Pp.std_ppcmds
val pr_universe_context_set : universe_context_set -> Pp.std_ppcmds

(** {6 Dumping to a file } *)

val dump_universes :
  (constraint_type -> string -> string -> unit) ->
  universes -> unit

(** {6 Hash-consing } *)

val hcons_univlevel : universe_level -> universe_level
val hcons_univ : universe -> universe
val hcons_constraints : constraints -> constraints
val hcons_universe_set : universe_set -> universe_set
val hcons_universe_context : universe_context -> universe_context
val hcons_universe_context_set : universe_context_set -> universe_context_set 

(******)
