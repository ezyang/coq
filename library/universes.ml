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

(** Fresh levels *)

let new_univ_level =
  let n = ref 0 in 
    fun dp -> incr n; 
      Univ.make_universe_level (dp, !n)

let fresh_level () = new_univ_level (Global.current_dirpath ())

(* TODO: remove *)
let new_univ dp = Univ.make_universe (new_univ_level dp)
let new_Type dp = mkType (new_univ dp)
let new_Type_sort dp = Type (new_univ dp)

let fresh_universe_instance (ctx, _) =
  List.map (fun _ -> fresh_level ()) ctx

let fresh_instance_from_context (vars, cst as ctx) =
  let inst = fresh_universe_instance ctx in
  let subst = List.combine vars inst in
  let constraints = instantiate_univ_context subst ctx in
    (inst, subst), constraints

let fresh_universe_set_instance (ctx, _) =
  List.fold_left (fun s _ -> UniverseLSet.add (fresh_level ()) s) UniverseLSet.empty ctx

let fresh_instance_from (vars, cst as ctx) =
  let ctx' = fresh_universe_set_instance ctx in
  let inst = UniverseLSet.elements ctx' in
  let subst = List.combine vars inst in
  let constraints = instantiate_univ_context subst ctx in
    (inst, subst), (ctx', constraints)

(** Fresh universe polymorphic construction *)

let fresh_constant_instance env c =
  let cb = lookup_constant c env in
  let (inst,_), ctx = fresh_instance_from cb.Declarations.const_universes in
    ((c, inst), ctx)

let fresh_inductive_instance env ind = 
  let mib, mip = Inductive.lookup_mind_specif env ind in
  let (inst,_), ctx = fresh_instance_from mib.Declarations.mind_universes in
    ((ind,inst), ctx)

let fresh_constructor_instance env (ind,i) = 
  let mib, mip = Inductive.lookup_mind_specif env ind in
  let (inst,_), ctx = fresh_instance_from mib.Declarations.mind_universes in
    (((ind,i),inst), ctx)

open Globnames
let fresh_global_instance env gr =
  match gr with
  | VarRef id -> mkVar id, Univ.empty_universe_context_set
  | ConstRef sp -> 
     let c, ctx = fresh_constant_instance env sp in
       mkConstU c, ctx
  | ConstructRef sp ->
     let c, ctx = fresh_constructor_instance env sp in
       mkConstructU c, ctx
  | IndRef sp -> 
     let c, ctx = fresh_inductive_instance env sp in
       mkIndU c, ctx

open Declarations

let type_of_reference env r =
  match r with
  | VarRef id -> Environ.named_type id env, Univ.empty_universe_context_set
  | ConstRef c ->
     let cb = Environ.lookup_constant c env in
     let (inst, subst), ctx = fresh_instance_from cb.const_universes in
       subst_univs_constr subst cb.const_type, ctx
  | IndRef ind ->
     let (mib, oib) = Inductive.lookup_mind_specif env ind in
     let (inst, subst), ctx = fresh_instance_from mib.mind_universes in
       subst_univs_constr subst oib.mind_arity.mind_user_arity, ctx
  | ConstructRef cstr ->
     let (mib,oib as specif) = Inductive.lookup_mind_specif env (inductive_of_constructor cstr) in
     let (inst, subst), ctx = fresh_instance_from mib.mind_universes in
       Inductive.type_of_constructor (cstr,inst) specif, ctx

let type_of_global t = type_of_reference (Global.env ()) t

let fresh_sort_in_family env = function
  | InProp -> prop_sort, Univ.empty_universe_context_set
  | InSet -> set_sort, Univ.empty_universe_context_set
  | InType -> 
    let u = fresh_level () in
      Type (Univ.make_universe u), Univ.singleton_universe_context_set u

let new_sort_in_family sf =
  fst (fresh_sort_in_family (Global.env ()) sf)

let extend_context (a, ctx) (ctx') =
  (a, Univ.union_universe_context_set ctx ctx')

let new_global_univ () =
  let u = fresh_level () in
    (Univ.make_universe u, Univ.singleton_universe_context_set u)

(** Simplification *)

module LevelUnionFind = Unionfind.Make (Univ.UniverseLSet) (Univ.UniverseLMap)

let remove_trivial_constraints cst =
  Univ.Constraint.fold (fun (l,d,r as cstr) nontriv ->
    if d <> Univ.Lt && Univ.eq_levels l r then nontriv
    else Univ.Constraint.add cstr nontriv)
    cst Univ.empty_constraint

let normalize_context_set (ctx, csts) = 
  let module UF = LevelUnionFind in 
  let uf = UF.create () in
  let noneqs = 
    Univ.Constraint.fold (fun (l,d,r as cstr) noneq -> 
      if d = Univ.Eq then (UF.union l r uf; noneq) else 
	(Univ.Constraint.add cstr noneq)) csts Univ.empty_constraint
  in
  let partition = UF.partition uf in
  let ctx', pcanons = List.fold_left (fun (ctx, canons) s -> 
    let canon = Univ.UniverseLSet.max_elt s in
    let rest = Univ.UniverseLSet.remove canon s in
    let ctx' = Univ.UniverseLSet.diff ctx rest in
    let canons' = (canon, Univ.UniverseLSet.elements rest) :: canons in
      (ctx', canons')) 
    (ctx, []) partition
  in
  let subst = List.concat (List.rev_map (fun (c, rs) -> 
    List.rev_map (fun r -> (r, c)) rs) pcanons) in
  let constraints = remove_trivial_constraints 
    (Univ.subst_univs_constraints subst noneqs)
  in (subst, (ctx', constraints))

(* let normalize_constraints ({evars = (sigma, (us, sm))} as d) = *)
(*   let (ctx', us') = normalize_context_set us in *)
(*     {d with evars = (sigma, (us', sm))} *)
