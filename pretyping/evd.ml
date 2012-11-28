(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Errors
open Util
open Names
open Nameops
open Term
open Termops
open Environ
open Globnames
open Mod_subst

(* The kinds of existential variables are now defined in [Evar_kinds] *)

(* The type of mappings for existential variables *)

type evar = Term.existential_key

let string_of_existential evk = "?" ^ string_of_int evk
let existential_of_int evk = evk

type evar_body =
  | Evar_empty
  | Evar_defined of constr

type evar_info = {
  evar_concl : constr;
  evar_hyps : named_context_val;
  evar_body : evar_body;
  evar_filter : bool list;
  evar_source : Evar_kinds.t Loc.located;
  evar_candidates : constr list option; (* if not None, list of allowed instances *)
  evar_extra : Store.t }

let make_evar hyps ccl = {
  evar_concl = ccl;
  evar_hyps = hyps;
  evar_body = Evar_empty;
  evar_filter = List.map (fun _ -> true) (named_context_of_val hyps);
  evar_source = (Loc.ghost,Evar_kinds.InternalHole);
  evar_candidates = None;
  evar_extra = Store.empty
}

let evar_concl evi = evi.evar_concl
let evar_hyps evi = evi.evar_hyps
let evar_context evi = named_context_of_val evi.evar_hyps
let evar_body evi = evi.evar_body
let evar_filter evi = evi.evar_filter
let evar_unfiltered_env evi = Global.env_of_context evi.evar_hyps
let evar_filtered_context evi =
  snd (List.filter2 (fun b c -> b) (evar_filter evi) (evar_context evi))
let evar_env evi =
  List.fold_right push_named (evar_filtered_context evi)
    (reset_context (Global.env()))

let eq_evar_body b1 b2 = match b1, b2 with
| Evar_empty, Evar_empty -> true
| Evar_defined t1, Evar_defined t2 -> eq_constr t1 t2
| _ -> false

let eq_evar_info ei1 ei2 =
  ei1 == ei2 ||
    eq_constr ei1.evar_concl ei2.evar_concl &&
    eq_named_context_val (ei1.evar_hyps) (ei2.evar_hyps) &&
    eq_evar_body ei1.evar_body ei2.evar_body
    (** ppedrot: [eq_constr] may be a bit too permissive here *)


let map_evar_body f = function
  | Evar_empty -> Evar_empty
  | Evar_defined d -> Evar_defined (f d)

let map_evar_info f evi =
  {evi with
    evar_body = map_evar_body f evi.evar_body;
    evar_hyps = map_named_val f evi.evar_hyps;
    evar_concl = f evi.evar_concl;
    evar_candidates = Option.map (List.map f) evi.evar_candidates }

(* spiwack: Revised hierarchy :
   - ExistentialMap ( Maps of existential_keys )
   - EvarInfoMap ( .t = evar_info ExistentialMap.t * evar_info ExistentialMap )
   - EvarMap ( .t = EvarInfoMap.t * sort_constraints )
   - evar_map (exported)
*)

module ExistentialMap = Int.Map
module ExistentialSet = Int.Set

(* This exception is raised by *.existential_value *)
exception NotInstantiatedEvar

(* Note: let-in contributes to the instance *)
let make_evar_instance sign args =
  let rec instrec = function
    | (id,_,_) :: sign, c::args when isVarId id c -> instrec (sign,args)
    | (id,_,_) :: sign, c::args -> (id,c) :: instrec (sign,args)
    | [],[] -> []
    | [],_ | _,[] -> anomaly "Signature and its instance do not match"
  in
    instrec (sign,args)

let instantiate_evar sign c args =
  let inst = make_evar_instance sign args in
  match inst with
  | [] -> c
  | _ -> replace_vars inst c

module EvarInfoMap = struct
  type t = evar_info ExistentialMap.t * evar_info ExistentialMap.t

  let empty = ExistentialMap.empty, ExistentialMap.empty

  let is_empty (d,u) = ExistentialMap.is_empty d && ExistentialMap.is_empty u

  let has_undefined (_,u) = not (ExistentialMap.is_empty u)

  let to_list (def,undef) =
    (* Workaround for change in Map.fold behavior in ocaml 3.08.4 *)
    let l = ref [] in
    ExistentialMap.iter (fun evk x -> l := (evk,x)::!l) def;
    ExistentialMap.iter (fun evk x -> l := (evk,x)::!l) undef;
    !l

  let undefined_list (def,undef) =
    (* Order is important: needs ocaml >= 3.08.4 from which "fold" is a
       "fold_left" *)
    ExistentialMap.fold (fun evk evi l -> (evk,evi)::l) undef []

  let undefined_evars (def,undef) = (ExistentialMap.empty,undef)
  let defined_evars (def,undef) = (def,ExistentialMap.empty)

  let find (def, undef) k =
    try ExistentialMap.find k undef
    with Not_found -> ExistentialMap.find k def
  let find_undefined (def,undef) k = ExistentialMap.find k undef
  let remove (def,undef) k =
    (ExistentialMap.remove k def,ExistentialMap.remove k undef)
  let mem (def, undef) k =
    ExistentialMap.mem k undef || ExistentialMap.mem k def
  let fold (def,undef) f a =
    ExistentialMap.fold f def (ExistentialMap.fold f undef a)
  let fold_undefined (def,undef) f a =
    ExistentialMap.fold f undef a
  let exists_undefined (def,undef) f =
    ExistentialMap.fold (fun k v b -> b || f k v) undef false

  let add (def,undef) evk newinfo = match newinfo.evar_body with
  | Evar_empty -> (def, ExistentialMap.add evk newinfo undef)
  | _ -> (ExistentialMap.add evk newinfo def, undef)

  let add_undefined (def,undef) evk newinfo = match newinfo.evar_body with
  | Evar_empty -> (def, ExistentialMap.add evk newinfo undef)
  | _ -> assert false

  let map (def,undef) f = (ExistentialMap.map f def, ExistentialMap.map f undef)
  let map_undefined (def,undef) f = (def, ExistentialMap.map f undef)

  let define (def,undef) evk body =
    let oldinfo =
      try ExistentialMap.find evk undef
      with Not_found -> 
	try ExistentialMap.find evk def
	with Not_found -> 
	  anomaly "Evd.define: cannot define undeclared evar" in
    let newinfo =
      { oldinfo with
	  evar_body = Evar_defined body } in
      match oldinfo.evar_body with
	| Evar_empty ->
	    (ExistentialMap.add evk newinfo def,ExistentialMap.remove evk undef)
	| _ ->
	    anomaly "Evd.define: cannot define an evar twice"

  let is_evar = mem

  let is_defined (def,undef) evk = ExistentialMap.mem evk def
  let is_undefined (def,undef) evk = ExistentialMap.mem evk undef

  (*******************************************************************)
  (* Formerly Instantiate module *)

  (* Existentials. *)

  let existential_type sigma (n,args) =
    let info =
      try find sigma n
      with Not_found ->
	anomaly ("Evar "^(string_of_existential n)^" was not declared") in
    let hyps = evar_filtered_context info in
      instantiate_evar hyps info.evar_concl (Array.to_list args)

  let existential_value sigma (n,args) =
    let info = find sigma n in
    let hyps = evar_filtered_context info in
      match evar_body info with
	| Evar_defined c ->
	    instantiate_evar hyps c (Array.to_list args)
	| Evar_empty ->
	    raise NotInstantiatedEvar

  let existential_opt_value sigma ev =
    try Some (existential_value sigma ev)
    with NotInstantiatedEvar -> None

end

(* 2nd part used to check consistency on the fly. *)
type evar_universe_context = 
  { uctx_local : Univ.universe_context_set; (** The local context of variables *)
    uctx_univ_variables : Univ.universe_set; (** The local universes that are unification variables *)
    uctx_univ_algebraic : Univ.universe_set; (** The subset of unification variables that can be instantiated with 
						 algebraic universes as they appear in types only. *)
    uctx_universes :  Univ.universes; (** The current graph extended with the local constraints *)
  }
  
let empty_evar_universe_context = 
  { uctx_local = Univ.empty_universe_context_set;
    uctx_univ_variables = Univ.empty_universe_set;
    uctx_univ_algebraic = Univ.empty_universe_set;
    uctx_universes = Univ.initial_universes }

let is_empty_evar_universe_context ctx =
  Univ.is_empty_universe_context_set ctx.uctx_local

let union_evar_universe_context ctx ctx' =
  { uctx_local = Univ.union_universe_context_set ctx.uctx_local ctx'.uctx_local;
    uctx_univ_variables = 
     Univ.union_universe_set ctx.uctx_univ_variables ctx'.uctx_univ_variables;
    uctx_univ_algebraic = 
     Univ.union_universe_set ctx.uctx_univ_algebraic ctx'.uctx_univ_algebraic;
    uctx_universes = (*FIXME *) ctx.uctx_universes }

type 'a in_evar_universe_context = 'a * evar_universe_context

let evar_universe_context_set ctx = ctx.uctx_local
let evar_universe_context_of ctx = { empty_evar_universe_context with uctx_local = ctx }

module EvarMap = struct

  type t = EvarInfoMap.t * evar_universe_context
  let empty = EvarInfoMap.empty, empty_evar_universe_context
  let evar_universe_context_from e c = 
    {empty_evar_universe_context with uctx_local = c; uctx_universes = universes e}
  let from_env_and_context e c = EvarInfoMap.empty, evar_universe_context_from e c

  let is_empty (sigma, ctx) = 
    EvarInfoMap.is_empty sigma
  let is_universes_empty (sigma, ctx) =
    EvarInfoMap.is_empty sigma && is_empty_evar_universe_context ctx
  let has_undefined (sigma,_) = EvarInfoMap.has_undefined sigma
  let add (sigma,sm) k v = (EvarInfoMap.add sigma k v, sm)
  let add_undefined (sigma,sm) k v = (EvarInfoMap.add_undefined sigma k v, sm)
  let find (sigma,_) = EvarInfoMap.find sigma
  let find_undefined (sigma,_) = EvarInfoMap.find_undefined sigma
  let remove (sigma,sm) k = (EvarInfoMap.remove sigma k, sm)
  let mem (sigma,_) = EvarInfoMap.mem sigma
  let to_list (sigma,_) = EvarInfoMap.to_list sigma
  let undefined_list (sigma,_) = EvarInfoMap.undefined_list sigma
  let undefined_evars (sigma,sm) = (EvarInfoMap.undefined_evars sigma, sm)
  let defined_evars (sigma,sm) = (EvarInfoMap.defined_evars sigma, sm)
  let map f (sigma,sm) = (EvarInfoMap.map sigma f, sm)
  let map_undefined f (sigma,sm) = (EvarInfoMap.map_undefined sigma f, sm)
  let fold (sigma,_) = EvarInfoMap.fold sigma
  let fold_undefined (sigma,_) = EvarInfoMap.fold_undefined sigma
  let define (sigma,sm) k v = (EvarInfoMap.define sigma k v, sm)
  let is_evar (sigma,_) = EvarInfoMap.is_evar sigma
  let is_defined (sigma,_) = EvarInfoMap.is_defined sigma
  let is_undefined (sigma,_) = EvarInfoMap.is_undefined sigma
  let existential_value (sigma,_) = EvarInfoMap.existential_value sigma
  let existential_type (sigma,_) = EvarInfoMap.existential_type sigma
  let existential_opt_value (sigma,_) = EvarInfoMap.existential_opt_value sigma
  let progress_evar_map (sigma1,sm1 as x) (sigma2,sm2 as y) =
    not (x == y) &&
    (EvarInfoMap.exists_undefined sigma1
      (fun k v -> assert (v.evar_body == Evar_empty);
        EvarInfoMap.is_defined sigma2 k))

  let merge e e' = fold e' (fun n v sigma -> add sigma n v) e

  let add_constraints_context ctx cstrs =
    { ctx with uctx_local = Univ.add_constraints_ctx ctx.uctx_local cstrs; 
      uctx_universes = Univ.merge_constraints cstrs ctx.uctx_universes }
  let add_constraints (sigma, ctx) cstrs =
    (sigma, add_constraints_context ctx cstrs)
end

(*******************************************************************)
(* Metamaps *)

(*******************************************************************)
(*            Constraints for existential variables                *)
(*******************************************************************)

type 'a freelisted = {
  rebus : 'a;
  freemetas : Int.Set.t }

(* Collects all metavars appearing in a constr *)
let metavars_of c =
  let rec collrec acc c =
    match kind_of_term c with
      | Meta mv -> Int.Set.add mv acc
      | _         -> fold_constr collrec acc c
  in
  collrec Int.Set.empty c

let mk_freelisted c =
  { rebus = c; freemetas = metavars_of c }

let map_fl f cfl = { cfl with rebus=f cfl.rebus }

(* Status of an instance found by unification wrt to the meta it solves:
  - a supertype of the meta (e.g. the solution to ?X <= T is a supertype of ?X)
  - a subtype of the meta (e.g. the solution to T <= ?X is a supertype of ?X)
  - a term that can be eta-expanded n times while still being a solution
    (e.g. the solution [P] to [?X u v = P u v] can be eta-expanded twice)
*)

type instance_constraint = IsSuperType | IsSubType | Conv

let eq_instance_constraint c1 c2 = c1 == c2

(* Status of the unification of the type of an instance against the type of
     the meta it instantiates:
   - CoerceToType means that the unification of types has not been done
     and that a coercion can still be inserted: the meta should not be
     substituted freely (this happens for instance given via the
     "with" binding clause).
   - TypeProcessed means that the information obtainable from the
     unification of types has been extracted.
   - TypeNotProcessed means that the unification of types has not been
     done but it is known that no coercion may be inserted: the meta
     can be substituted freely.
*)

type instance_typing_status =
    CoerceToType | TypeNotProcessed | TypeProcessed

(* Status of an instance together with the status of its type unification *)

type instance_status = instance_constraint * instance_typing_status

(* Clausal environments *)

type clbinding =
  | Cltyp of Name.t * constr freelisted
  | Clval of Name.t * (constr freelisted * instance_status) * constr freelisted

let map_clb f = function
  | Cltyp (na,cfl) -> Cltyp (na,map_fl f cfl)
  | Clval (na,(cfl1,pb),cfl2) -> Clval (na,(map_fl f cfl1,pb),map_fl f cfl2)

(* name of defined is erased (but it is pretty-printed) *)
let clb_name = function
    Cltyp(na,_) -> (na,false)
  | Clval (na,_,_) -> (na,true)

(***********************)

module Metaset = Int.Set

let meta_exists p s = Metaset.fold (fun x b -> b || (p x)) s false

module Metamap = Int.Map

let metamap_to_list m =
  Metamap.fold (fun n v l -> (n,v)::l) m []

(*************************)
(* Unification state *)

type conv_pb = Reduction.conv_pb
type evar_constraint = conv_pb * Environ.env * constr * constr
type evar_map =
    { evars : EvarMap.t;
      conv_pbs : evar_constraint list;
      last_mods : ExistentialSet.t;
      metas : clbinding Metamap.t }

(*** Lifting primitive from EvarMap. ***)

(* HH: The progress tactical now uses this function. *)
let progress_evar_map d1 d2 =
  EvarMap.progress_evar_map d1.evars d2.evars

(* spiwack: tentative. It might very well not be the semantics we want
     for merging evar_map *)
let merge d1 d2 = {
  evars = EvarMap.merge d1.evars d2.evars ;
  conv_pbs = List.rev_append d1.conv_pbs d2.conv_pbs ;
  last_mods = ExistentialSet.union d1.last_mods d2.last_mods ;
  metas = Metamap.fold (fun k m r -> Metamap.add k m r) d2.metas d1.metas
}
let add d e i = { d with evars=EvarMap.add d.evars e i }
let remove d e = { d with evars=EvarMap.remove d.evars e }
let find d e = EvarMap.find d.evars e
let find_undefined d e = EvarMap.find_undefined d.evars e
let mem d e = EvarMap.mem d.evars e
(* spiwack: this function loses information from the original evar_map
   it might be an idea not to export it. *)
let to_list d = EvarMap.to_list d.evars
let undefined_list d = EvarMap.undefined_list d.evars
let undefined_evars d = { d with evars=EvarMap.undefined_evars d.evars }
let defined_evars d = { d with evars=EvarMap.defined_evars d.evars }

let map f d = { d with evars = EvarMap.map f d.evars }
let map_undefined f d = { d with evars = EvarMap.map_undefined f d.evars }

(* spiwack: not clear what folding over an evar_map, for now we shall
    simply fold over the inner evar_map. *)
let fold f d a = EvarMap.fold d.evars f a
let fold_undefined f d a = EvarMap.fold_undefined d.evars f a
let is_evar d e = EvarMap.is_evar d.evars e
let is_defined d e = EvarMap.is_defined d.evars e
let is_undefined d e = EvarMap.is_undefined d.evars e

let existential_value d e = EvarMap.existential_value d.evars e
let existential_type d e = EvarMap.existential_type d.evars e
let existential_opt_value d e = EvarMap.existential_opt_value d.evars e

let add_constraints d e = {d with evars = EvarMap.add_constraints d.evars e}

(*** /Lifting... ***)

(* evar_map are considered empty disregarding histories *)
let is_empty d =
  EvarMap.is_empty d.evars &&
  begin match d.conv_pbs with [] -> true | _ -> false end &&
  Metamap.is_empty d.metas

let subst_named_context_val s = map_named_val (subst_mps s)

let subst_evar_info s evi =
  let subst_evb = function Evar_empty -> Evar_empty
    | Evar_defined c -> Evar_defined (subst_mps s c) in
  { evi with
      evar_concl = subst_mps s evi.evar_concl;
      evar_hyps = subst_named_context_val s evi.evar_hyps;
      evar_body = subst_evb evi.evar_body }

let subst_evar_defs_light sub evd =
  assert (Univ.is_initial_universes (snd evd.evars).uctx_universes);
  assert (List.is_empty evd.conv_pbs);
  { evd with
      metas = Metamap.map (map_clb (subst_mps sub)) evd.metas;
      evars = EvarInfoMap.map (fst evd.evars) (subst_evar_info sub), (snd evd.evars)
  }

let subst_evar_map = subst_evar_defs_light

(* spiwack: deprecated *)
let create_evar_defs sigma = { sigma with
  conv_pbs=[]; last_mods=ExistentialSet.empty; metas=Metamap.empty }
(* spiwack: tentatively deprecated *)
let create_goal_evar_defs sigma = { sigma with
   (* conv_pbs=[]; last_mods=ExistentialSet.empty; metas=Metamap.empty } *)
  metas=Metamap.empty } 
let empty =  {
  evars=EvarMap.empty;
  conv_pbs=[];
  last_mods = ExistentialSet.empty;
  metas=Metamap.empty
}

let from_env ?(ctx=Univ.empty_universe_context_set) e = 
  { empty with evars = EvarMap.from_env_and_context e ctx }

let has_undefined evd =
  EvarMap.has_undefined evd.evars

let merge_universe_context ({evars = (evd, uctx)} as d) uctx' =
  {d with evars = (evd, union_evar_universe_context uctx uctx')}

let evars_reset_evd ?(with_conv_pbs=false) evd d = 
  {d with evars = (fst evd.evars, union_evar_universe_context (snd evd.evars) (snd d.evars));
  conv_pbs = if with_conv_pbs then evd.conv_pbs else d.conv_pbs }
let add_conv_pb pb d = {d with conv_pbs = pb::d.conv_pbs}
let evar_source evk d = (EvarMap.find d.evars evk).evar_source

(* define the existential of section path sp as the constr body *)
let define evk body evd =
  { evd with
    evars = EvarMap.define evd.evars evk body;
    last_mods =
        match evd.conv_pbs with
	| [] ->  evd.last_mods
        | _ -> ExistentialSet.add evk evd.last_mods }

let evar_declare hyps evk ty ?(src=(Loc.ghost,Evar_kinds.InternalHole)) ?filter ?candidates evd =
  let filter = match filter with
  | None ->
    List.map (fun _ -> true) (named_context_of_val hyps)
  | Some filter ->
    assert (Int.equal (List.length filter) (List.length (named_context_of_val hyps)));
    filter
  in
  { evd with
    evars = EvarMap.add_undefined evd.evars evk
      {evar_hyps = hyps;
       evar_concl = ty;
       evar_body = Evar_empty;
       evar_filter = filter;
       evar_source = src;
       evar_candidates = candidates;
       evar_extra = Store.empty } }

let is_defined_evar evd (evk,_) = EvarMap.is_defined evd.evars evk

(* Does k corresponds to an (un)defined existential ? *)
let is_undefined_evar evd c = match kind_of_term c with
  | Evar ev -> not (is_defined_evar evd ev)
  | _ -> false

(* extracts conversion problems that satisfy predicate p *)
(* Note: conv_pbs not satisying p are stored back in reverse order *)
let extract_conv_pbs evd p =
  let (pbs,pbs1) =
    List.fold_left
      (fun (pbs,pbs1) pb ->
    	 if p pb then
	   (pb::pbs,pbs1)
         else
	   (pbs,pb::pbs1))
      ([],[])
      evd.conv_pbs
  in
  {evd with conv_pbs = pbs1; last_mods = ExistentialSet.empty},
  pbs

let extract_changed_conv_pbs evd p =
  extract_conv_pbs evd (p evd.last_mods)

let extract_all_conv_pbs evd =
  extract_conv_pbs evd (fun _ -> true)

(* spiwack: should it be replaced by Evd.merge? *)
let evar_merge evd evars =
  { evd with evars = EvarMap.merge evd.evars evars.evars }

let evar_list evd c =
  let rec evrec acc c =
    match kind_of_term c with
    | Evar (evk, _ as ev) when mem evd evk -> ev :: acc
    | _ -> fold_constr evrec acc c in
  evrec [] c

let collect_evars c =
  let rec collrec acc c =
    match kind_of_term c with
      | Evar (evk,_) -> ExistentialSet.add evk acc
      | _       -> fold_constr collrec acc c
  in
  collrec ExistentialSet.empty c

(**********************************************************)
(* Sort variables *)

type rigid = 
  | UnivRigid
  | UnivFlexible of bool (** Is substitution by an algebraic ok? *)

let univ_rigid = UnivRigid
let univ_flexible = UnivFlexible false
let univ_flexible_alg = UnivFlexible true

let evar_universe_context {evars = (sigma, uctx)} = uctx

let get_universe_context_set ?(with_algebraic=true) ({evars = (sigma, uctx) }) = 
  if with_algebraic then uctx.uctx_local
  else 
    let (ctx, csts) = uctx.uctx_local in
    let ctx' = Univ.UniverseLSet.diff ctx uctx.uctx_univ_algebraic in
      (*FIXME check no constraint depend on algebraic universes
	we're about to remove *)
      (ctx', csts)

let universe_context ({evars = (sigma, uctx) }) =
  Univ.context_of_universe_context_set uctx.uctx_local

let merge_uctx rigid uctx ctx' =
  let uctx = 
    match rigid with
    | UnivRigid -> uctx
    | UnivFlexible b ->
    let uvars' = Univ.UniverseLSet.union uctx.uctx_univ_variables (fst ctx') in
      if b then
	{ uctx with uctx_univ_variables = uvars';
	uctx_univ_algebraic = Univ.UniverseLSet.union uctx.uctx_univ_algebraic (fst ctx') }
      else { uctx with uctx_univ_variables = uvars' }
  in
    { uctx with uctx_local = Univ.union_universe_context_set uctx.uctx_local ctx';
      uctx_universes = Univ.merge_constraints (snd ctx') uctx.uctx_universes }

let merge_context_set rigid ({evars = (sigma, uctx)} as d) ctx' = 
  {d with evars = (sigma, merge_uctx rigid uctx ctx')}

let with_context_set rigid d (a, ctx) = 
  (merge_context_set rigid d ctx, a)

let uctx_new_univ_variable rigid 
  ({ uctx_local = (vars, cst); uctx_univ_variables = uvars; uctx_univ_algebraic = avars} as uctx) =
  let u = Universes.new_univ_level (Global.current_dirpath ()) in
  let vars' = Univ.UniverseLSet.add u vars in
  let uctx' = 
    match rigid with
    | UnivRigid -> uctx
    | UnivFlexible b -> 
      let uvars' = Univ.UniverseLSet.add u uvars in
	if b then {uctx with uctx_univ_variables = uvars';
	  uctx_univ_algebraic = Univ.UniverseLSet.add u avars}
	else {uctx with uctx_univ_variables = Univ.UniverseLSet.add u uvars} in
    {uctx' with uctx_local = (vars', cst)}, u

let new_univ_variable rigid ({ evars = (sigma, uctx) } as d) =
  let uctx', u = uctx_new_univ_variable rigid uctx in
    ({d with evars = (sigma, uctx')}, Univ.Universe.make u)

let new_sort_variable rigid d =
  let (d', u) = new_univ_variable rigid d in
    (d', Type u)

let make_flexible_variable 
  ({evars=(evm,({uctx_univ_variables = uvars; uctx_univ_algebraic = avars} as ctx))} as d) b u =
  let uvars' = Univ.UniverseLSet.add u uvars in
  let avars' = if b then Univ.UniverseLSet.add u avars else avars in
    {d with evars = (evm, {ctx with uctx_univ_variables = uvars'; 
			    uctx_univ_algebraic = avars'})}



(****************************************)
(* Operations on constants              *)
(****************************************)

let fresh_sort_in_family env evd s = 
  with_context_set univ_flexible evd (Universes.fresh_sort_in_family env s)

let fresh_constant_instance env evd c = 
  with_context_set univ_flexible evd (Universes.fresh_constant_instance env c)

let fresh_inductive_instance env evd i =
  with_context_set univ_flexible evd (Universes.fresh_inductive_instance env i)

let fresh_constructor_instance env evd c =
  with_context_set univ_flexible evd (Universes.fresh_constructor_instance env c)

let fresh_global rigid env evd gr =
  with_context_set rigid evd (Universes.fresh_global_instance env gr)

let is_sort_variable {evars=(_,uctx)} s = 
  match s with 
  | Type u -> 
    (match Univ.universe_level u with
    | Some l -> 
      if Univ.UniverseLSet.mem l (fst uctx.uctx_local) then 
	Some (l, not (Univ.UniverseLSet.mem l uctx.uctx_univ_variables))
      else None
    | None -> None)
  | _ -> None

let whd_sort_variable {evars=(_,sm)} t = t

let is_eq_sort s1 s2 =
  if Int.equal (sorts_ord s1 s2) 0 then None (* FIXME *)
  else
    let u1 = univ_of_sort s1
    and u2 = univ_of_sort s2 in
      if Univ.Universe.equal u1 u2 then None
      else Some (u1, u2)

let is_univ_var_or_set u = 
  not (Option.is_empty (Univ.universe_level u))

type universe_global = 
  | LocalUniv of Univ.universe_level
  | GlobalUniv of Univ.universe_level

type universe_kind = 
  | Algebraic of Univ.universe
  | Variable of universe_global

let is_univ_level_var (us, cst) u =
  match Univ.universe_level u with
  | Some u -> Variable (if Univ.UniverseLSet.mem u us then LocalUniv u else GlobalUniv u)
  | None -> Algebraic u

let set_eq_sort ({evars = (sigma, uctx)} as d) s1 s2 =
  let us = uctx.uctx_local in
  match is_eq_sort s1 s2 with
  | None -> d
  | Some (u1, u2) ->
      match s1, s2 with
      | Prop c, Type u when Univ.universe_level u <> None ->
	  add_constraints d (Univ.enforce_eq u1 u2 Univ.empty_constraint)

      | Type u, Type v ->

        (match is_univ_level_var us u, is_univ_level_var us v with
        | Variable u, Variable v -> 

	  (match u, v with
	  | LocalUniv u, (LocalUniv v | GlobalUniv v) ->
	    add_constraints d (Univ.enforce_eq u1 u2 Univ.empty_constraint)
	  | GlobalUniv u, LocalUniv v -> 
	    add_constraints d (Univ.enforce_eq u2 u1 Univ.empty_constraint)
	    (* {d with evars = (sigma, (Univ.subst_univs_context us v u, *)
	    (* 			     Univ.enforce_eq u1 u2 sm)) } *)
	  | GlobalUniv u, GlobalUniv v -> 
	    add_constraints d (Univ.enforce_eq u1 u2 Univ.empty_constraint))

	| (Variable _, Algebraic _) | (Algebraic _, Variable _) -> 
        (* Will fail *)
	  add_constraints d (Univ.enforce_eq u1 u2 Univ.empty_constraint)

	| Algebraic _, Algebraic _ -> 
	(* Will fail *)
	  add_constraints d (Univ.enforce_eq u1 u2 Univ.empty_constraint))

      | Type u, Prop _ when Univ.universe_level u <> None -> 
        add_constraints d (Univ.enforce_eq u1 u2 Univ.empty_constraint)

      | _, _ -> raise (Univ.UniverseInconsistency (Univ.Eq, u1, u2, []))

let set_eq_level d u1 u2 =
  add_constraints d (Univ.enforce_eq_level u1 u2 Univ.empty_constraint)

let set_leq_level d u1 u2 =
  add_constraints d (Univ.enforce_leq_level u1 u2 Univ.empty_constraint)

let set_leq_sort ({evars = (sigma, uctx)} as d) s1 s2 =
  match is_eq_sort s1 s2 with
  | None -> d
  | Some (u1, u2) ->
      match s1, s2 with
      | Prop c, Prop c' -> 
	  if c = Null && c' = Pos then d
	  else (raise (Univ.UniverseInconsistency (Univ.Le, u1, u2, [])))
      | Type u, Prop c -> 
          if c = Pos then 
	    add_constraints d (Univ.enforce_leq u Univ.type0_univ Univ.empty_constraint)
	  else (* Lower u to Prop *)
	    set_eq_sort d s1 s2
      | _, Type u ->
         (match is_univ_level_var uctx.uctx_local u with
	 | Algebraic _ -> raise (Univ.UniverseInconsistency (Univ.Le, u1, u2, []))
	 | Variable (LocalUniv u | GlobalUniv u) ->
	   add_constraints d (Univ.enforce_leq u1 u2 Univ.empty_constraint))

let normalize_evar_universe_context uctx = 
  let (subst, us') = 
    Universes.normalize_context_set uctx.uctx_local uctx.uctx_univ_variables
      uctx.uctx_univ_algebraic
  in subst, us'

let nf_constraints ({evars = (sigma, uctx)} as d) = 
  let (subst, us') = normalize_evar_universe_context uctx in
  let uctx' = {uctx with uctx_local = us'; uctx_univ_variables = Univ.UniverseLSet.empty} in
  let evd' = {d with evars = (sigma, uctx')} in
    evd', subst
        	    
(* Conversion w.r.t. an evar map and its local universes. *)

let conversion env ({evars = (sigma, uctx)} as d) pb t u =
  let conv = match pb with 
    | Reduction.CONV -> Reduction.conv
    | Reduction.CUMUL -> Reduction.conv_leq
  in 
  let cst = conv ~evars:(existential_opt_value d) env t u in
  let uctx = { uctx with uctx_local = Univ.add_constraints_ctx uctx.uctx_local cst } in
    { d with evars = (sigma, uctx) }

(**********************************************************)
(* Accessing metas *)

let meta_list evd = metamap_to_list evd.metas

let find_meta evd mv = Metamap.find mv evd.metas

let undefined_metas evd =
  let filter = function
    | (n,Clval(_,_,typ)) -> None
    | (n,Cltyp (_,typ))  -> Some n
  in
  let m = List.map_filter filter (meta_list evd) in
  List.sort (-) m

let metas_of evd =
  List.map (function
    | (n,Clval(_,_,typ)) -> (n,typ.rebus)
    | (n,Cltyp (_,typ))  -> (n,typ.rebus))
    (meta_list evd)

let map_metas_fvalue f evd =
  { evd with metas =
      Metamap.map
        (function
          | Clval(id,(c,s),typ) -> Clval(id,(mk_freelisted (f c.rebus),s),typ)
          | x -> x) evd.metas }

let meta_opt_fvalue evd mv =
  match Metamap.find mv evd.metas with
    | Clval(_,b,_) -> Some b
    | Cltyp _ -> None

let meta_defined evd mv =
  match Metamap.find mv evd.metas with
    | Clval _ -> true
    | Cltyp _ -> false

let try_meta_fvalue evd mv =
  match Metamap.find mv evd.metas with
    | Clval(_,b,_) -> b
    | Cltyp _ -> raise Not_found

let meta_fvalue evd mv =
  try try_meta_fvalue evd mv
  with Not_found -> anomaly "meta_fvalue: meta has no value"

let meta_value evd mv =
  (fst (try_meta_fvalue evd mv)).rebus

let meta_ftype evd mv =
  match Metamap.find mv evd.metas with
    | Cltyp (_,b) -> b
    | Clval(_,_,b) -> b

let meta_type evd mv = (meta_ftype evd mv).rebus

let meta_declare mv v ?(name=Anonymous) evd =
  { evd with metas = Metamap.add mv (Cltyp(name,mk_freelisted v)) evd.metas }

let meta_assign mv (v,pb) evd =
  match Metamap.find mv evd.metas with
  | Cltyp(na,ty) ->
      { evd with
        metas = Metamap.add mv (Clval(na,(mk_freelisted v,pb),ty)) evd.metas }
  | _ -> anomaly "meta_assign: already defined"

let meta_reassign mv (v,pb) evd =
  match Metamap.find mv evd.metas with
  | Clval(na,_,ty) ->
      { evd with
        metas = Metamap.add mv (Clval(na,(mk_freelisted v,pb),ty)) evd.metas }
  | _ -> anomaly "meta_reassign: not yet defined"

(* If the meta is defined then forget its name *)
let meta_name evd mv =
  try fst (clb_name (Metamap.find mv evd.metas)) with Not_found -> Anonymous

let meta_with_name evd id =
  let na = Name id in
  let (mvl,mvnodef) =
    Metamap.fold
      (fun n clb (l1,l2 as l) ->
        let (na',def) = clb_name clb in
        if Name.equal na na' then if def then (n::l1,l2) else (n::l1,n::l2)
        else l)
      evd.metas ([],[]) in
  match mvnodef, mvl with
    | _,[]  ->
	errorlabstrm "Evd.meta_with_name"
          (str"No such bound variable " ++ pr_id id ++ str".")
    | ([n],_|_,[n]) ->
	n
    | _  ->
	errorlabstrm "Evd.meta_with_name"
          (str "Binder name \"" ++ pr_id id ++
           strbrk "\" occurs more than once in clause.")


let meta_merge evd1 evd2 =
  {evd2 with
    metas = List.fold_left (fun m (n,v) -> Metamap.add n v m)
      evd2.metas (metamap_to_list evd1.metas) }

type metabinding = metavariable * constr * instance_status

let retract_coercible_metas evd =
  let mc,ml =
    Metamap.fold (fun n v (mc,ml) ->
      match v with
	| Clval (na,(b,(Conv,CoerceToType as s)),typ) ->
	    (n,b.rebus,s)::mc, Metamap.add n (Cltyp (na,typ)) ml
	| v ->
	    mc, Metamap.add n v ml)
      evd.metas ([],Metamap.empty) in
  mc, { evd with metas = ml }

let subst_defined_metas bl c =
  let rec substrec c = match kind_of_term c with
    | Meta i -> substrec (List.assoc_snd_in_triple i bl)
    | _ -> map_constr substrec c
  in try Some (substrec c) with Not_found -> None

(*******************************************************************)
type open_constr = evar_map * constr

(*******************************************************************)
(* The type constructor ['a sigma] adds an evar map to an object of
  type ['a] *)
type 'a sigma = {
  it : 'a ;
  sigma : evar_map}

let sig_it x = x.it
let sig_sig x = x.sigma

(**********************************************************)
(* Failure explanation *)

type unsolvability_explanation = SeveralInstancesFound of int

(**********************************************************)
(* Pretty-printing *)

let pr_instance_status (sc,typ) =
  begin match sc with
  | IsSubType -> str " [or a subtype of it]"
  | IsSuperType -> str " [or a supertype of it]"
  | Conv -> mt ()
  end ++
  begin match typ with
  | CoerceToType -> str " [up to coercion]"
  | TypeNotProcessed -> mt ()
  | TypeProcessed -> str " [type is checked]"
  end

let pr_meta_map mmap =
  let pr_name = function
      Name id -> str"[" ++ pr_id id ++ str"]"
    | _ -> mt() in
  let pr_meta_binding = function
    | (mv,Cltyp (na,b)) ->
      	hov 0
	  (pr_meta mv ++ pr_name na ++ str " : " ++
           print_constr b.rebus ++ fnl ())
    | (mv,Clval(na,(b,s),t)) ->
      	hov 0
	  (pr_meta mv ++ pr_name na ++ str " := " ++
           print_constr b.rebus ++
	   str " : " ++ print_constr t.rebus ++
	   spc () ++ pr_instance_status s ++ fnl ())
  in
  prlist pr_meta_binding (metamap_to_list mmap)

let pr_decl ((id,b,_),ok) =
  match b with
  | None -> if ok then pr_id id else (str "{" ++ pr_id id ++ str "}")
  | Some c -> str (if ok then "(" else "{") ++ pr_id id ++ str ":=" ++
      print_constr c ++ str (if ok then ")" else "}")

let pr_evar_source = function
  | Evar_kinds.QuestionMark _ -> str "underscore"
  | Evar_kinds.CasesType -> str "pattern-matching return predicate"
  | Evar_kinds.BinderType (Name id) -> str "type of " ++ Nameops.pr_id id
  | Evar_kinds.BinderType Anonymous -> str "type of anonymous binder"
  | Evar_kinds.ImplicitArg (c,(n,ido),b) ->
      let id = Option.get ido in
      str "parameter " ++ pr_id id ++ spc () ++ str "of" ++
      spc () ++ print_constr (Universes.constr_of_global c)
  | Evar_kinds.InternalHole -> str "internal placeholder"
  | Evar_kinds.TomatchTypeParameter (ind,n) ->
      pr_nth n ++ str " argument of type " ++ print_constr (mkInd ind)
  | Evar_kinds.GoalEvar -> str "goal evar"
  | Evar_kinds.ImpossibleCase -> str "type of impossible pattern-matching clause"
  | Evar_kinds.MatchingVar _ -> str "matching variable"

let pr_evar_info evi =
  let phyps =
    try
      let decls = List.combine (evar_context evi) (evar_filter evi) in
      prlist_with_sep spc pr_decl (List.rev decls)
    with Invalid_argument _ -> str "Ill-formed filtered context" in
  let pty = print_constr evi.evar_concl in
  let pb =
    match evi.evar_body with
      | Evar_empty -> mt ()
      | Evar_defined c -> spc() ++ str"=> "  ++ print_constr c
  in
  let candidates =
    match evi.evar_body, evi.evar_candidates with
      | Evar_empty, Some l ->
           spc () ++ str "{" ++
           prlist_with_sep (fun () -> str "|") print_constr l ++ str "}"
      | _ ->
          mt ()
  in
  let src = str "(" ++ pr_evar_source (snd evi.evar_source) ++ str ")" in
  hov 2
    (str"["  ++ phyps ++ spc () ++ str"|- "  ++ pty ++ pb ++ str"]" ++
       candidates ++ spc() ++ src)

let compute_evar_dependency_graph (sigma:evar_map) =
  (* Compute the map binding ev to the evars whose body depends on ev *)
  fold (fun evk evi acc ->
    let deps =
      match evar_body evi with
      | Evar_empty -> ExistentialSet.empty
      | Evar_defined c -> collect_evars c in
    ExistentialSet.fold (fun evk' acc ->
      let tab = try ExistentialMap.find evk' acc with Not_found -> [] in
      ExistentialMap.add evk' ((evk,evi)::tab) acc) deps acc)
    sigma ExistentialMap.empty

let evar_dependency_closure n sigma =
  let graph = compute_evar_dependency_graph sigma in
  let order a b = fst a < fst b in
  let rec aux n l =
    if Int.equal n 0 then l
    else
      let l' =
        List.map_append (fun (evk,_) ->
          try ExistentialMap.find evk graph with Not_found -> []) l in
      aux (n-1) (List.uniquize (Sort.list order (l@l'))) in
  aux n (undefined_list sigma)

let pr_evar_map_t depth sigma =
  let (evars,ctx) = sigma.evars in
  let pr_evar_list l =
    h 0 (prlist_with_sep fnl
	   (fun (ev,evi) ->
	     h 0 (str(string_of_existential ev) ++
                    str"==" ++ pr_evar_info evi)) l) in
  let evs =
    if EvarInfoMap.is_empty evars then mt ()
    else
      match depth with
      | None ->
          (* Print all evars *)
          str"EVARS:"++brk(0,1)++pr_evar_list (to_list sigma)++fnl()
      | Some n ->
          (* Print all evars *)
          str"UNDEFINED EVARS"++
          (if Int.equal n 0 then mt() else str" (+level "++int n++str" closure):")++
          brk(0,1)++
          pr_evar_list (evar_dependency_closure n sigma)++fnl()
  and svs =
    if is_empty_evar_universe_context ctx then mt ()
    else
      (str"UNIVERSES:"++brk(0,1)++ h 0 (Univ.pr_universe_context_set ctx.uctx_local) ++ fnl () ++
       str"UNDEFINED UNIVERSES:"++brk(0,1)++ h 0 (Univ.pr_universe_set ctx.uctx_univ_variables))
  in evs ++ svs

let print_env_short env =
  let pr_body n = function None -> pr_name n | Some b -> str "(" ++ pr_name n ++ str " := " ++ print_constr b ++ str ")" in
  let pr_named_decl (n, b, _) = pr_body (Name n) b in
  let pr_rel_decl (n, b, _) = pr_body n b in
  let nc = List.rev (named_context env) in
  let rc = List.rev (rel_context env) in
    str "[" ++ pr_sequence pr_named_decl nc ++ str "]" ++ spc () ++
    str "[" ++ pr_sequence pr_rel_decl rc ++ str "]"

let pr_constraints pbs =
  h 0
    (prlist_with_sep fnl
       (fun (pbty,env,t1,t2) ->
	  print_env_short env ++ spc () ++ str "|-" ++ spc () ++
	    print_constr t1 ++ spc() ++
	    str (match pbty with
		 | Reduction.CONV -> "=="
		 | Reduction.CUMUL -> "<=") ++
	    spc() ++ print_constr t2) pbs)

let pr_evar_map_constraints evd =
  match evd.conv_pbs with
  | [] -> mt ()
  | _ -> pr_constraints evd.conv_pbs ++ fnl ()

let pr_evar_map allevars evd =
  let pp_evm =
    if EvarMap.is_empty evd.evars && EvarMap.is_universes_empty evd.evars then mt() else
      pr_evar_map_t allevars evd++fnl() in
  let cstrs = match evd.conv_pbs with
  | [] -> mt ()
  | _ ->
    str "CONSTRAINTS:" ++ brk(0,1) ++ pr_constraints evd.conv_pbs ++ fnl ()
  in
  let pp_met =
    if Metamap.is_empty evd.metas then mt() else
      str"METAS:"++brk(0,1)++pr_meta_map evd.metas in
  v 0 (pp_evm ++ cstrs ++ pp_met)

let pr_metaset metas =
  str "[" ++ pr_sequence pr_meta (Metaset.elements metas) ++ str "]"
