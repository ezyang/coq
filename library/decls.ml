(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** This module registers tables for some non-logical informations
     associated declarations *)

open Util
open Names
open Sign
open Decl_kinds
open Libnames

(** Datas associated to section variables and local definitions *)

type variable_data =
  Dir_path.t * bool (* opacity *) * Univ.universe_context_set * Univ.constraints * logical_kind

let vartab = ref (Id.Map.empty : variable_data Id.Map.t)

let _ = Summary.declare_summary "VARIABLE"
  { Summary.freeze_function = (fun () -> !vartab);
    Summary.unfreeze_function = (fun ft -> vartab := ft);
    Summary.init_function = (fun () -> vartab := Id.Map.empty) }

let add_variable_data id o = vartab := Id.Map.add id o !vartab

let variable_path id = let (p,_,_,_,_) = Id.Map.find id !vartab in p
let variable_opacity id = let (_,opaq,_,_,_) = Id.Map.find id !vartab in opaq
let variable_kind id = let (_,_,_,_,k) = Id.Map.find id !vartab in k
let variable_context id = let (_,_,ctx,_,_) = Id.Map.find id !vartab in ctx
let variable_constraints id = let (_,_,_,cst,_) = Id.Map.find id !vartab in cst

let variable_secpath id =
  let dir = drop_dirpath_prefix (Lib.library_dp()) (variable_path id) in
  make_qualid dir id

let variable_exists id = Id.Map.mem id !vartab

(** Datas associated to global parameters and constants *)

let csttab = ref (Cmap.empty : logical_kind Cmap.t)

let _ = Summary.declare_summary "CONSTANT"
	  { Summary.freeze_function = (fun () -> !csttab);
	    Summary.unfreeze_function = (fun ft -> csttab := ft);
	    Summary.init_function = (fun () -> csttab := Cmap.empty) }

let add_constant_kind kn k = csttab := Cmap.add kn k !csttab

let constant_kind kn = Cmap.find kn !csttab

(** Miscellaneous functions. *)

let initialize_named_context_for_proof () =
  let sign = Global.named_context () in
  List.fold_right
    (fun (id,c,t as d) signv ->
      let d = if variable_opacity id then (id,None,t) else d in
      Environ.push_named_context_val d signv) sign Environ.empty_named_context_val

let last_section_hyps dir =
  fold_named_context
    (fun (id,_,_) sec_ids ->
      try if Dir_path.equal dir (variable_path id) then id::sec_ids else sec_ids
      with Not_found -> sec_ids)
    (Environ.named_context (Global.env()))
    ~init:[]
