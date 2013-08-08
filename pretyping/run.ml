open List
open String

open Term
open Termops
open Reductionops
open Environ
open Evarutil
open Evd
open Names
open Closure
open Util
open Evarconv
open Libnames
(* open Vars *)


module Constr = struct
  let mkConstr name = lazy (Universes.constr_of_global (Nametab.global_of_path (path_of_string name)))

  let isConstr = fun r c -> 
    let l = Lazy.force r in
    if isConstruct l && isConstruct c then
      let ((m1, i1), _) = destConstruct l in
      let ((m2, i2), _) = destConstruct c in
      eq_ind m1 m2 && i1 = i2
    else
      false
end


module MtacNames = struct
  let mtacore_name = "Mtac.mtacore"
  let mtac_module_name = mtacore_name ^ ".Mtac"
  let mkLazyConstr = fun e-> Constr.mkConstr (mtac_module_name ^ "." ^ e)
  let mkConstr = fun e-> Lazy.force (Constr.mkConstr (mtac_module_name ^ "." ^ e))
  let mkT_lazy = lazy (mkConstr "Mtac")

  let mkBase = mkLazyConstr "base"
  let mkTele = mkLazyConstr "tele"

  let isBase = Constr.isConstr mkBase
  let isTele = Constr.isConstr mkTele

end

module Exceptions = struct

  let mkInternalException = fun e -> mkApp (
    MtacNames.mkConstr "InternalException", [|MtacNames.mkConstr e|])

  let mkNullPointer = lazy (mkInternalException  "NullPointer")
  let mkTermNotGround = lazy (mkInternalException  "TermNotGround")

  (* HACK: we put Prop as the type of the raise. We can put an evar, but
     what's the point anyway? *)
  let mkRaise e = mkApp(MtacNames.mkConstr "raise", [|mkProp; Lazy.force e|]) 

  let error_stuck = "Cannot reduce term, perhaps an opaque definition?"
  let error_param = "Parameter appears in returned value"
  let error_no_match = "No pattern matches"
  let error_abs = "Cannot abstract non variable"
  let unknown_reduction_strategy = "Unknown reduction strategy"

  let raise = Errors.error
end

module ReductionStrategy = struct

  let mkRed = fun s -> lazy (MtacNames.mkConstr s)
  let redNone = mkRed "RedNone"
  let redSimpl = mkRed "RedSimpl"
  let redWhd = mkRed "RedWhd"

  let test = fun r c -> eq_constr (Lazy.force r) c
  let isRedNone = test redNone
  let isRedSimpl = test redSimpl
  let isRedWhd = test redWhd

  let reduce sigma env strategy c =
    if isRedNone strategy then
      c
    else if isRedSimpl strategy then
      Tacred.simpl env sigma c
    else if isRedWhd strategy then
      whd_betadeltaiota env sigma c
    else
      Exceptions.raise Exceptions.unknown_reduction_strategy 

end

module UnificationStrategy = struct

  let mkUni = fun s -> lazy (MtacNames.mkConstr s)
  let uniRed = mkUni "UniRed"
  let uniSimpl = mkUni "UniSimpl"

  let test = fun r c -> eq_constr (Lazy.force r) c
  let isUniRed = test uniRed
  let isUniSimpl = test uniSimpl

  let find_pbs sigma evars =
    let (_, pbs) = extract_all_conv_pbs sigma in
    List.filter (fun (_,_,c1,c2) -> 
      List.exists (fun e -> 
	Termops.occur_term e c1 || Termops.occur_term e c2) evars) pbs

  let unify rsigma env evars strategy t1 t2 =
    if isUniRed strategy then
      try
        let sigma = the_conv_x (* ~eta:false *) env t2 t1 !rsigma in
	rsigma := consider_remaining_unif_problems env sigma;
        List.length (find_pbs !rsigma evars) = 0
      with _ -> false
    else if isUniSimpl strategy then
      match Simpleunify.unify env !rsigma t2 t1 with
	| Evarsolve.Success sigma ->
	  rsigma := sigma;
	  List.length (find_pbs sigma evars) = 0
	| _ -> false
    else
      Exceptions.raise Exceptions.unknown_reduction_strategy 

end

let mkT () = Lazy.force MtacNames.mkT_lazy

module CoqList = struct
  let mkNil  = Constr.mkConstr "Coq.Init.Datatypes.nil"
  let mkCons = Constr.mkConstr "Coq.Init.Datatypes.cons"

  let isNil  = Constr.isConstr mkNil
  let isCons = Constr.isConstr mkCons
end

module CoqEq = struct
  let mkEq = Constr.mkConstr "Coq.Init.Logic.eq"
  let mkEqRefl = Constr.mkConstr "Coq.Init.Logic.eq_refl"

  let mkAppEq a x y = mkApp(Lazy.force mkEq, [|a;x;y|])
  let mkAppEqRefl a x = mkApp(Lazy.force mkEqRefl, [|a;x|])
end

module CoqSigT = struct
  let mkExistT  = Constr.mkConstr "Coq.Init.Specif.existT"

  let mkAppExistT a p x px =
    mkApp (Lazy.force mkExistT, [|a; p; x; px|])
end

module CoqNat = struct
  let mkZero = Constr.mkConstr "Coq.Init.Datatypes.O"
  let mkSucc = Constr.mkConstr "Coq.Init.Datatypes.S"

  let isZero = Constr.isConstr mkZero
  let isSucc = Constr.isConstr mkSucc

  let rec to_coq = function
    | 0 -> Lazy.force mkZero
    | n -> Term.mkApp (Lazy.force mkSucc, [| to_coq (pred n) |])

  let from_coq env evd c =
    let rec fc c = 
      if isZero c then
        0
      else 
        let (s, n) = destApp c in
        begin
          if isSucc s then
            1 + (fc (n.(0)))
          else
	    Errors.error "Not a nat"
        end
    in
    let c' = Tacred.cbv_betadeltaiota env evd c in
    fc c'
     
end

module CoqPositive = struct
  let xI = Constr.mkConstr "Coq.Numbers.BinNums.xI"
  let xO = Constr.mkConstr "Coq.Numbers.BinNums.xO"
  let xH = Constr.mkConstr "Coq.Numbers.BinNums.xH"

  let isH = Constr.isConstr xH
  let isI = Constr.isConstr xI
  let isO = Constr.isConstr xO
  
  let from_coq env evd c =
    let rec fc i c =
      if isH c then
        1
      else 
        let (s, n) = destApp c in
        begin
          if isI s then
            (fc (i+1) (n.(0)))*2 + 1
          else if isO s then
            (fc (i+1) (n.(0)))*2
          else
	    Errors.error "Not a positive"
        end
    in
    let c' = Tacred.cbv_betadeltaiota env evd c in
    fc 0 c'

  let rec to_coq n =
    if n = 1 then
      Lazy.force xH
    else if n mod 2 = 0 then
      mkApp(Lazy.force xO, [|to_coq (n / 2)|])
    else
      mkApp(Lazy.force xI, [|to_coq ((n-1)/2)|])

end

module CoqN = struct
  let tN = Constr.mkConstr "Coq.Numbers.BinNums.N"
  let h0 = Constr.mkConstr "Coq.Numbers.BinNums.N0"
  let hP = Constr.mkConstr "Coq.Numbers.BinNums.Npos"

  let is0 = Constr.isConstr h0
  let isP = Constr.isConstr hP

  let from_coq env evd c =
    let rec fc c = 
      if is0 c then
        0
      else 
        let (s, n) = destApp c in
        begin
          if isP s then
            CoqPositive.from_coq env evd (n.(0))
          else
	    Errors.error "Not a positive"
        end
    in
    let c' = Tacred.cbv_betadeltaiota env evd c in
    fc c'

  let to_coq n =
    if n = 0 then
      Lazy.force h0
    else
      mkApp(Lazy.force hP, [|CoqPositive.to_coq n|])
end

module CoqBool = struct

  let mkTrue = Constr.mkConstr "Coq.Init.Datatypes.true"
  let mkFalse = Constr.mkConstr "Coq.Init.Datatypes.false"

  let isTrue = Constr.isConstr mkTrue

end 

module CoqAscii = struct

  let from_coq env sigma c =
    let (h, args) = whd_betadeltaiota_stack env sigma c in
    let rec from_bits n bits =
      match bits with
        | [] -> 0
        | (b :: bs) -> (if CoqBool.isTrue b then 1 else 0) lsl n + from_bits (n+1) bs
    in 
    let n = from_bits 0 args in
    Char.escaped (Char.chr n)

end 

module CoqString = struct

  let mkEmpty = Constr.mkConstr "Coq.Strings.String.EmptyString"
  let mkString = Constr.mkConstr "Coq.Strings.String.String"

  let isEmpty = Constr.isConstr mkEmpty
  let isString = Constr.isConstr mkString

  let rec from_coq env sigma s =
    let (h, args) = whd_betadeltaiota_stack env sigma s in
    if isEmpty h then
      ""
    else if isString h then
      let c, s' = List.nth args 0, List.nth args 1 in
      CoqAscii.from_coq env sigma c ^ from_coq env sigma s'
    else
      Errors.error "Not a string"

end

module CoqUnit = struct
  let mkTT = Constr.mkConstr "Coq.Init.Datatypes.tt"
end




module type RefConstructors = 
  sig
    val mkRef : constr lazy_t
  end

module RefFactory = functor (Ref : RefConstructors) ->
struct
  let isRef =  Constr.isConstr Ref.mkRef

  let to_coq a n = 
    Term.mkApp (Lazy.force Ref.mkRef, [|a ; CoqN.to_coq n|])

  let from_coq env evd c =
    let c = Tacred.cbv_betadeltaiota env evd c in
    if isApp c && isRef (fst (destApp c)) then
      CoqN.from_coq env evd (snd (destApp c)).(1)
    else
      Errors.error "Not a reference"

end

module ForgetRef : RefConstructors = struct
  let mkRef= Constr.mkConstr (MtacNames.mtac_module_name ^ ".mkRef")
end

module ForgetRefFactory = RefFactory(ForgetRef)

(** An array that grows 1.5 times when it gets out of space *) 
module GrowingArray = struct
  type 'a t = 'a array ref * 'a * int ref
  
  let make i t = (ref (Array.make i t), t, ref 0)
  let length g = let (_, _, i) = g in !i
  let get g = let (a, _, _) = g in Array.get !a
  let set g = let (a, _, _) = g in Array.set !a

  let add g t =
    let (a, e, i) = g in
    begin
    if Array.length !a <= !i then
      a := Array.append !a (Array.make (Array.length !a / 2) e)
    else
      ()
    end;
    Array.set !a !i t;
    i := !i+1
 
end

module Refs = struct
  let bag = ref (GrowingArray.make 4 None)

  let clean () = 
    bag := GrowingArray.make 4 None

  let length () =
    GrowingArray.length !bag

  let check_context undo index c =
    let size = List.length undo in
    let rec check depth t =
      match kind_of_term t with
      | Rel k ->
        if depth < k && k <= depth + size then
          let rl = List.nth undo (k - depth -1) in
          rl := (index :: !rl)
        else
          ()
      | _ -> iter_constr_with_binders succ check depth t
    in
    check 0 c

  let new_ref undo a c =
    let level = List.length undo in
    GrowingArray.add !bag (Some (c, level));
    let index = pred (GrowingArray.length !bag) in
    check_context undo index c;
    ForgetRefFactory.to_coq a index

  exception NullPointerException

  let get env evd undo i = 
    let level = List.length undo in
    let index = ForgetRefFactory.from_coq env evd i in
    let v = GrowingArray.get !bag index in
    match v with
      None -> raise NullPointerException
    | Some (c, l) -> (lift (level - l) c)

  (* HACK SLOW *)
  let remove_all undo index =
    List.iter (fun rl ->
      rl := List.filter (fun i -> i <> index) !rl) undo

  let set env evd undo i c = 
    let level = List.length undo in
    let index = ForgetRefFactory.from_coq env evd i in
    remove_all undo index;
    check_context undo index c;
    GrowingArray.set !bag index (Some (c, level))

  let invalidate index =
    GrowingArray.set !bag index None
    
end


type data = Val of (evar_map * constr) | Err of constr

let (>>=) v g =
  match v with
    | Val v' -> g v'
    | _ -> v

let return s t = Val (s, t)

let fail t = Err t
(*
let uflags =
  { Unification.default_unify_flags with
    Unification.modulo_eta = false }
*)
let rec open_pattern (env, sigma) p evars =
  let (patt, args) = whd_betadeltaiota_stack env sigma p in
  let length = List.length args in
  let nth = List.nth args in
  if MtacNames.isBase patt && length = 6 then
    let p = nth 3 in
    let b = nth 4 in
    let strategy = nth 5 in
    Some (sigma, evars, p, b, strategy)
  else if MtacNames.isTele patt && length = 5 then
    let c = nth 2 in
    let f = nth 4 in
    let (sigma', evar) = Evarutil.new_evar sigma env (* empty_env *) c in
(*    let evar = Evarutil.new_meta () in
    let sigma' = Evd.meta_declare evar c sigma in *)
    open_pattern (env, sigma') (mkApp (f, [|evar|])) (evar :: evars)
  else
    None



let rec runmatch' (env, sigma as ctxt) t ty patts' i =
  let (patts, args) = whd_betadeltaiota_stack env sigma patts' in
  if CoqList.isNil patts && List.length args = 1 then
    Exceptions.raise Exceptions.error_no_match
  else if CoqList.isCons patts && List.length args = 3 then
    match open_pattern ctxt (List.nth args 1) [] with
        Some (sigma', evars, p, body, strategy) ->
          let rsigma' = ref sigma' in
	  let devars = destEvars evars in
          begin
            if unify env rsigma' evars strategy p t && all_defined rsigma' devars then
              let body = nf_evar !rsigma' body in
              let () = remove_all rsigma' devars in
	      let body' = mkApp(body, [|CoqEq.mkAppEqRefl ty t|]) in
              (!rsigma', body')
            else
              runmatch' ctxt t ty (List.nth args 2) (i+1)
          end
      | None -> Exceptions.raise Exceptions.error_stuck
  else
    Exceptions.raise Exceptions.error_stuck

and destEvars =
  (* fun l -> l *)
  List.map (fun e-> let ev, _ = destEvar e in ev)

and all_defined rsigma =
  (* List.fold_left (fun b e -> b && Evd.meta_defined !rsigma e) true *)
  (*
  List.fold_left (fun b e -> b && Evd.is_defined !rsigma e) true
  *)
  (fun _->true)

and remove_all rsigma =
  fun l -> ()
  (* List.iter (fun e -> rsigma := Evd.remove !rsigma e) *)

and unify env rsigma evars strategy t1 t2 =
  UnificationStrategy.unify rsigma env evars strategy t1 t2


let runmatch (env, sigma as ctxt) t ty patts = 
  runmatch' ctxt t ty patts 0


let print env sigma s = Printf.printf "[DEBUG] %s\n" (CoqString.from_coq env sigma s)

let mysubstn t n c =
  let rec substrec depth c = match kind_of_term c with
    | Rel k     ->
        if k<=depth then c
        else if k = depth+n then lift depth t
        else mkRel (k+1)
    | _ -> map_constr_with_binders succ substrec depth c in
  substrec 0 c

(* solves typeclasses instances appearing in t *)
(* NOT WORKING!
let solve_instances_for env evd t =
  let revd = ref evd in
  let rec f depth c = 
    let c = whd_evar !revd c in
    match kind_of_term c with
    | Evar e     ->
      let ty = Evd.existential_type !revd e in
      let (evd', _) = Typeclasses.resolve_one_typeclass env !revd ty in
      revd := evd'
    | _ -> iter_constr_with_binders succ f depth c in
  f 0 t;
  !revd
*)


let rec run' (env, sigma, undo as ctxt) t =
  let t = whd_betadeltaiota env sigma t in
  let (h, args) = decompose_app t in
  let nth = List.nth args in
  let assert_args n = 
    if List.length args = n then
      ()
    else
      Errors.error "The number of arguments for the constructor is wrong"
  in
  let constr c = 
    if isConstruct c then
      let ((m, ix), _) = destConstruct h in
      if eq_ind m (fst (destInd (mkT ()))) then
	ix
      else
        Exceptions.raise Exceptions.error_stuck
    else
      Exceptions.raise Exceptions.error_stuck
  in
  match constr h with
      | 1 -> assert_args 3; (* ret *)        
	return sigma (ReductionStrategy.reduce sigma env (nth 1) (nth 2))
      | 2 -> assert_args 4; (* bind *)
	run' ctxt (nth 2) >>= fun (sigma', v) ->
	let t' = mkApp(nth 3, [|v|]) in
	run' (env, sigma', undo) t'
      | 3 -> assert_args 3; (* try *)
	begin
	match run' ctxt (nth 1) with
	  | Val (sigma', v) -> return sigma' v
	  | Err i -> 
            let t' = mkApp(nth 2, [|i|]) in
            run' ctxt t'
	end
      | 4 -> assert_args 2; (* raise *)
	fail (List.nth args 1)
      | 5 -> assert_args 6; (* fix1 *)
	let a, b, s, i, f, x = nth 0, nth 1, nth 2, nth 3, nth 4, nth 5 in
	run_fix ctxt h [|a|] b s i f [|x|]
      | 6 -> assert_args 8; (* fix 2 *)
	let a1, a2, b, s, i, f, x1, x2 = nth 0, nth 1, nth 2, nth 3, nth 4, nth 5, nth 6, nth 7 in
	run_fix ctxt h [|a1; a2|] b s i f [|x1; x2|]
      | 7 -> assert_args 10; (* fix 3 *)
	let a1, a2, a3, b, s, i, f, x1, x2, x3 = 
	  nth 0, nth 1, nth 2, nth 3, nth 4, nth 5, nth 6, nth 7, nth 8, nth 9 in
	run_fix ctxt h [|a1; a2; a3|] b s i f [|x1; x2; x3|]
      | 8 -> assert_args 4; (* match *)
	let (sigma', body) = runmatch (env, sigma) (nth 2) (nth 0) (nth 3) in
	run' (env, sigma', undo) body

      | 9 -> assert_args 1; (* print *)
	let s = nth 0 in
	print env sigma s;
	return sigma (Lazy.force CoqUnit.mkTT)

      | 10 -> assert_args 3; (* nu *)
	let a, f = nth 0, nth 2 in
	let fx = mkApp(lift 1 f, [|mkRel 1|]) in
        let ur = ref [] in
        begin
	match run' (push_rel (Anonymous, None, a) env, sigma, (ur :: undo)) fx with
          | Val (sigma', e) ->
            clean !ur;
	    if Int.Set.mem 1 (free_rels e) then
              Exceptions.raise Exceptions.error_param
	    else
	      return sigma' (pop e)
          | Err e -> 
            clean !ur;
	    if Int.Set.mem 1 (free_rels e) then
              Exceptions.raise Exceptions.error_param
	    else
	      fail (pop e)
        end

      | 11 -> assert_args 2; (* is_param *)
	let e = whd_betadeltaiota env sigma (nth 1) in
	if isRel e then
	  return sigma (Lazy.force CoqBool.mkTrue)
	else
	  return sigma (Lazy.force CoqBool.mkFalse)

      | 12 -> assert_args 4; (* abs *)
        let a, p, x, y = nth 0, nth 1, nth 2, nth 3 in
        abs env sigma a p x y false

      | 13 -> assert_args 4; (* abs_eq *)
        let a, p, x, y = nth 0, nth 1, nth 2, nth 3 in
        abs env sigma a p x y true

      | 14 -> assert_args 1; (* evar *)
	let t = nth 0 in
	let (sigma', ev) = Evarutil.new_evar sigma env t in
	return sigma' ev

      | 15 -> assert_args 2; (* is_evar *)
	let e = whd_betadeltaiota env sigma (nth 1) in
	if isEvar e then
	  return sigma (Lazy.force CoqBool.mkTrue)
	else
	  return sigma (Lazy.force CoqBool.mkFalse)

      | 16 -> assert_args 2; (* ref *)
	return sigma (Refs.new_ref undo (nth 0) (nth 1))

      | 17 -> assert_args 2; (* read *)
	begin
	try
	  return sigma (Refs.get env sigma undo (nth 1))
	with Refs.NullPointerException ->
	  fail (Lazy.force Exceptions.mkNullPointer)
	end

      | 18 -> assert_args 3; (* write *)
	Refs.set env sigma undo (nth 1) (nth 2);
	return sigma (Lazy.force CoqUnit.mkTT)

      | 19 -> assert_args 3; (* hash *)
        return sigma (hash ctxt (nth 1) (nth 2))

      | 20 -> assert_args 4; (* nu_let *)
	let a, t, f = nth 0, nth 2, nth 3 in
	let fx = mkApp(lift 1 f, [|mkRel 1;CoqEq.mkAppEqRefl a (mkRel 1)|]) in
        let ur = ref [] in
        begin
	match run' (push_rel (Anonymous, Some t, a) env, sigma, (ur :: undo)) fx with
          | Val (sigma', e) ->
            clean !ur;
	    return sigma' (mkLetIn (Anonymous, t, a, e))
          | Err e -> 
            clean !ur;
	    if Int.Set.mem 1 (free_rels e) then
              Exceptions.raise Exceptions.error_param
	    else
	      fail (pop e)
        end

      | 21 -> assert_args 0; (* solve_typeclasses *)
	let evd' = Typeclasses.resolve_typeclasses env sigma in
	return evd' (Lazy.force CoqUnit.mkTT)
      | _ ->
	Errors.error "I have no idea what is this construct of T that you have here"

and abs env sigma a p x y eq_proof =
  let x = whd_betadeltaiota env sigma x in
  if isRel x then
    let y' = mysubstn (mkRel 1) (destRel x) y in
    let t = mkLambda (Anonymous, a, y') in
    if eq_proof then
      let ex_a = mkProd (Anonymous, a, mkApp(lift 1 p, [|mkRel 1|])) in
      let px_type = mkApp(p, [|x|]) in
      let ex_p = mkLambda (Anonymous, ex_a, CoqEq.mkAppEq px_type (mkApp(mkRel 1, [|lift 1 x|])) (lift 1 y)) in
      let ex_x = t in
      let ex_px = CoqEq.mkAppEqRefl px_type y in
      return sigma (CoqSigT.mkAppExistT ex_a ex_p ex_x ex_px)
    else
      return sigma t
  else
    Exceptions.raise Exceptions.error_abs

and clean =
  List.iter (fun i -> Refs.invalidate i)
  
and run_fix (env, sigma, _ as ctxt) h a b s i f x =
  let fixf = mkApp(h, Array.append a [|b;s;i;f|]) in
  let c = mkApp (f, Array.append [| fixf|] x) in
  run' ctxt c

and hash (env, sigma, undo) c size =
  let size = CoqNat.from_coq env sigma size in
  let nus = List.length undo in
  let rec upd depth t =
    match kind_of_term t with
    | Rel k ->
      if depth < k then
        begin
        if k > depth + nus then
          mkRel (k - nus)
        else
          mkRel (k + nus - (2 * (k -1)))
        end
      else
        t
    | _ -> map_constr_with_binders succ upd depth t
  in
  let h = Term.hash_constr (upd 0 c) in
  CoqNat.to_coq (Pervasives.abs (h mod size))

let assert_free_of_refs c =
  if Refs.length () = 0 then
    ()
  else if occur_term (Lazy.force ForgetRef.mkRef) c then
    Errors.error "Returning a reference. This is not allowed since you might be naughty and use it in the next execution."
  else ()

let run (env, sigma) t  = 
  let _ = Refs.clean () in
  match run' (env, sigma, []) (nf_evar sigma t) with
    | Err i -> 
      assert_free_of_refs i;
      Err i
    | Val (sigma', v) -> 
      assert_free_of_refs v;
      Val (sigma', nf_evar sigma' v)


let pretypeT pretype tycon env evdref lvar c =
    let t = 
      match tycon with
      | Some ty -> ty
      | _ ->
        let sigma, univ = new_univ_variable univ_flexible !evdref in
        evdref := sigma;
        e_new_evar evdref env (mkType univ)
    in
    let tt = mkApp(mkT (), [|t|]) in
    t, pretype (mk_tycon tt) env evdref lvar c

let pretype_run pretype coerce_to_tycon tycon env evdref lvar loc c =
   let t, r = pretypeT pretype tycon env evdref lvar c in
   let d = run (env, !evdref) r.uj_val in
   match d with
       | Val (evmap, e) ->
         evdref := evmap ;
         let r = { uj_val = e; uj_type = t } in
         coerce_to_tycon loc env evdref r tycon
       | Err e -> 
         Pretype_errors.error_user_exception loc env !evdref e

