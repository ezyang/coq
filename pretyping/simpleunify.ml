open List

open Term
open Termops
open Reduction
open Reductionops
open Environ
open Evarutil
open Evd
open Names
open Closure


let whd evd c = 
  Reductionops.whd_nored_stack evd c

let success s = Evarsolve.Success s

let err s env t1 t2 = Evarsolve.UnifFailure (s, 
			Pretype_errors.ConversionFailed (env, t1, t2) )

let (&&=) opt f = 
  match opt with
  | Evarsolve.Success x -> f x
  | _ -> opt

let (||=) opt f = 
  match opt with
  | Evarsolve.UnifFailure _ -> f ()
  | _ -> opt

	
let ise_array2 evd f v1 v2 =
  let l1 = Array.length v1 in
  let l2 = Array.length v2 in
  assert (l1 <= l2) ;
  let diff = l2 - l1 in
  let rec allrec evdi n = 
    if n >= l1 then success evdi
    else
      f evdi v1.(n) v2.(n+diff) &&= (fun evdi' ->
      allrec evdi' (n+1))
  in
  allrec evd 0

exception Oops (* HACK *)
let ise_list2 evd f l1 l2 =
  let rec ise_list2 i l1 l2 =
    match l1,l2 with
      [], [] -> success i
    | [x], [y] -> f i x y
    | x::l1, y::l2 ->
        f i x y &&= (fun i' ->
        ise_list2 i' l1 l2)
    | _ -> raise Oops in
  ise_list2 evd l1 l2
    

let (>>=) opt f = 
  match opt with
  | Some(x) -> f x
  | None -> None
   
let return x = Some x


let (-.) n m =
  if n > m then n - m
  else 0

let rec is_id_subst ctxt s =
  match ctxt, s with
    | ((id, _, _) :: ctxt'), (c :: s') ->
      isVarId id c && is_id_subst ctxt' s'
    | [], [] -> true
    | _ -> false
    
let linear env args =
  let arr = Array.make (List.length (rel_context env)) false in
  List.for_all (fun a -> 
    if isRel a then
      let i = destRel a in
      if arr.(i) = true then false
      else
      begin
	arr.(i) <- true;
        true
      end
    else
      false) args
(*
let rec bla env t i args subs =
  List.fold_left (fun a t' -> 
      let ty = lookup_rel (rel_context env) (destRel a) in
      mkLambda(
  
  match args with
    | (a :: args') ->
      let ty = lookup_rel (rel_context env) (destRel a)
      
*)

let ev_define env sigma (ev, s) args t =
  let evi = Evd.find_undefined sigma ev in
  let ctxt = Evd.evar_context evi in
  if occur_evar ev t || args <> [] || not (is_id_subst ctxt (Array.to_list s)) 
    || not (Vars.closedn (List.length args) t) || not (linear env args) then
    err sigma env (mkApp (mkEvar(ev,s), Array.of_list args)) t
  else
    success (Evd.define ev t sigma)
      

let rec unify ?(conv_pb=CONV) env sigma0 t t' =
  let (c, l as t), (c', l' as t') = whd sigma0 t, whd sigma0 t' in
  let res =
    match (kind_of_term c, kind_of_term c') with
      | Evar e, _ when l = [] ->
    (* ev_define env sigma0 e l (applist t') *)
    begin
    try
      let sigma1 = Evarsolve.evar_define 
	(fun env sigma conv_pb t1 t2->unify ~conv_pb:conv_pb env sigma t1 t2)
	env sigma0 e (applist t')
      in success sigma1
    with _ -> err sigma0 env (applist t) (applist t')
    end
  | _, Evar e when l' = [] ->
    (* ev_define env sigma0 e l' (applist t) *)
    begin
    try
      let sigma1 = Evarsolve.evar_define 
	(fun env sigma conv_pb t1 t2->unify ~conv_pb:conv_pb env sigma t1 t2)
	env sigma0 e (applist t)
      in success sigma1
    with _ -> err sigma0 env (applist t) (applist t')
    end

  (* The setoid algorithm is expecting this *)
  | Meta e1, Meta e2 -> 
    if e1 = e2 then
      success sigma0
    else
      err sigma0 env (applist t) (applist t')

  (* Prop-Same, Set-Same, Type-Same *)
  | Sort s1, Sort s2 -> 
    begin
      assert (l = [] && l' = []);
      try
	let sigma1 = match conv_pb with
        | CONV -> Evd.set_eq_sort sigma0 s1 s2 
        | CUMUL -> Evd.set_leq_sort sigma0 s1 s2
        in success sigma1
      with Univ.UniverseInconsistency _ -> err sigma0 env (applist t) (applist t')
    end

  (* Lam-Same *)
  | Lambda (name, t1, c1), Lambda (_, t2, c2) 
    when l = [] && l' = [] ->
    let env' = push_rel (name, None, t1) env in
    unify env sigma0 t1 t2 &&= fun sigma1 ->
    unify env' sigma1 c1 c2 &&= fun sigma2 ->
    success sigma2

  (* Prod-Same *)
  | Prod (name, t1, c1), Prod (_, t2, c2) ->
    assert (l = [] && l' = []);
    unify env sigma0 t1 t2 &&= fun sigma1 ->
    unify (push_rel (name,None,t1) env) sigma1 ~conv_pb c1 c2

  (* Let-Same *)
  | LetIn (name, trm1, ty1, body1), LetIn (_, trm2, ty2, body2) 
    when l = [] && l'= [] ->
    unify env sigma0 trm1 trm2 &&= fun sigma1 ->
    unify (push_rel (name, Some trm1, ty1) env) 
      sigma1 ~conv_pb body1 body2

  | Rel n1, Rel n2 when n1 = n2 && l = [] && l' = [] ->
    success sigma0
  | Var id1, Var id2 when id1 = id2 && l = [] && l' = [] -> 
    success sigma0
  | Const c1, Const c2 when eq_constant c1 c2 && l = [] && l' = [] ->
    success sigma0

  | Ind c1, Ind c2 when eq_ind c1 c2 && l = [] && l' = [] ->
    success sigma0
	
  | Construct c1, Construct c2 
    when eq_constructor c1 c2 && l = [] && l' = []  ->
    success sigma0

  | CoFix (i1,(_,tys1,bds1 as recdef1)), CoFix (i2,(_,tys2,bds2))
    when i1 = i2 && l = [] && l' = [] ->
    ise_array2 sigma0 (fun i -> unify env i) tys1 tys2 &&= fun sigma1 ->
    ise_array2 sigma1 (fun i -> unify (push_rec_types recdef1 env) i) bds1 bds2

  | Case (_, p1, c1, cl1), Case (_, p2, c2, cl2) 
    when l = [] && l' = [] ->
      unify env sigma0 p1 p2 &&= fun sigma1 ->
      unify env sigma1 c1 c2 &&= fun sigma2 ->
      ise_array2 sigma2 (fun i -> unify env i) cl1 cl2

  | Fix (li1, (_, tys1, bds1 as recdef1)), Fix (li2, (_, tys2, bds2)) 
    when li1 = li2 && l = [] && l' = [] ->
    ise_array2 sigma0 (fun i -> unify env i) tys1 tys2 &&= fun sigma1 ->
    ise_array2 sigma1 (fun i -> unify (push_rec_types recdef1 env) i) bds1 bds2

  | _, _ when l <> [] && l' <> [] ->
    let n = List.length l in
    let m = List.length l' in
    let nm = n -. m in
    let mn = m -. n in
    let l1, l2 = CList.chop nm l in
    let l1', l2' = CList.chop mn l' in
      unify ~conv_pb env sigma0
        (applist (c, l1)) (applist (c', l1')) &&= fun sigma1 ->
      ise_list2 sigma1 (fun i -> unify env i) l2 l2' &&= fun sigma2 ->
      success sigma2

  | _, _ -> err sigma0 env (applist t) (applist t')
  in res

