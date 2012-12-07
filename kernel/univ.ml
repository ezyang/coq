(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Created in Caml by Gérard Huet for CoC 4.8 [Dec 1988] *)
(* Functional code by Jean-Christophe Filliâtre for Coq V7.0 [1999] *)
(* Extension with algebraic universes by HH for Coq V7.0 [Sep 2001] *)
(* Additional support for sort-polymorphic inductive types by HH [Mar 2006] *)

(* Revisions by Bruno Barras, Hugo Herbelin, Pierre Letouzey *)

open Pp
open Errors
open Util

(* Universes are stratified by a partial ordering $\le$.
   Let $\~{}$ be the associated equivalence. We also have a strict ordering
   $<$ between equivalence classes, and we maintain that $<$ is acyclic,
   and contained in $\le$ in the sense that $[U]<[V]$ implies $U\le V$.

   At every moment, we have a finite number of universes, and we
   maintain the ordering in the presence of assertions $U<V$ and $U\le V$.

   The equivalence $\~{}$ is represented by a tree structure, as in the
   union-find algorithm. The assertions $<$ and $\le$ are represented by
   adjacency lists *)

module Level = struct

  type t =
    | Prop
    | Set
    | Level of int * Names.Dir_path.t

  (* A specialized comparison function: we compare the [int] part first.
     This way, most of the time, the [Dir_path.t] part is not considered.

     Normally, placing the [int] first in the pair above in enough in Ocaml,
     but to be sure, we write below our own comparison function.

     Note: this property is used by the [check_sorted] function below. *)

  let compare u v =
    if u == v then 0
    else
    (match u,v with
    | Prop,Prop -> 0
    | Prop, _ -> -1
    | _, Prop -> 1
    | Set, Set -> 0
    | Set, _ -> -1
    | _, Set -> 1
    | Level (i1, dp1), Level (i2, dp2) ->
      if i1 < i2 then -1
      else if i1 > i2 then 1
      else Names.Dir_path.compare dp1 dp2)

  let equal u v = match u,v with
    | Prop, Prop -> true
    | Set, Set -> true
    | Level (i1, dp1), Level (i2, dp2) ->
      Int.equal i1 i2 && Int.equal (Names.Dir_path.compare dp1 dp2) 0
    | _ -> false

  let eq u v = equal u v

  let make m n = Level (n, m)

  let to_string = function
    | Prop -> "Prop"
    | Set -> "Set"
    | Level (n,d) -> Names.Dir_path.to_string d^"."^string_of_int n

  let pr u = str (to_string u)
end

let pr_universe_list l = 
  prlist_with_sep spc Level.pr l

module LSet = struct
  module M = Set.Make (Level)
  include M

  let pr s = 
    str"{" ++ pr_universe_list (elements s) ++ str"}"

  let of_list l =
    List.fold_left (fun acc x -> add x acc) empty l
end



module LMap = struct 
  module M = Map.Make (Level)
  include M

  let union l r = 
    merge (fun k l r -> 
      match l, r with
      | Some _, _ -> l
      | _, _ -> r) l r

  let elements = bindings
  let of_set s d = 
    LSet.fold (fun u -> add u d) s
      empty
    
  let of_list l =
    List.fold_left (fun m (u, v) -> add u v m) empty l 
    
  let universes m =
    fold (fun u _ acc -> LSet.add u acc) m LSet.empty

  let pr f m =
    fold (fun u v acc -> 
      h 0 (Level.pr u ++ f v) ++ acc) m (mt())
      
end

module LList = struct
  type t = Level.t list

  let empty = []
  let eq l l' = 
    try List.for_all2 Level.equal l l'
    with Invalid_argument _ -> false

end

type universe_level = Level.t
type universe_list = universe_level list
type universe_set = LSet.t
type 'a universe_map = 'a LMap.t

type 'a puniverses = 'a * universe_list
let out_punivs (a, _) = a

let compare_levels = Level.compare
let eq_levels = Level.equal

(* An algebraic universe [universe] is either a universe variable
   [Level.t] or a formal universe known to be greater than some
   universe variables and strictly greater than some (other) universe
   variables

   Universes variables denote universes initially present in the term
   to type-check and non variable algebraic universes denote the
   universes inferred while type-checking: it is either the successor
   of a universe present in the initial term to type-check or the
   maximum of two algebraic universes
*)

module Universe =
struct
  type t =
  | Atom of Level.t
  | Max of Level.t list * Level.t list

  let compare u1 u2 =
    if u1 == u2 then 0 else
    match u1, u2 with
    | Atom l1, Atom l2 -> Level.compare l1 l2
    | Max (lt1, le1), Max (lt2, le2) ->
      let c = List.compare Level.compare lt1 lt2 in
      if Int.equal c 0 then
        List.compare Level.compare le1 le2
      else c
    | Atom _, Max _ -> -1
    | Max _, Atom _ -> 1

  let equal u1 u2 = Int.equal (compare u1 u2) 0

  let make l = Atom l

  let pr = function
    | Atom u -> Level.pr u
    | Max ([],[u]) ->
      str "(" ++ Level.pr u ++ str ")+1"
    | Max (gel,gtl) ->
      let opt_sep = match gel, gtl with
	| [], _ | _, [] -> mt ()
	| _ -> pr_comma ()
      in
	str "max(" ++ hov 0
	(prlist_with_sep pr_comma Level.pr gel ++ opt_sep ++
	 prlist_with_sep pr_comma
	   (fun x -> str "(" ++ Level.pr x ++ str ")+1") gtl) ++
	str ")"

  let level = function
  | Atom l -> Some l
  | Max _ -> None


  let rec normalize x = 
    match x with
    | Atom _ -> x
    | Max ([],[]) -> Atom Level.Prop
    | Max ([u],[]) -> Atom u
    | Max (gel, gtl) -> 
      let gel' = CList.uniquize gel in
      let gtl' = CList.uniquize gtl in
	if gel' == gel && gtl' == gtl then x
	else normalize (Max (gel', gtl'))
    
end

let pr_uni = Universe.pr

open Universe

type universe = Universe.t

let universe_level = Universe.level

(* When typing [Prop] and [Set], there is no constraint on the level,
   hence the definition of [type1_univ], the type of [Prop] *)

let type1_univ = Max ([], [Level.Set])

(* Returns the formal universe that lies juste above the universe variable u.
   Used to type the sort u. *)
let super = function
  | Atom Level.Prop -> type1_univ
  | Atom u ->
      Max ([],[u])
  | Max ([],[]) (* Prop *) -> type1_univ
  | Max (gel,[]) -> Max ([], gel)
  | Max _ ->
      anomaly ("Cannot take the successor of a non variable universe:\n"^
               "(maybe a bugged tactic)")

(* Returns the formal universe that is greater than the universes u and v.
   Used to type the products. *)
let sup u v =
  match u,v with
    | Atom ua, Atom va ->
	if Level.equal ua va then u else
	  if ua = Level.Prop then v
	  else if va = Level.Prop then u
	  else Max ([ua;va],[])
    | Atom Level.Prop, v -> v
    | u, Atom Level.Prop -> u
    | u, Max ([],[]) -> u
    | Max ([],[]), v -> v
    | Atom u, Max (gel,gtl) -> 
       if List.mem u gtl then v
       else Max (List.add_set u gel,gtl)
    | Max (gel,gtl), Atom v -> 
       if List.mem v gtl then u
       else Max (List.add_set v gel,gtl)
    | Max (gel,gtl), Max (gel',gtl') ->
	let gel'' = List.union gel gel' in
	let gtl'' = List.union gtl gtl' in
	Max (List.subtract gel'' gtl'',gtl'')

(* Comparison on this type is pointer equality *)
type canonical_arc =
    { univ: Level.t;
      lt: Level.t list;
      le: Level.t list;
      rank : int}

let terminal u = {univ=u; lt=[]; le=[]; rank=0}

(* A Level.t is either an alias for another one, or a canonical one,
   for which we know the universes that are above *)

type univ_entry =
    Canonical of canonical_arc
  | Equiv of Level.t


type universes = univ_entry LMap.t

let enter_equiv_arc u v g =
  LMap.add u (Equiv v) g

let enter_arc ca g =
  LMap.add ca.univ (Canonical ca) g

(* The lower predicative level of the hierarchy that contains (impredicative)
   Prop and singleton inductive types *)
let type0m_univ = Atom Level.Prop

let is_type0m_univ = function
  | Max ([],[]) -> true
  | Atom Level.Prop -> true
  | _ -> false

(* The level of predicative Set *)
let type0_univ = Atom Level.Set

let is_type0_univ = function
  | Atom Level.Set -> true
  | Max ([Level.Set], []) -> msg_warning (str "Non canonical Set"); true
  | u -> false

let is_univ_variable = function
  | Atom (Level.Level _) -> true
  | _ -> false

let initial_universes = LMap.empty
let is_initial_universes = LMap.is_empty

(* Every Level.t has a unique canonical arc representative *)

(* repr : universes -> Level.t -> canonical_arc *)
(* canonical representative : we follow the Equiv links *)

let repr g u =
  let rec repr_rec u =
    let a =
      try LMap.find u g
      with Not_found -> anomalylabstrm "Univ.repr"
	  (str"Universe " ++ Level.pr u ++ str" undefined")
    in
    match a with
      | Equiv v -> repr_rec v
      | Canonical arc -> arc
  in
  repr_rec u

let can g = List.map (repr g)

(* [safe_repr] also search for the canonical representative, but
   if the graph doesn't contain the searched universe, we add it. *)

let safe_repr g u =
  let rec safe_repr_rec u =
    match LMap.find u g with
      | Equiv v -> safe_repr_rec v
      | Canonical arc -> arc
  in
  try g, safe_repr_rec u
  with Not_found ->
    let can = terminal u in
    enter_arc can g, can

(* reprleq : canonical_arc -> canonical_arc list *)
(* All canonical arcv such that arcu<=arcv with arcv#arcu *)
let reprleq g arcu =
  let rec searchrec w = function
    | [] -> w
    | v :: vl ->
	let arcv = repr g v in
        if List.memq arcv w || arcu==arcv then
	  searchrec w vl
        else
	  searchrec (arcv :: w) vl
  in
  searchrec [] arcu.le


(* between : Level.t -> canonical_arc -> canonical_arc list *)
(* between u v = {w|u<=w<=v, w canonical}          *)
(* between is the most costly operation *)

let between g arcu arcv =
  (* good are all w | u <= w <= v  *)
  (* bad are all w | u <= w ~<= v *)
    (* find good and bad nodes in {w | u <= w} *)
    (* explore b u = (b or "u is good") *)
  let rec explore ((good, bad, b) as input) arcu =
    if List.memq arcu good then
      (good, bad, true) (* b or true *)
    else if List.memq arcu bad then
      input    (* (good, bad, b or false) *)
    else
      let leq = reprleq g arcu in
	(* is some universe >= u good ? *)
      let good, bad, b_leq =
	List.fold_left explore (good, bad, false) leq
      in
	if b_leq then
	  arcu::good, bad, true (* b or true *)
	else
	  good, arcu::bad, b    (* b or false *)
  in
  let good,_,_ = explore ([arcv],[],false) arcu in
    good

(* We assume  compare(u,v) = LE with v canonical (see compare below).
   In this case List.hd(between g u v) = repr u
   Otherwise, between g u v = []
 *)

type constraint_type = Lt | Le | Eq

type explanation = (constraint_type * universe) list

let constraint_type_ord c1 c2 = match c1, c2 with
| Lt, Lt -> 0
| Lt, _ -> -1
| Le, Lt -> 1
| Le, Le -> 0
| Le, Eq -> -1
| Eq, Eq -> 0
| Eq, _ -> 1

(* Assuming the current universe has been reached by [p] and [l]
   correspond to the universes in (direct) relation [rel] with it,
   make a list of canonical universe, updating the relation with
   the starting point (path stored in reverse order). *)
let canp g (p:explanation) rel l : (canonical_arc * explanation) list =
  List.map (fun u -> (repr g u, (rel,Atom u)::p)) l

type order = EQ | LT of explanation | LE of explanation | NLE

(** [compare_neq] : is [arcv] in the transitive upward closure of [arcu] ?

  In [strict] mode, we fully distinguish between LE and LT, while in
  non-strict mode, we simply answer LE for both situations.

  If [arcv] is encountered in a LT part, we could directly answer
  without visiting unneeded parts of this transitive closure.
  In [strict] mode, if [arcv] is encountered in a LE part, we could only
  change the default answer (1st arg [c]) from NLE to LE, since a strict
  constraint may appear later. During the recursive traversal,
  [lt_done] and [le_done] are universes we have already visited,
  they do not contain [arcv]. The 4rd arg is [(lt_todo,le_todo)],
  two lists of universes not yet considered, known to be above [arcu],
  strictly or not.

  We use depth-first search, but the presence of [arcv] in [new_lt]
  is checked as soon as possible : this seems to be slightly faster
  on a test.
*)

let compare_neq strict g arcu arcv =
  (* [c] characterizes whether (and how) arcv has already been related
     to arcu among the lt_done,le_done universe *)
  let rec cmp c lt_done le_done = function
  | [],[] -> c
  | (arc,p)::lt_todo, le_todo ->
    if List.memq arc lt_done then
      cmp c lt_done le_done (lt_todo,le_todo)
    else
      let lt_new = canp g p Lt arc.lt@ canp g p Le arc.le in
      (try
	 let p = List.assq arcv lt_new in
	 if strict then LT p else LE p
       with Not_found ->
	 cmp c (arc::lt_done) le_done (lt_new@lt_todo,le_todo))
  | [], (arc,p)::le_todo ->
    if arc == arcv then
      (* No need to continue inspecting universes above arc:
	 if arcv is strictly above arc, then we would have a cycle.
         But we cannot answer LE yet, a stronger constraint may
	 come later from [le_todo]. *)
      if strict then cmp (LE p) lt_done le_done ([],le_todo) else LE p
    else
      if (List.memq arc lt_done) || (List.memq arc le_done) then
	cmp c lt_done le_done ([],le_todo)
      else
	let lt_new = canp g p Lt arc.lt in
	(try
	  let p = List.assq arcv lt_new in
	  if strict then LT p else LE p
	 with Not_found ->
	   let le_new = canp g p Le arc.le in
	   cmp c lt_done (arc::le_done) (lt_new, le_new@le_todo))
  in
  cmp NLE [] [] ([],[arcu,[]])

let compare g arcu arcv =
  if arcu == arcv then EQ else compare_neq true g arcu arcv

let is_leq g arcu arcv =
  arcu == arcv ||
 (match compare_neq false g arcu arcv with
     NLE -> false
   | (EQ|LE _|LT _) -> true)

let is_lt g arcu arcv =
  match compare g arcu arcv with
      LT _ -> true
    | (EQ|LE _|NLE) -> false

(* Invariants : compare(u,v) = EQ <=> compare(v,u) = EQ
                compare(u,v) = LT or LE => compare(v,u) = NLE
                compare(u,v) = NLE => compare(v,u) = NLE or LE or LT

   Adding u>=v is consistent iff compare(v,u) # LT
    and then it is redundant iff compare(u,v) # NLE
   Adding u>v is consistent iff compare(v,u) = NLE
    and then it is redundant iff compare(u,v) = LT *)

(** * Universe checks [check_eq] and [check_leq], used in coqchk *)

(** First, checks on universe levels *)

let check_equal g u v =
  let g, arcu = safe_repr g u in
  let _, arcv = safe_repr g v in
  arcu == arcv

let check_smaller g strict u v =
  let g, arcu = safe_repr g u in
  let g, arcv = safe_repr g v in
  if strict then
    is_lt g arcu arcv
  else
    arcu == snd (safe_repr g Level.Prop) || is_leq g arcu arcv

(** Then, checks on universes *)

type check_function = universes -> universe -> universe -> bool

let incl_list cmp l1 l2 =
  List.for_all (fun x1 -> List.exists (fun x2 -> cmp x1 x2) l2) l1

let compare_list cmp l1 l2 =
  (l1 == l2)
  || (incl_list cmp l1 l2 && incl_list cmp l2 l1)

let check_eq g u v =
  match u,v with
    | Atom ul, Atom vl -> check_equal g ul vl
    | Max(ule,ult), Max(vle,vlt) ->
        (* TODO: remove elements of lt in le! *)
        compare_list (check_equal g) ule vle &&
        compare_list (check_equal g) ult vlt
    | _ -> anomaly "check_eq" (* not complete! (Atom(u) = Max([u],[]) *)

let exists_bigger g strict ul l =
  List.exists (fun ul' -> check_smaller g strict ul ul') l

let check_leq g u v =
  match u,v with
  | Atom Level.Prop, v -> true
  | Atom ul, Atom vl -> check_smaller g false ul vl
  | Max(le,lt), Atom vl ->
    List.for_all (fun ul -> check_smaller g false ul vl) le &&
    List.for_all (fun ul -> check_smaller g true ul vl) lt
  | Max(le,lt), Max(le',lt') ->
    (* Every u in le is smaller or equal to one in le' or lt'.
       Every u in lt is smaller or equal to one in lt or 
       strictly smaller than one in le'. *)
  List.for_all (fun ul -> 
    exists_bigger g false ul le' || exists_bigger g false ul lt') le &&
  List.for_all (fun ul -> 
    exists_bigger g true ul le' || exists_bigger g false ul lt') lt
  | Atom ul, Max (le, lt) ->
    exists_bigger g false ul le || exists_bigger g false ul lt

(** Enforcing new constraints : [setlt], [setleq], [merge], [merge_disc] *)

(* setlt : Level.t -> Level.t -> reason -> unit *)
(* forces u > v *)
(* this is normally an update of u in g rather than a creation. *)
let setlt g arcu arcv =
  let arcu' = {arcu with lt=arcv.univ::arcu.lt} in
  enter_arc arcu' g, arcu'

(* checks that non-redundant *)
let setlt_if (g,arcu) v =
  let arcv = repr g v in
  if is_lt g arcu arcv then g, arcu
  else setlt g arcu arcv

(* setleq : Level.t -> Level.t -> unit *)
(* forces u >= v *)
(* this is normally an update of u in g rather than a creation. *)
let setleq g arcu arcv =
  let arcu' = {arcu with le=arcv.univ::arcu.le} in
  enter_arc arcu' g, arcu'


(* checks that non-redundant *)
let setleq_if (g,arcu) v =
  let arcv = repr g v in
  if is_leq g arcu arcv then g, arcu
  else setleq g arcu arcv

(* merge : Level.t -> Level.t -> unit *)
(* we assume  compare(u,v) = LE *)
(* merge u v  forces u ~ v with repr u as canonical repr *)
let merge g arcu arcv =
  (* we find the arc with the biggest rank, and we redirect all others to it *)
  let arcu, g, v =
    let best_ranked (max_rank, old_max_rank, best_arc, rest) arc =
      if arc.rank >= max_rank
      then (arc.rank, max_rank, arc, best_arc::rest)
      else (max_rank, old_max_rank, best_arc, arc::rest)
    in
    match between g arcu arcv with
      | [] -> anomaly "Univ.between"
      | arc::rest ->
        let (max_rank, old_max_rank, best_arc, rest) =
          List.fold_left best_ranked (arc.rank, min_int, arc, []) rest in
        if max_rank > old_max_rank then best_arc, g, rest
        else begin
          (* one redirected node also has max_rank *)
          let arcu = {best_arc with rank = max_rank + 1} in
          arcu, enter_arc arcu g, rest
        end 
  in
  let redirect (g,w,w') arcv =
    let g' = enter_equiv_arc arcv.univ arcu.univ g in
    (g',List.unionq arcv.lt w,arcv.le@w')
  in
  let (g',w,w') = List.fold_left redirect (g,[],[]) v in
  let g_arcu = (g',arcu) in
  let g_arcu = List.fold_left setlt_if g_arcu w in
  let g_arcu = List.fold_left setleq_if g_arcu w' in
  fst g_arcu

(* merge_disc : Level.t -> Level.t -> unit *)
(* we assume  compare(u,v) = compare(v,u) = NLE *)
(* merge_disc u v  forces u ~ v with repr u as canonical repr *)
let merge_disc g arc1 arc2 =
  let arcu, arcv = if arc1.rank < arc2.rank then arc2, arc1 else arc1, arc2 in
  let arcu, g = 
    if arc1.rank <> arc2.rank then arcu, g
    else
      let arcu = {arcu with rank = succ arcu.rank} in 
      arcu, enter_arc arcu g
  in
  let g' = enter_equiv_arc arcv.univ arcu.univ g in
  let g_arcu = (g',arcu) in
  let g_arcu = List.fold_left setlt_if g_arcu arcv.lt in
  let g_arcu = List.fold_left setleq_if g_arcu arcv.le in
  fst g_arcu

(* Universe inconsistency: error raised when trying to enforce a relation
   that would create a cycle in the graph of universes. *)

exception UniverseInconsistency of
  constraint_type * universe * universe * explanation

let error_inconsistency o u v (p:explanation) =
  raise (UniverseInconsistency (o,Atom u,Atom v,p))

(* enforce_univ_leq : Level.t -> Level.t -> unit *)
(* enforce_univ_leq u v will force u<=v if possible, will fail otherwise *)
let enforce_univ_leq u v g =
  let g,arcu = safe_repr g u in
  let g,arcv = safe_repr g v in
  if is_leq g arcu arcv then g
  else match compare g arcv arcu with
    | LT p -> error_inconsistency Le u v (List.rev p)
    | LE _ -> merge g arcv arcu
    | NLE -> fst (setleq g arcu arcv)
    | EQ -> anomaly "Univ.compare"

(* enforc_univ_eq : Level.t -> Level.t -> unit *)
(* enforc_univ_eq u v will force u=v if possible, will fail otherwise *)
let enforce_univ_eq u v g =
  let g,arcu = safe_repr g u in
  let g,arcv = safe_repr g v in
  match compare g arcu arcv with
    | EQ -> g
    | LT p -> error_inconsistency Eq u v (List.rev p)
    | LE _ -> merge g arcu arcv
    | NLE ->
	(match compare g arcv arcu with
           | LT p -> error_inconsistency Eq u v (List.rev p)
           | LE _ -> merge g arcv arcu
           | NLE -> merge_disc g arcu arcv
           | EQ -> anomaly "Univ.compare")

(* enforce_univ_lt u v will force u<v if possible, will fail otherwise *)
let enforce_univ_lt u v g =
  let g,arcu = safe_repr g u in
  let g,arcv = safe_repr g v in
  match compare g arcu arcv with
    | LT _ -> g
    | LE _ -> fst (setlt g arcu arcv)
    | EQ -> error_inconsistency Lt u v [(Eq,Atom v)]
    | NLE ->
      (match compare_neq false g arcv arcu with
	  NLE -> fst (setlt g arcu arcv)
	| EQ -> anomaly "Univ.compare"
	| (LE p|LT p) -> error_inconsistency Lt u v (List.rev p))

(* Constraints and sets of consrtaints. *)

type univ_constraint = Level.t * constraint_type * Level.t

let enforce_constraint cst g =
  match cst with
    | (u,Lt,v) -> enforce_univ_lt u v g
    | (u,Le,v) -> enforce_univ_leq u v g
    | (u,Eq,v) -> enforce_univ_eq u v g

module Constraint = Set.Make(
  struct
    type t = univ_constraint
    let compare (u,c,v) (u',c',v') =
      let i = constraint_type_ord c c' in
      if not (Int.equal i 0) then i
      else
	let i' = Level.compare u u' in
	if not (Int.equal i' 0) then i'
	else Level.compare v v'
  end)

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
type universe_subst = universe_level universe_map

(** A full substitution might involve algebraic universes *)
type universe_full_subst = universe universe_map

(** Pretty-printing *)
let pr_constraints c =
  Constraint.fold (fun (u1,op,u2) pp_std ->
		     let op_str = match op with
		       | Lt -> " < "
		       | Le -> " <= "
		       | Eq -> " = "
		     in pp_std ++  Level.pr u1 ++ str op_str ++
			  Level.pr u2 ++ fnl () )  c (str "")
let pr_universe_context (ctx, cst) =
  if ctx = [] && Constraint.is_empty cst then mt() else
    pr_universe_list ctx ++ str " |= " ++ v 1 (pr_constraints cst)

let pr_universe_context_set (ctx, cst) = 
  if LSet.is_empty ctx && Constraint.is_empty cst then mt() else
    LSet.pr ctx ++ str " |= " ++ v 1 (pr_constraints cst)

(** Constraints *)
let empty_constraint = Constraint.empty
let is_empty_constraint = Constraint.is_empty
let union_constraints = Constraint.union

let constraints_of (_, cst) = cst

(** Universe contexts (variables as a list) *)
let empty_universe_context = ([], empty_constraint)
let is_empty_universe_context (univs, cst) = 
  univs = [] && is_empty_constraint cst
let union_universe_context (univs, cst) (univs', cst') =
  CList.union univs univs', union_constraints cst cst'

(** Universe contexts (variables as a set) *)
let empty_universe_context_set = (LSet.empty, empty_constraint)
let is_empty_universe_context_set (univs, cst) =
  LSet.is_empty univs
let singleton_universe_context_set u = (LSet.singleton u, empty_constraint)
let is_empty_universe_context_set (univs, cst) = 
  LSet.is_empty univs && is_empty_constraint cst

let union_universe_context_set (univs, cst) (univs', cst') =
  LSet.union univs univs', union_constraints cst cst'

let universe_context_set_of_list l =
  (LSet.of_list l, empty_constraint)

let universe_context_set_of_universe_context (ctx,cst) =
  (LSet.of_list ctx, cst)

let constraint_depend (l,d,r) u =
  Level.eq l u || Level.eq l r

let constraint_depend_list (l,d,r) us =
  List.mem l us || List.mem r us

let constraints_depend cstr us = 
  Constraint.exists (fun c -> constraint_depend_list c us) cstr

let remove_dangling_constraints dangling cst =
  Constraint.fold (fun (l,d,r as cstr) cst' -> 
    if List.mem l dangling || List.mem r dangling then cst'
    else
      (** Unnecessary constraints Prop <= u *)
      if l = Level.Prop && d = Le then cst'
      else Constraint.add cstr cst') cst Constraint.empty
  
let check_context_subset (univs, cst) (univs', cst') =
  let newunivs, dangling = List.partition (fun u -> LSet.mem u univs) univs' in
    (* Some universe variables that don't appear in the term 
       are still mentionned in the constraints. This is the 
       case for "fake" universe variables that correspond to +1s.
       assert(not (constraints_depend cst' dangling));*)
    (* TODO: check implication *)
  (** Remove local universes that do not appear in any constraint, they
      are really entirely parametric. *)
  (* let newunivs, dangling' = List.partition (fun u -> constraints_depend cst [u]) newunivs in *)
  let cst' = remove_dangling_constraints dangling cst in
    newunivs, cst'

let add_constraints_ctx (univs, cst) cst' =
  univs, union_constraints cst cst'

let add_universes_ctx univs ctx =
  union_universe_context_set (universe_context_set_of_list univs) ctx

let context_of_universe_context_set (ctx, cst) =
  (LSet.elements ctx, cst)

(** Substitutions. *)

let make_universe_subst inst (ctx, csts) = 
  try List.fold_left2 (fun acc c i -> LMap.add c i acc) 
        LMap.empty ctx inst
  with Invalid_argument _ -> 
    anomaly ("Mismatched instance and context when building universe substitution")

let empty_subst = LMap.empty
let is_empty_subst = LMap.is_empty

(** Substitution functions *)
let subst_univs_level subst l = 
  try LMap.find l subst
  with Not_found -> l

let subst_univs_universe subst u =
  match u with
  | Atom a -> 
    let a' = subst_univs_level subst a in
      if a' == a then u else Atom a'
  | Max (gel, gtl) -> 
    let gel' = CList.smartmap (subst_univs_level subst) gel in
    let gtl' = CList.smartmap (subst_univs_level subst) gtl in
      if gel == gel' && gtl == gtl' then u
      else Universe.normalize (Max (gel', gtl'))

let subst_univs_full_level subst l = 
  try LMap.find l subst
  with Not_found -> Atom l

let subst_univs_full_level_opt subst l = 
  try Some (LMap.find l subst)
  with Not_found -> None

let subst_univs_full_level_fail subst l = 
  try 
    (match LMap.find l subst with
    | Atom u -> u
    | Max _ -> anomaly "Trying to substitute an algebraic universe where only levels are allowed")
  with Not_found -> l

let subst_univs_full_universe subst u =
  match u with
  | Atom a -> 
    (match subst_univs_full_level_opt subst a with
    | Some a' -> a'
    | None -> u)
  | Max (gel, gtl) -> 
    let gel' = CList.smartmap (subst_univs_full_level_fail subst) gel in
    let gtl' = CList.smartmap (subst_univs_full_level_fail subst) gtl in
      if gel == gel' && gtl == gtl' then u
      else Universe.normalize (Max (gel', gtl'))

let subst_univs_constraint subst (u,d,v) =
  let u' = subst_univs_level subst u and v' = subst_univs_level subst v in
    if d <> Lt && Level.eq u' v' then None
    else Some (u',d,v')

let subst_univs_constraints subst csts =
  Constraint.fold 
    (fun c -> Option.fold_right Constraint.add (subst_univs_constraint subst c))
    csts Constraint.empty 

(** Substitute instance inst for ctx in csts *)
let instantiate_univ_context subst (_, csts) = 
  subst_univs_constraints subst csts

(** Constraint functions. *)

type constraint_function =
    universe -> universe -> constraints -> constraints

let constraint_add_leq v u c =
  (* We just discard trivial constraints like u<=u *)
  if Level.equal v u then c
  else Constraint.add (v,Le,u) c

let check_univ_eq u v =
  match u, v with
  | (Atom u, Atom v)
  | Atom u, Max ([v],[])
  | Max ([u],[]), Atom v -> Level.equal u v
  | Max (gel,gtl), Max (gel',gtl') ->
    compare_list Level.equal gel gel' &&
    compare_list Level.equal gtl gtl'
  | _, _ -> false

let enforce_leq u v c =
  match u, v with
  | Atom u, Atom v -> constraint_add_leq u v c
  | Max (gel,gtl), Atom v ->
      let d = List.fold_right (fun u -> constraint_add_leq u v) gel c in
      List.fold_right (fun u -> Constraint.add (u,Lt,v)) gtl d
  | _ -> anomaly "A universe bound can only be a variable"

let enforce_leq u v c =
  if check_univ_eq u v then c
  else enforce_leq u v c

let enforce_eq u v c =
  match (u,v) with
    | Atom u, Atom v ->
      (* We discard trivial constraints like u=u *)
      if Level.equal u v then c else Constraint.add (u,Eq,v) c
    | _ -> anomaly "A universe comparison can only happen between variables"

let enforce_eq u v c =
  if check_univ_eq u v then c
  else enforce_eq u v c

let enforce_eq_level u v c =
  if Level.equal u v then c else Constraint.add (u,Eq,v) c

let enforce_leq_level u v c =
  if Level.equal u v then c else Constraint.add (u,Le,v) c
  
let merge_constraints c g =
  Constraint.fold enforce_constraint c g

let check_consistent_constraints (ctx,cstrs) cstrs' =
  (* TODO *) ()

(* Normalization *)

let lookup_level u g =
  try Some (LMap.find u g) with Not_found -> None

(** [normalize_universes g] returns a graph where all edges point
    directly to the canonical representent of their target. The output
    graph should be equivalent to the input graph from a logical point
    of view, but optimized. We maintain the invariant that the key of
    a [Canonical] element is its own name, by keeping [Equiv] edges
    (see the assertion)... I (Stéphane Glondu) am not sure if this
    plays a role in the rest of the module. *)
let normalize_universes g =
  let rec visit u arc cache = match lookup_level u cache with
    | Some x -> x, cache
    | None -> match Lazy.force arc with
    | None ->
      u, LMap.add u u cache
    | Some (Canonical {univ=v; lt=_; le=_}) ->
      v, LMap.add u v cache
    | Some (Equiv v) ->
      let v, cache = visit v (lazy (lookup_level v g)) cache in
      v, LMap.add u v cache
  in
  let cache = LMap.fold
    (fun u arc cache -> snd (visit u (Lazy.lazy_from_val (Some arc)) cache))
    g LMap.empty
  in
  let repr x = LMap.find x cache in
  let lrepr us = List.fold_left
    (fun e x -> LSet.add (repr x) e) LSet.empty us
  in
  let canonicalize u = function
    | Equiv _ -> Equiv (repr u)
    | Canonical {univ=v; lt=lt; le=le; rank=rank} ->
      assert (u == v);
      (* avoid duplicates and self-loops *)
      let lt = lrepr lt and le = lrepr le in
      let le = LSet.filter
        (fun x -> x != u && not (LSet.mem x lt)) le
      in
      LSet.iter (fun x -> assert (x != u)) lt;
      Canonical {
        univ = v;
        lt = LSet.elements lt;
        le = LSet.elements le;
	rank = rank
      }
  in
  LMap.mapi canonicalize g

(** [check_sorted g sorted]: [g] being a universe graph, [sorted]
    being a map to levels, checks that all constraints in [g] are
    satisfied in [sorted]. *)
let check_sorted g sorted =
  let get u = try LMap.find u sorted with
    | Not_found -> assert false
  in
  let iter u arc =
    let lu = get u in match arc with
    | Equiv v -> assert (Int.equal lu (get v))
    | Canonical {univ = u'; lt = lt; le = le} ->
      assert (u == u');
      List.iter (fun v -> assert (lu <= get v)) le;
      List.iter (fun v -> assert (lu < get v)) lt
  in
  LMap.iter iter g

(**
  Bellman-Ford algorithm with a few customizations:
    - [weight(eq|le) = 0], [weight(lt) = -1]
    - a [le] edge is initially added from [bottom] to all other
      vertices, and [bottom] is used as the source vertex
*)
let bellman_ford bottom g =
  let () = match lookup_level bottom g with
  | None -> ()
  | Some _ -> assert false
  in
  let ( << ) a b = match a, b with
    | _, None -> true
    | None, _ -> false
    | Some x, Some y -> x < y
  and ( ++ ) a y = match a with
    | None -> None
    | Some x -> Some (x-y)
  and push u x m = match x with
    | None -> m
    | Some y -> LMap.add u y m
  in
  let relax u v uv distances =
    let x = lookup_level u distances ++ uv in
    if x << lookup_level v distances then push v x distances
    else distances
  in
  let init = LMap.add bottom 0 LMap.empty in
  let vertices = LMap.fold (fun u arc res ->
    let res = LSet.add u res in
    match arc with
      | Equiv e -> LSet.add e res
      | Canonical {univ=univ; lt=lt; le=le} ->
        assert (u == univ);
        let add res v = LSet.add v res in
        let res = List.fold_left add res le in
        let res = List.fold_left add res lt in
        res) g LSet.empty
  in
  let g =
    let node = Canonical {
      univ = bottom;
      lt = [];
      le = LSet.elements vertices
      rank = 0
    } in LMap.add bottom node g
  in
  let rec iter count accu =
    if count <= 0 then
      accu
    else
      let accu = LMap.fold (fun u arc res -> match arc with
        | Equiv e -> relax e u 0 (relax u e 0 res)
        | Canonical {univ=univ; lt=lt; le=le} ->
          assert (u == univ);
          let res = List.fold_left (fun res v -> relax u v 0 res) res le in
          let res = List.fold_left (fun res v -> relax u v 1 res) res lt in
          res) g accu
      in iter (count-1) accu
  in
  let distances = iter (LSet.cardinal vertices) init in
  let () = LMap.iter (fun u arc ->
    let lu = lookup_level u distances in match arc with
      | Equiv v ->
        let lv = lookup_level v distances in
        assert (not (lu << lv) && not (lv << lu))
      | Canonical {univ=univ; lt=lt; le=le} ->
        assert (u == univ);
        List.iter (fun v -> assert (not (lu ++ 0 << lookup_level v distances))) le;
        List.iter (fun v -> assert (not (lu ++ 1 << lookup_level v distances))) lt) g
  in distances

(** [sort_universes g] builds a map from universes in [g] to natural
    numbers. It outputs a graph containing equivalence edges from each
    level appearing in [g] to [Type.n], and [lt] edges between the
    [Type.n]s. The output graph should imply the input graph (and the
    implication will be strict most of the time), but is not
    necessarily minimal. Note: the result is unspecified if the input
    graph already contains [Type.n] nodes (calling a module Type is
    probably a bad idea anyway). *)
let sort_universes orig =
  let mp = Names.Dir_path.make [Names.Id.of_string "Type"] in
  let rec make_level accu g i =
    let type0 = Level.Level (i, mp) in
    let distances = bellman_ford type0 g in
    let accu, continue = LMap.fold (fun u x (accu, continue) ->
      let continue = continue || x < 0 in
      let accu =
        if Int.equal x 0 && u != type0 then LMap.add u i accu
        else accu
      in accu, continue) distances (accu, false)
    in
    let filter x = not (LMap.mem x accu) in
    let push g u =
      if LMap.mem u g then g else LMap.add u (Equiv u) g
    in
    let g = LMap.fold (fun u arc res -> match arc with
      | Equiv v as x ->
        begin match filter u, filter v with
          | true, true -> LMap.add u x res
          | true, false -> push res u
          | false, true -> push res v
          | false, false -> res
        end
      | Canonical {univ=v; lt=lt; le=le; rank=r} ->
        assert (u == v);
        if filter u then
          let lt = List.filter filter lt in
          let le = List.filter filter le in
          LMap.add u (Canonical {univ=u; lt=lt; le=le; rank=r}) res
        else
          let res = List.fold_left (fun g u -> if filter u then push g u else g) res lt in
          let res = List.fold_left (fun g u -> if filter u then push g u else g) res le in
          res) g LMap.empty
    in
    if continue then make_level accu g (i+1) else i, accu
  in
  let max, levels = make_level LMap.empty orig 0 in
  (* defensively check that the result makes sense *)
  check_sorted orig levels;
  let types = Array.init (max+1) (fun x -> Level.Level (x, mp)) in
  let g = LMap.map (fun x -> Equiv types.(x)) levels in
  let g =
    let rec aux i g =
      if i < max then
        let u = types.(i) in
        let g = LMap.add u (Canonical {
          univ = u;
          le = [];
          lt = [types.(i+1)];
	  rank = 1
        }) g in aux (i+1) g
      else g
    in aux 0 g
  in g

(**********************************************************************)
(* Tools for sort-polymorphic inductive types                         *)

(* Miscellaneous functions to remove or test local univ assumed to
   occur only in the le constraints *)

let make_max = function
  | ([u],[]) -> Atom u
  | (le,lt) -> Max (le,lt)

let remove_large_constraint u = function
  | Atom u' as x -> if Level.equal u u' then Max ([],[]) else x
  | Max (le,lt) -> make_max (List.remove u le,lt)

let is_direct_constraint u = function
  | Atom u' -> Level.equal u u'
  | Max (le,lt) -> List.mem u le

(*
   Solve a system of universe constraint of the form

   u_s11, ..., u_s1p1, w1 <= u1
   ...
   u_sn1, ..., u_snpn, wn <= un

where

  - the ui (1 <= i <= n) are universe variables,
  - the sjk select subsets of the ui for each equations,
  - the wi are arbitrary complex universes that do not mention the ui.
*)

let is_direct_sort_constraint s v = match s with
  | Some u -> is_direct_constraint u v
  | None -> false

let solve_constraints_system levels level_bounds =
  let levels =
    Array.map (Option.map (function Atom u -> u | _ -> anomaly "expects Atom"))
      levels in
  let v = Array.copy level_bounds in
  let nind = Array.length v in
  for i=0 to nind-1 do
    for j=0 to nind-1 do
      if not (Int.equal i j) && is_direct_sort_constraint levels.(j) v.(i) then
	v.(i) <- sup v.(i) level_bounds.(j)
    done;
    for j=0 to nind-1 do
      match levels.(j) with
      | Some u -> v.(i) <- remove_large_constraint u v.(i)
      | None -> ()
    done
  done;
  v

let subst_large_constraint u u' v =
  match u with
  | Atom u ->
      if is_direct_constraint u v then sup u' (remove_large_constraint u v)
      else v
  | _ ->
      anomaly "expect a universe level"

let subst_large_constraints =
  List.fold_right (fun (u,u') -> subst_large_constraint u u')

let no_upper_constraints u cst =
  match u with
  | Atom u ->
    let test (u1, _, _) =
      not (Int.equal (Level.compare u1 u) 0) in
    Constraint.for_all test cst
  | Max _ -> anomaly "no_upper_constraints"

(* Is u mentionned in v (or equals to v) ? *)

let univ_depends u v =
  match u, v with
    | Atom u, Atom v -> Level.equal u v
    | Atom u, Max (gel,gtl) -> List.mem u gel || List.mem u gtl
    | _ -> anomaly "univ_depends given a non-atomic 1st arg"

(* Pretty-printing *)

let pr_arc = function
  | _, Canonical {univ=u; lt=[]; le=[]} ->
      mt ()
  | _, Canonical {univ=u; lt=lt; le=le} ->
      let opt_sep = match lt, le with
      | [], _ | _, [] -> mt ()
      | _ -> spc ()
      in
      Level.pr u ++ str " " ++
      v 0
        (pr_sequence (fun v -> str "< " ++ Level.pr v) lt ++
	 opt_sep ++
         pr_sequence (fun v -> str "<= " ++ Level.pr v) le) ++
      fnl ()
  | u, Equiv v ->
      Level.pr u  ++ str " = " ++ Level.pr v ++ fnl ()

let pr_universes g =
  let graph = LMap.fold (fun u a l -> (u,a)::l) g [] in
  prlist pr_arc graph

(* Dumping constraints to a file *)

let dump_universes output g =
  let dump_arc u = function
    | Canonical {univ=u; lt=lt; le=le} ->
	let u_str = Level.to_string u in
	List.iter (fun v -> output Lt u_str (Level.to_string v)) lt;
	List.iter (fun v -> output Le u_str (Level.to_string v)) le
    | Equiv v ->
      output Eq (Level.to_string u) (Level.to_string v)
  in
    LMap.iter dump_arc g

(* Hash-consing *)

module Hunivlevel =
  Hashcons.Make(
    struct
      type t = universe_level
      type u = Names.Dir_path.t -> Names.Dir_path.t
      let hashcons hdir = function
	| Level.Prop -> Level.Prop
	| Level.Set -> Level.Set
	| Level.Level (n,d) -> Level.Level (n,hdir d)
      let equal l1 l2 =
        l1 == l2 ||
        match l1,l2 with
	| Level.Prop, Level.Prop -> true
	| Level.Set, Level.Set -> true
	| Level.Level (n,d), Level.Level (n',d') ->
	  n == n' && d == d'
	| _ -> false
      let hash = Hashtbl.hash
    end)

module Hunivcons =
    struct
      type t = universe
      type u = universe_level -> universe_level
      let hashcons hdir = function
	| Atom u -> Atom (hdir u)
	| Max (gel,gtl) -> Max (List.map hdir gel, List.map hdir gtl)
      let equal u v =
        u == v ||
	match u, v with
	  | Atom u, Atom v -> u == v
	  | Max (gel,gtl), Max (gel',gtl') ->
	      (List.for_all2eq (==) gel gel') &&
              (List.for_all2eq (==) gtl gtl')
	  | _ -> false
      let hash = Hashtbl.hash
    end

module Huniv =
  Hashcons.Make(Hunivcons)

let hcons_univlevel = Hashcons.simple_hcons Hunivlevel.generate Names.Dir_path.hcons
let hcons_univ = Hashcons.simple_hcons Huniv.generate hcons_univlevel

let hcons_univ x = hcons_univ (Universe.normalize x)

let equal_universes x y = 
  let x' = hcons_univ x and y' = hcons_univ y in
    if Hunivcons.equal x' y' then true
    else 
      (match x', y' with
      | Atom _, Atom _ -> false (* already handled *)
      | Max (gel, gtl), Max (gel', gtl') -> 
	(* Consider lists as sets, i.e. up to reordering,
	   they are already without duplicates thanks to normalization. *)
        CList.eq_set gel gel' && CList.eq_set gtl gtl'
      | _, _ -> false)

module Hconstraint =
  Hashcons.Make(
    struct
      type t = univ_constraint
      type u = universe_level -> universe_level
      let hashcons hul (l1,k,l2) = (hul l1, k, hul l2)
      let equal (l1,k,l2) (l1',k',l2') =
	l1 == l1' && k == k' && l2 == l2'
      let hash = Hashtbl.hash
    end)

module Hconstraints =
  Hashcons.Make(
    struct
      type t = constraints
      type u = univ_constraint -> univ_constraint
      let hashcons huc s =
	Constraint.fold (fun x -> Constraint.add (huc x)) s Constraint.empty
      let equal s s' =
	List.for_all2eq (==)
	  (Constraint.elements s)
	  (Constraint.elements s')
      let hash = Hashtbl.hash
    end)

let hcons_constraint = Hashcons.simple_hcons Hconstraint.generate hcons_univlevel
let hcons_constraints = Hashcons.simple_hcons Hconstraints.generate hcons_constraint

module Huniverse_list = 
  Hashcons.Make(
    struct
      type t = universe_list
      type u = universe_level -> universe_level
      let hashcons huc s =
	List.fold_left (fun a x -> huc x :: a) s []
      let equal s s' = List.for_all2eq (==) s s'
      let hash = Hashtbl.hash
    end)

let hcons_universe_list = 
  Hashcons.simple_hcons Huniverse_list.generate hcons_univlevel
let hcons_universe_context (v, c) = 
  (hcons_universe_list v, hcons_constraints c)

module Huniverse_set = 
  Hashcons.Make(
    struct
      type t = universe_set
      type u = universe_level -> universe_level
      let hashcons huc s =
	LSet.fold (fun x -> LSet.add (huc x)) s LSet.empty
      let equal s s' =
	LSet.equal s s'
      let hash = Hashtbl.hash
    end)

let hcons = 
  Hashcons.simple_hcons Huniverse_set.generate hcons_univlevel
let hcons_universe_context_set (v, c) = 
  (hcons v, hcons_constraints c)
