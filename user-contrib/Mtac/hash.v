Require Import mtacore.
Require Import Coq.Program.Program Arith Lists.List.
Import ListNotations.

Import MtacNotations.

Module ListMtactics.

  Definition NotFound : Exception.
    exact exception.
  Qed.

  Definition inlist {A} (x : A) :=
    mfix f (s : list A) :=
      mmatch s with
      | [l r] l ++ r =>
        mtry 
          il <- f l;
          ret (in_or_app l r x (or_introl il))
        with NotFound =>
          ir <- f r;
          ret (in_or_app l r x (or_intror ir))
        end
      | [s'] (x :: s') => ret (in_eq _ _)
      | [y s'] (y :: s') =>
        r <- f s';
        ret (in_cons y _ _ r)
      | _ => raise NotFound
      end.
    
  Program
  Definition find {A} {B : A -> Type} (x : A) : list (sigT B) -> M (B x) :=
    mfix f (s : list (sigT B)) : M (B x) :=
      mmatch s with
      | [l r] l ++ r => 
        mtry 
          _ (f l)
        with NotFound =>
          _ (f r)
        end
      | [y s'] (existT B x y :: s') => _ (ret y)
      | [y s'] (y :: s') => _ (f s')
      | _ => raise NotFound
      end.

End ListMtactics.

Module HashTbl.
  

  Definition t A (P : A -> Type) := (Ref nat * Ref (Array.t (list (sigT P))))%type.

  Definition initial_size := 16.
  Definition inc_factor := 2.
  Definition threshold := 7.

  Definition NotFound : Exception.
    exact exception.
  Qed.

  Definition create A B : M (t A B) :=
    n <- ref 0;
    a <- Array.make initial_size nil;
    ra <- ref a;
    ret (n, ra).

  
  Definition quick_add {A P} (a : Array.t (list (sigT P))) (x : A) (y : P x) : M unit :=
    i <- hash x (Array.length a);
    l <- Array.get a i;
    Array.set a i (existT _ x y  :: l).

  
  Definition iter {A B} (h : t A B) (f : forall x : A, B x -> M unit) : M unit :=
    let (_, ra) := h in
    a <- !ra;
    let size := Array.length a in
    let execute i :=
       l <- Array.get a i;
       fold_right (fun k r => r;;
         match k with
           existT _ x y => f x y
         end) (ret tt) l
    in
    let loop := fix lp n := 
      match n with
      | 0 => ret tt
      | S n' => execute n';; lp n'
      end
    in
    loop size.

  Definition expand {A B} (h : t A B) : M unit :=
    let (load, ra) := h in
    a <- !ra;
    let new_size := Array.length a * inc_factor in
    new_a <- Array.make new_size nil;
    iter h (fun x y=> quick_add new_a x y);;
    ra ::= new_a.
        

  (* There is no order on the elements *)
  Definition to_list {A B} (h : t A B) :=
    rl <- ref nil;
    HashTbl.iter h (fun x y => l <- !rl; rl ::= (existT _ x y :: l));;
    !rl.

  (* debugging function to test how big is the biggest bucket *)
  Definition max_bucket {A B} (h : t A B) :=
    let (_, ra) := h in
    a <- !ra;
    let size := Array.length a in
    let execute i :=
       l <- Array.get a i;
       ret (length l)
    in
    max <- ref 0;
    let loop := fix lp n := 
      match n with
      | 0 => !max
      | S n' => 
        size <- execute n';
        prev <- !max;
        if leb prev size then
          max ::= size;; lp n'
        else
          lp n'
      end
    in
    loop size;;
    !max.
    

  Definition add {A B} (h : t A B) (x : A) (y : B x) :=
    let (rl, ra) := h in
    load <- !rl;
    a <- !ra;
    let size := Array.length a in
    (if (leb (threshold * size) (10 * load)) then
      print "expanding";;
      expand h
    else
      ret tt);;
    a <- !ra;
    quick_add a x y;;
    rl ::= (S load).

  Definition find {A B} (h : t A B) (x : A) : M (B x) :=
    x' <- ret x;
    let (_, ra) := h in
    a <- !ra;
    i <- hash x' (Array.length a);
    l <- Array.get a i;
    mtry
      ListMtactics.find x l
    with ListMtactics.NotFound =>
      raise NotFound
    end.

  
End HashTbl.
