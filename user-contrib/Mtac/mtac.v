Require Export mtacore.

Export MtacNotations.

Obligation Tactic := idtac.

(* This coercion allows to avoid the explicit call to eval, but it is 
   inconvenient for typechecking. *)
(* Coercion eval : M >-> Funclass. *)

(** Tactic to unify two terms [x] and [y]. *)
Definition unify {A} (x y : A) (P : A -> Type) (f : x = y -> P y) : M (P x) :=
    a <- mmatch x as x' return M (x = x' -> _) with 
           | y => ret (fun H => f H)
         end;
    retS (a (eq_refl _)).

