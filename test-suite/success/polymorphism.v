Polymorphic Inductive prod (A : Type) (B : Type) : Type :=
 pair : A -> B -> prod A B.

Check prod nat nat.
Print Universes.


(* Some tests of sort-polymorphisme *)
Section S.
Variable A:Type.
(*
Definition f (B:Type) := (A * B)%type.
*)
Inductive I (B:Type) : Type := prod : A->B->I B.

Check I nat.

End S.
(*
Check f nat nat : Set.
*)
Check I nat nat : Set.