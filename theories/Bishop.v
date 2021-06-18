Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.


Reserved Notation "A /~ B" (at level 40).


(*
We need Bishop sets (AKA Setoids) not Coq's Type to make the Yoneda
embedding on presheafs work properly.

FIXME: This probably isn't quite right and not an "exact" or "Abelian"
category.
*)
#[universes(cumulative)]
Class Bishop := bishop_intro { T: Type ; Bishop_Setoid: Setoid T ; }.

Arguments T: clear implicits.

Module Import BishopNotations.
  Declare Scope bishop_scope.
  Delimit Scope bishop_scope with bishop.

  Bind Scope bishop_scope with Bishop.

  Add Printing Let Bishop.
  Existing Instance Bishop_Setoid.
  Coercion T: Bishop >-> Sortclass.
  Infix "/~" := bishop_intro: bishop_scope.
End BishopNotations.

Definition type (A: Type) := bishop_intro A {| equiv := eq |}.
