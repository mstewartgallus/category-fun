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

Add Printing Let Bishop.
Existing Instance Bishop_Setoid.
Coercion T: Bishop >-> Sortclass.

Definition hom (A B: Bishop) := { f: A → B | Proper (equiv ==> equiv) f }.

Definition proj1_hom [A B]: hom A B → A → B := @proj1_sig _ _.
Definition proj2_hom [A B]: ∀ (f:hom A B), Proper (equiv ==> equiv) (proj1_hom f) := @proj2_sig _ _.

Coercion proj1_hom: hom >-> Funclass.

Existing Instance proj2_hom.

Definition type (A: Type) := bishop_intro A {| equiv := eq |}.

Create HintDb bishop discriminated.

#[global]
Hint Resolve proj2_hom: bishop.
#[global]
Hint Unfold hom proj1_hom proj2_hom type: bishop.

Module Import BishopNotations.
  Declare Scope bishop_scope.
  Delimit Scope bishop_scope with bishop.

  Bind Scope bishop_scope with Bishop.

  Infix "/~" := bishop_intro: bishop_scope.
End BishopNotations.
