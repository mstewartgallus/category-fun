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

Definition hom (A B: Bishop) (f: A → B) := Proper (equiv ==> equiv) f.

Definition hom_predicate [A B: Bishop] (f:A → B) (h:hom A B f): Proper (equiv ==> equiv) f.
  intros.
  apply h.
Defined.
Existing Instance hom_predicate.

Definition type (A: Type) := bishop_intro A {| equiv := eq |}.

Create HintDb bishop discriminated.

#[global]
Hint Resolve hom_predicate: bishop.
#[global]
Hint Unfold hom type: bishop.

Module Import BishopNotations.
  Declare Scope bishop_scope.
  Delimit Scope bishop_scope with bishop.

  Bind Scope bishop_scope with Bishop.

  Infix "/~" := bishop_intro: bishop_scope.
End BishopNotations.
