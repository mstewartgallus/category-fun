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

Definition homomorphic [A B:Bishop] (f: T A → T B) := ∀ x y, x == y → f x == f y.
Existing Class homomorphic.

Definition hom (A B: Bishop) := { f: A → B | homomorphic f }.

Definition proj1_hom [A B]: hom A B → A → B := @proj1_sig _ _.
Definition proj2_hom [A B]: ∀ (f:hom A B), homomorphic (proj1_hom f) := @proj2_sig _ _.

Coercion proj1_hom: hom >-> Funclass.
Coercion proj2_hom: hom >-> homomorphic.

Existing Instance proj2_hom.

Add Parametric Morphism {A B} (f: hom A B) : (proj1_hom f)
    with signature equiv ==> equiv as hom_mor.
Proof.
  intros.
  apply proj2_hom.
  auto.
Qed.

Module Import BishopNotations.
  Declare Scope bishop_scope.
  Delimit Scope bishop_scope with bishop.

  Bind Scope bishop_scope with Bishop.

  Infix "/~" := bishop_intro: bishop_scope.
End BishopNotations.

Definition type (A: Type) := bishop_intro A {| equiv := eq |}.
