Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.

Import CategoryNotations.
Import BishopNotations.

Open Scope category_scope.
Open Scope bishop_scope.


Reserved Notation "F ⁻¹" (at level 1).
Reserved Notation "A <~> B" (at level 80).


#[universes(cumulative)]
Class Groupoid := {
  C: Category ;

  invert [A B]: C A B → C B A where "f ⁻¹" := (invert f) ;

  compose_invert_left [A B] (f: C A B): f ⁻¹ ∘ f == id _ ;
  compose_invert_right [A B] (f: C A B): f ∘ f ⁻¹ == id _ ;

  invert_compat [A B] (f f': C A B):
    f == f' → f ⁻¹ ==  f' ⁻¹ ;
}.

Existing Instance C.
Coercion C: Groupoid >-> Category.

Add Parametric Morphism [G: Groupoid] A B : (@invert G A B)
    with signature equiv ==> equiv as invert_mor.
Proof.
  intros ? ? p.
  apply invert_compat.
  auto.
Qed.

Module GroupoidNotations.
  Notation "f ⁻¹" := (invert f).
  Notation "A ↔ B" := (C A B) : category_scope.
  Notation "A <~> B" := (C A B) : category_scope.
End GroupoidNotations.
