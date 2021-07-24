Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.

Import CategoryNotations.
Import BishopNotations.

Open Scope morphism_scope.
Open Scope bishop_scope.


Reserved Notation "F ⁻¹" (at level 1).
Reserved Notation "A <~> B" (at level 80).


#[universes(cumulative)]
Class Groupoid := {
  C: Category ;

  invert [A B]: C A B → C B A where "f ⁻¹" := (invert f) ;

  compose_invert_left [A B] (f: C A B): f ⁻¹ ∘ f == id _ ;
  compose_invert_right [A B] (f: C A B): f ∘ f ⁻¹ == id _ ;

  invert_compat [A B]: Proper (equiv ==> equiv) (@invert A B);
}.

Existing Instance C.
Coercion C: Groupoid >-> Category.

Existing Instance invert_compat.

Module Import GroupoidNotations.
  Notation "f ⁻¹" := (invert f) : morphism_scope.
  Notation "A ↔ B" := (C A B) : bishop_scope.
End GroupoidNotations.

Lemma invert_invert {G:Groupoid} {A B} (f: G A B): (f ⁻¹) ⁻¹ == f.
Proof.
  symmetry.
  remember ((f ⁻¹) ⁻¹) as f'.
  rewrite <- (compose_id_left f).
  rewrite <- (compose_invert_left (f ⁻¹)).
  rewrite <- compose_assoc.
  rewrite compose_invert_left.
  rewrite compose_id_right.
  subst.
  reflexivity.
Qed.
