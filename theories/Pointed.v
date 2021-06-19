Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Bishop.

Import BishopNotations.

#[universes(cumulative)]
Class Pointed := point { S: Bishop ; pt: S; }.

Arguments S: clear implicits.

Add Printing Let Pointed.
Existing Instance S.
Coercion S: Pointed >-> Bishop.

Class Homomorphic [A B: Pointed] (F: A → B): Prop := Homomorphic_intro {
  Bishop_Homomorphic: Bishop.homomorphic F ;
  map_pt: F pt == pt ;
}.

Coercion Bishop_Homomorphic: Homomorphic >-> Bishop.homomorphic.
Existing Instance Bishop_Homomorphic.

#[program]
Definition hom (A B: Pointed): Type := {f: A -> B | Homomorphic f}.

Definition proj1_hom [A B]: hom A B → A → B := @proj1_sig _ _.
Definition proj2_hom [A B]: ∀ (f:hom A B), Homomorphic (proj1_hom f) := @proj2_sig _ _.

Coercion proj1_hom: hom >-> Funclass.
Coercion proj2_hom: hom >-> Homomorphic.

Existing Instance proj2_hom.

Add Parametric Morphism {A B} (f: hom A B) : (proj1_hom f)
    with signature equiv ==> equiv as hom_mor.
Proof.
  intros.
  apply proj2_hom.
  auto.
Qed.

#[global]
Hint Constructors Homomorphic: Bishop.
#[global]
Hint Resolve Homomorphic_intro: Bishop.

Module Import PointedNotations.
  Declare Scope pointed_scope.
  Delimit Scope pointed_scope with pointed.

  Bind Scope pointed_scope with Pointed.
End PointedNotations.
