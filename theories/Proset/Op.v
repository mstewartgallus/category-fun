Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Proset.

Import ProsetNotations.

Reserved Notation "C 'ᵒᵖ'" (at level 1).

#[program]
Definition Op (P: Proset): Proset := {|
  T := P;
  preorder x y := y ⊑ x ;
|}.

Next Obligation.
Proof.
  exists.
  - intro.
    reflexivity.
  - intros ? ? ? p q.
    rewrite q, p.
    reflexivity.
Defined.

Module OpNotations.
  Notation "C 'ᵒᵖ'" := (Op C) : proset_scope.
End OpNotations.
