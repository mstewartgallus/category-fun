Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Monoid.
Require Blech.PointedCategory.

Require Blech.Reflect.

Import CategoryNotations.
Import BishopNotations.
Import MonoidNotations.
Import PointedCategory.PointedNotations.

Open Scope category_scope.
Open Scope bishop_scope.
Open Scope monoid_scope.

#[local]
Obligation Tactic := Reflect.category_simpl.

#[program]
Definition Endo (C: PointedCategory.Category): Monoid := {|
  S := C PointedCategory.pt PointedCategory.pt ;

  unit := id _ ;
  app := @compose _ _ _ _ ;
|}.

Next Obligation.
Proof.
  rewrite H, H0.
  reflexivity.
Qed.

Module EndoNotations.
  Notation "Λ₊" := Endo.
End EndoNotations.
