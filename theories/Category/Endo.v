Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Category.
Require Blech.Bicategory.

#[local]
Obligation Tactic := Reflect.category_simpl.

Definition Endo (C: Bicategory) (c: C): Category := C c c.

Module EndoNotations.
  Notation "Λ₊" := Endo : category_scope.
End EndoNotations.
