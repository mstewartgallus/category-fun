Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Bishop.

Import BishopNotations.

#[universes(cumulative)]
Class Pointed := point { S: Bishop ; pt: S; }.

Arguments S: clear implicits.

Module Import PointedNotations.
  Declare Scope pointed_scope.
  Delimit Scope pointed_scope with pointed.

  Bind Scope pointed_scope with Pointed.

  Add Printing Let Pointed.
  Existing Instance S.
  Coercion S: Pointed >-> Bishop.
End PointedNotations.
