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

#[program]
Definition hom (A B: Pointed): Type := {f:hom A B | f pt == pt}.

Module Import PointedNotations.
  Declare Scope pointed_scope.
  Delimit Scope pointed_scope with pointed.

  Bind Scope pointed_scope with Pointed.
End PointedNotations.
