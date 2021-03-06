Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Monoid.

Require Import Psatz.

Import BishopNotations.
Import MonoidNotations.

Open Scope bishop_scope.
Open Scope monoid_scope.

#[program]
Definition Circle: Monoid := {|
  S := type nat ;

  e := 0 ;
  app f g := f + g ;
|}.

Solve All Obligations with cbn; lia.

Module CircleNotations.
  Notation "S¹₊" := Circle.
End CircleNotations.
