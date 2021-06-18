Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.ZArith.ZArith.

Require Import Blech.Bishop.
Require Import Blech.Monoid.
Require Import Blech.Group.

Require Psatz.

Import BishopNotations.
Import MonoidNotations.
Import GroupNotations.

Open Scope bishop_scope.
Open Scope monoid_scope.
Open Scope group_scope.
Open Scope Z_scope.

#[program]
 Definition Circle: Group := {|
  M := {|
        S := Z /~ {| equiv := eq |} ;

        unit := 0 ;
        app f g := f + g ;
      |} ;
  invert x := -x;
|}.

Solve All Obligations with cbn; Psatz.lia.

Module Export CircleNotations.
  Notation "S¹" := Circle.
End CircleNotations.
