Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Bool.Bool.

Require Import Blech.Bishop.
Require Import Blech.Bishop.Trv.
Require Import Blech.Category.
Require Import Blech.Groupoid.
Require Import Blech.Group.

Require Blech.Reflect.

Import BishopNotations.
Import CategoryNotations.
Import GroupoidNotations.
Import GroupNotations.

Open Scope bishop_scope.
Open Scope category_scope.
Open Scope monoid_scope.
Open Scope group_scope.

#[program]
Definition Interval: Groupoid := {|
  C := {|
        Obj := bool ;
        Mor _ _ := trv ;

        id _ := I ;
        compose _ _ _ _ _ := I ;
      |} ;
  Groupoid.invert _ _ _ := I ;
|}.
