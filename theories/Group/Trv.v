Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Group.
Require Import Blech.Monoid.
Require Import Blech.Monoid.Trv.
Require Blech.Pointed.
Require Blech.Bishops.

Require Blech.Reflect.

Import BishopNotations.
Import CategoryNotations.
Import MonoidNotations.
Import GroupNotations.

Open Scope category_scope.
Open Scope bishop_scope.
Open Scope monoid_scope.
Open Scope group_scope.

#[program]
Definition Trv: Group := {|
  M := Trv ;
  invert _ := I ;
|}.
