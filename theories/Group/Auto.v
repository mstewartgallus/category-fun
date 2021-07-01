Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Groupoid.
Require Import Blech.Monoid.
Require Import Blech.Group.
Require Blech.PointedGroupoid.
Require Blech.Pointed.

Require Blech.Reflect.

Import BishopNotations.
Import CategoryNotations.
Import GroupoidNotations.
Import MonoidNotations.
Import GroupNotations.
Import Pointed.PointedNotations.
Import PointedGroupoid.PointedNotations.

Open Scope category_scope.
Open Scope bishop_scope.
Open Scope monoid_scope.
Open Scope group_scope.

#[local]
Obligation Tactic := Reflect.category_simpl.

#[program]
Definition Λ (C: PointedGroupoid.Groupoid): Group := {|
  M := {|
        S := C PointedGroupoid.pt PointedGroupoid.pt ;
        e := id _ ;
        app := @compose _ _ _ _ ;
      |} ;
  invert := @Groupoid.invert _ _ _ ;
|}.

Next Obligation.
Proof.
  apply compose_invert_left.
Qed.

Next Obligation.
Proof.
  apply compose_invert_right.
Qed.
