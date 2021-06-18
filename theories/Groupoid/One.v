Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Bool.Bool.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Groupoid.
Require Import Blech.Monoid.
Require Import Blech.Group.
Require Import Blech.Category.One.
Require Blech.PointedGroupoid.
Require Blech.Pointed.

Require Blech.Reflect.

Import BishopNotations.
Import CategoryNotations.
Import GroupoidNotations.
Import Pointed.PointedNotations.
Import MonoidNotations.
Import GroupNotations.
Import OneNotations.

Open Scope bishop_scope.
Open Scope category_scope.
Open Scope monoid_scope.
Open Scope group_scope.

#[program]
Definition 𝑩 (G: Group): PointedGroupoid.Groupoid := {|
  PointedGroupoid.G := {|
                        C := 𝑩₊ G ;
                        Groupoid.invert _ _ := Group.invert ;
                      |} ;
  PointedGroupoid.pt := I ;
|}.

Next Obligation.
Proof.
  apply app_invert_left.
Qed.

Next Obligation.
Proof.
  apply app_invert_right.
Qed.

Next Obligation.
Proof.
  rewrite H.
  reflexivity.
Qed.
