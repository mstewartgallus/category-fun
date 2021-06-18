Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.ZArith.ZArith.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Groupoid.
Require Import Blech.Monoid.
Require Import Blech.Group.
Require Blech.PointedGroupoid.
Require Blech.Monoids.
Require Blech.Pointed.
Require Blech.Bishops.

Require Blech.Reflect.
Require Psatz.

Import BishopNotations.
Import CategoryNotations.
Import MonoidNotations.
Import GroupNotations.
Import Pointed.PointedNotations.
Import PointedGroupoid.PointedNotations.

Open Scope category_scope.
Open Scope bishop_scope.
Open Scope monoid_scope.
Open Scope group_scope.

Import Monoid.
Import Group.

Local Open Scope Z_scope.

#[program]
 Definition Trivial: Group := {|
  M := Monoids.Trivial ;
  invert _ := I ;
|}.

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

Obligation Tactic := Reflect.category_simpl.

#[program]
 Definition Λ (C: PointedGroupoid.Groupoid): Group := {|
  M := {|
        S := C PointedGroupoid.pt PointedGroupoid.pt ;
        unit := id _ ;
        app := @compose _ _ _ _ ;
      |} ;
  invert := @Groupoid.invert _ _ _ ;
                                                     |}.

Import Groupoid.

Next Obligation.
Proof.
  rewrite H, H0.
  reflexivity.
Qed.

Next Obligation.
Proof.
  apply compose_invert_left.
Qed.

Next Obligation.
Proof.
  apply compose_invert_right.
Qed.

Next Obligation.
Proof.
  rewrite H.
  reflexivity.
Qed.

Module Export GroupsNotations.
  Notation "S¹" := Circle.
End GroupsNotations.
