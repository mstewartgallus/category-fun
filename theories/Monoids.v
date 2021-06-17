Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Monoid.
Require Blech.Pointed.
Require Blech.Bishops.

Require Blech.Reflect.
Require Psatz.

Import CategoryNotations.
Import BishopNotations.
Import MonoidNotations.
Import Pointed.PointedNotations.

Open Scope category_scope.
Open Scope bishop_scope.
Open Scope monoid_scope.

#[program]
Definition Trivial: Monoid := {|
  S := Bishops.True ;
  unit := I ;
  app _ _ := I ;
|}.

#[program]
 Definition OrBool: Monoid := {|
  S := Bishops.simple bool ;

  unit := false ;
  app := orb ;
|}.

Next Obligation.
Proof.
  destruct f, g, h.
  all: cbn in *.
  all: reflexivity.
Qed.

Next Obligation.
Proof.
  destruct f.
  all: cbn in *.
  all: reflexivity.
Qed.

#[program]
 Definition AndBool: Monoid := {|
  S := Bishops.simple bool ;

  unit := true ;
  app := andb ;
|}.

Next Obligation.
Proof.
  destruct f, g, h.
  all: cbn in *.
  all: reflexivity.
Qed.

Next Obligation.
Proof.
  destruct f.
  all: cbn in *.
  all: reflexivity.
Qed.


#[program]
Definition Circle: Monoid := {|
  S := Bishops.simple nat ;

  unit := 0 ;
  app f g := f + g ;
|}.

Solve All Obligations with cbn; Psatz.lia.


Obligation Tactic := Reflect.category_simpl.

#[program]
Definition Endo (C: Pointed.Category): Monoid := {|
  S := C (Pointed.pt C) (Pointed.pt C) ;

  unit := id _ ;
  app := @compose _ _ _ _ ;
|}.

Next Obligation.
Proof.
  rewrite H, H0.
  reflexivity.
Qed.


Module MonoidsNotations.
  Notation "Λ₊" := Endo.
  Notation "S¹₊" := Circle.
End MonoidsNotations.
