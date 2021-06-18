Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Groupoid.
Require Blech.Reflect.

Import CategoryNotations.
Import GroupoidNotations.
Import BishopNotations.

Open Scope category_scope.
Open Scope bishop_scope.


#[local]
Obligation Tactic := Reflect.category_simpl.


#[program]
Definition Dis (S: Bishop): Groupoid := {|
  C := {|
    Obj := S ;
    Mor A B := (A == B) /~ {| equiv _ _ := True |} ;
  |} ;
|}.

Next Obligation.
Proof.
  exists.
  all: exists.
Defined.

Next Obligation.
Proof.
  rewrite H0, H.
  reflexivity.
Defined.

Next Obligation.
Proof.
  symmetry.
  assumption.
Defined.
