Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Bool.Bool.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Groupoid.
Require Import Blech.Groupoid.Core.
Require Import Blech.Category.Trv.
Require Import Blech.Functor.
Require Import Blech.Bicategory.

Require Blech.Reflect.

Import BishopNotations.
Import CategoryNotations.
Import GroupoidNotations.

Open Scope bishop_scope.
Open Scope category_scope.

#[local]
Obligation Tactic := Reflect.category_simpl.

#[program]
Definition UndirectedInterval: Bicategory := {|
  Obj := bool ;
  Mor _ _ := Trv ;

  id _ := I ;
  compose _ _ _ :=
    {|
      op _ := I ;
      map _ _ _ := I ;
    |} ;
|}.

Next Obligation.
Proof.
  exists.
  all: cbn in *.
  all: intros.
  - apply I.
  - apply I.
  - intros ? ? ?.
    apply I.
Defined.

Next Obligation.
Proof.
  destruct F.
  apply (Category.id (I: Core Trv)).
Defined.

Next Obligation.
Proof.
  destruct F.
  apply (Category.id (I: Core Trv)).
Defined.

Next Obligation.
Proof.
  apply (Category.id (I: Core Trv)).
Defined.
