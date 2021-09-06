Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Bool.Bool.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Category.Trv.
Require Import Blech.Category.Mt.
Require Import Blech.Groupoid.
Require Import Blech.Groupoid.Core.
Require Import Blech.Functor.
Require Import Blech.Bicategory.

Require Blech.Reflect.

Import BishopNotations.
Import CategoryNotations.
Import GroupoidNotations.
Import CoreNotations.

Open Scope bishop_scope.
Open Scope category_scope.

Reserved Notation "'I₊'".

#[local]
Obligation Tactic := Reflect.category_simpl.

#[program]
Definition Interval: Bicategory := {|
  Obj := bool ;
  Mor A B := if implb A B then Trv else Mt ;

  id A :=
    match A with
    | true => I
    | false => I
    end ;
  compose A B C :=
    {|
      op _ := _ ;
      map _ _ _ := _ ;
    |} ;
|}.

Next Obligation.
Proof.
  destruct A, B, C.
  all: cbn in *.
  all: try apply I.
  all: destruct H.
  all: contradiction.
Defined.

Next Obligation.
Proof.
  destruct A, B, C.
  all: cbn in *.
  all: try apply I.
  all: destruct H.
  all: cbn in *.
  all: contradiction.
Defined.

Next Obligation.
Proof.
  destruct A, B, C.
  all: cbn in *.
  - exists.
    all: cbn in *.
    all: intros.
    + apply I.
    + apply I.
    + intros ? ? ?.
      apply I.
  - exists.
    all: cbn in *.
    + intros [? ?].
      contradiction.
    + intros [? ?].
      contradiction.
    + intros [? ?].
      contradiction.
  - exists.
    all: cbn in *.
    all: intros.
    + apply I.
    + apply I.
    + intros ? ? ?.
      apply I.
  - exists.
    all: cbn in *.
    + intros [? ?].
      contradiction.
    + intros [? ?].
      contradiction.
    + intros [? ?].
      contradiction.
  - exists.
    all: cbn in *.
    all: intros.
    + apply I.
    + apply I.
    + intros ? ? ?.
      apply I.
  - exists.
    all: cbn in *.
    + intros [? ?].
      contradiction.
    + intros [? ?].
      contradiction.
    + intros [? ?].
      contradiction.
  - exists.
    all: cbn in *.
    all: intros.
    + apply I.
    + apply I.
    + intros ? ? ?.
      apply I.
  - exists.
    all: cbn in *.
    all: intros.
    + apply I.
    + apply I.
    + intros ? ? ?.
      apply I.
Qed.

Next Obligation.
Proof.
  destruct A, B.
  all: cbn in *.
  all: try contradiction.
  all: destruct F.
  all: apply (Category.id (I: Core Trv)).
Qed.

Next Obligation.
Proof.
  destruct A, B.
  all: cbn in *.
  all: destruct F.
  all: apply (Category.id (I: Core Trv)).
Qed.

Next Obligation.
Proof.
  destruct A, B, C, D.
  all: cbn in *.
  all: try contradiction.
  all: apply (Category.id (I: Core Trv)).
Defined.

Module IntervalNotations.
  Notation "'I₊'" := Interval.
End IntervalNotations.
