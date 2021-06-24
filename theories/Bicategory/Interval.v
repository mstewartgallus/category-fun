Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Bool.Bool.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Category.Trv.
Require Import Blech.Category.Mt.
Require Import Blech.Functor.
Require Import Blech.Bicategory.

Require Blech.Reflect.

Import BishopNotations.
Import CategoryNotations.

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
      op '(x, y) := _ ;
      map '(_, _) '(_, _) '(_, _) := _ ;
    |} ;
|}.

Next Obligation.
Proof.
  destruct A, B, C.
  all: cbn in *.
  all: try contradiction.
  all: exists.
Defined.

Next Obligation.
Proof.
  destruct A, B, C.
  all: cbn in *.
  all: try contradiction.
  all: exists.
Defined.

Next Obligation.
Proof.
  destruct A, B, C.
  all: cbn in *.
  all: try destruct X.
  all: try destruct Y.
  all: try destruct Z.
  all: try destruct x.
  all: try destruct y.
  all: try contradiction.
  all: exists.
Qed.

Next Obligation.
Proof.
  destruct A, B, C, A0.
  all: cbn in *.
  all: try contradiction.
  all: exists.
Qed.

Next Obligation.
Proof.
  destruct A, B, C, A0.
  all: cbn in *.
  all: try contradiction.
  all: exists.
Qed.

Next Obligation.
Proof.
  destruct A, B.
  all: cbn in *.
  all: try contradiction.
  all: destruct F.
  all: exists I I.
  all: cbn.
  all: exists.
Qed.

Next Obligation.
Proof.
  destruct A, B.
  all: cbn in *.
  all: destruct F.
  all: exists I I.
  all: cbn.
  all: exists.
Qed.

Next Obligation.
Proof.
  destruct A, B, C, D.
  all: cbn in *.
  all: try contradiction.
  all: exists I I.
  all: cbn.
  all: exists.
Qed.

Module IntervalNotations.
  Notation "'I₊'" := Interval.
End IntervalNotations.
