Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Bool.Bool.

Require Import Blech.Bishop.
Require Import Blech.Functor.
Require Import Blech.Monoidal.
Require Import Blech.Category.
Require Import Blech.Category.Interval.
Require Import Blech.Category.Prod.

Require Blech.Reflect.

Import BishopNotations.
Import FunctorNotations.
Import CategoryNotations.
Import MonoidalNotations.
Import ProdNotations.

Open Scope bishop_scope.
Open Scope category_scope.

#[local]
Obligation Tactic := Reflect.category_simpl.

#[program]
Definition Interval: Category := {|
  C := Interval ;

  pt := true ;
  app :=
    {|
      op '(x, y) := andb x y ;
    |} ;
|}.

Next Obligation.
Proof.
  destruct X.
  destruct A as [A A'].
  destruct B as [B B'].
  destruct A, A', B, B'.
  all: cbn in *.
  all: try contradiction.
  all: exists.
Qed.
