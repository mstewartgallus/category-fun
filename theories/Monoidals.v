Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Bool.Bool.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Functor.
Require Import Blech.Product.
Require Import Blech.Monoidal.
Require Import Blech.Categories.

Require Blech.Reflect.

Import BishopNotations.
Import FunctorNotations.
Import CategoryNotations.
Import CategoriesNotations.
Import MonoidalNotations.
Import ProductNotations.

Open Scope bishop_scope.
Open Scope category_scope.

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
  destruct b1, b2, b, b0.
  all: cbn in *.
  all: try contradiction.
  all: exists.
Qed.
