Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Functor.
Require Import Blech.Category.Funct.
Require Blech.Reflect.

Import CategoryNotations.
Import FunctorNotations.
Import BishopNotations.

Open Scope category_scope.
Open Scope bishop_scope.


#[local]
Obligation Tactic := Reflect.category_simpl.

#[program]
 Definition compose [A B C] (f: Functor B C) (g: Functor A B): Functor A C :=
  {|
  op x := f (g x) ;
  map _ _ x := map f (map g x)
  |}.

Next Obligation.
Proof.
  repeat rewrite map_composes.
  reflexivity.
Qed.

Next Obligation.
Proof.
  repeat rewrite map_id.
  reflexivity.
Qed.

Next Obligation.
Proof.
  rewrite H.
  reflexivity.
Qed.
