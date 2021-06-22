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
Definition compose {X Y Z} (F: Functor Y Z) (G: Functor X Y): Functor X Z :=
  {|
    op x := F (G x) ;
    map _ _ x := map F (map G x) ;
  |}.

Next Obligation.
Proof.
  repeat rewrite <- map_composes.
  Reflect.category.
  reflexivity.
Qed.

Next Obligation.
Proof.
  repeat rewrite <- map_id.
  Reflect.category.
  reflexivity.
Qed.

Next Obligation.
Proof.
  intros ? ? p.
  apply map_compat.
  apply map_compat.
  auto.
Qed.
