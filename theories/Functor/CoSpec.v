Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Functor.
Require Import Blech.Category.Bsh.
Require Import Blech.Category.Funct.
Require Import Blech.Category.Prod.
Require Import Blech.Category.PSh.
Require Import Blech.Category.CoPSh.
Require Import Blech.Category.Op.
Require Import Blech.Functor.Yo.
Require Blech.Reflect.

Import CategoryNotations.
Import FunctorNotations.
Import BishopNotations.
Import ProdNotations.
Import OpNotations.

Open Scope category_scope.
Open Scope bishop_scope.

#[local]
Obligation Tactic := Reflect.category_simpl.

#[program]
Definition CoSpec [C: Category] (A: PSh C): CoPSh C := {|
  op (u: C) := (∀ x, Bsh (A x) (Yo C u x)) /~ {| equiv f g := ∀ t, f t == g t |} ;
  map _ _ x y _ z := x ∘ y _ z ;
|}.

Next Obligation.
Proof.
  admit.
Admitted.

Next Obligation.
Proof.
  intros ? ? p.
  apply compose_compat.
  1: reflexivity.
  apply (proj2_sig (y o1)).
  auto.
Qed.

Next Obligation.
Proof.
  intros ? ? ? ? ?.
  cbn in *.
  apply compose_compat.
  1: reflexivity.
  apply H.
Qed.

Next Obligation.
Proof.
  intros ? ? p ? ? ?.
  cbn in *.
  apply compose_compat.
  2: reflexivity.
  apply p.
Qed.
