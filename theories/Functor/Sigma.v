Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Functor.
Require Import Blech.Category.Over.

Require Blech.Reflect.

Import CategoryNotations.
Import FunctorNotations.
Import BishopNotations.
Import OverNotations.

Open Scope category_scope.
Open Scope object_scope.
Open Scope bishop_scope.

#[local]
Obligation Tactic := Reflect.category_simpl.

#[program]
Definition Σ [C: Category] {A B: C} (f: C A B): Functor (C/A) (C/B) := {|
  op (u: C/A) := lub _, f ∘ π u ;
  map _ _ x := x ;
|}.

Next Obligation.
Proof.
  rewrite <- compose_assoc.
  rewrite H.
  reflexivity.
Qed.

Next Obligation.
Proof.
  intros ? ? p.
  cbn.
  auto.
Qed.
