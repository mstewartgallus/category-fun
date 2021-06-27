Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Type.Predicate.
Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Functor.
Require Blech.Reflect.

Import CategoryNotations.
Import FunctorNotations.
Import BishopNotations.

Open Scope category_scope.
Open Scope bishop_scope.


#[local]
Obligation Tactic := Reflect.category_simpl.

Definition Natural [C D: Category] (F G: Functor C D): Predicate (∀ x, D (F x) (G x)) :=
  λ α, ∀ {x y} (m: C x y), map G m ∘ α _ == α _ ∘ map F m.

Definition proj1_NatTrans [C D: Category] [F G: Functor C D]
  : Natural F G → ∀ x, D (F x) (G x) := @proj1_sig _ _.

#[program]
Definition Funct (K L: Category): Category := {|
  Obj := Functor K L ;
  Mor A B := (Natural A B) /~ {| equiv f g := ∀ x, f x == g x |} ;
  id A _ := id _ ;
  compose _ _ _ f g _ := f _  ∘ g _  ;
|}.

Next Obligation.
Proof.
  exists.
  all: unfold Reflexive, Symmetric, Transitive; cbn.
  - intros.
    reflexivity.
  - intros ? ? p ?.
    symmetry.
    apply (p _).
  - intros ? ? ? p q ?.
    rewrite (p _), (q _).
    reflexivity.
Qed.

Next Obligation.
Proof.
  intros ? ? ?.
  Reflect.category.
  reflexivity.
Qed.

Next Obligation.
Proof.
  intros ? ? ?.
  destruct f, g.
  cbn in *.
  repeat rewrite compose_assoc.
  rewrite n.
  repeat rewrite <- compose_assoc.
  apply compose_compat.
  1: reflexivity.
  rewrite n0.
  reflexivity.
Qed.

Next Obligation.
Proof.
  intros ? ? p ? ? q ?.
  cbn in *.
  rewrite (p _), (q _).
  reflexivity.
Qed.
