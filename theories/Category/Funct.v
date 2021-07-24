Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

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

Definition Natural {C D: Category} {F G: Functor C D} (α: ∀ x, D (F x) (G x)): Prop :=
  ∀ {x y} (m: C x y), map G m ∘ α _ == α _ ∘ map F m.
Existing Class Natural.

Definition natural {C D: Category} {F G: Functor C D} {α: ∀ x, D (F x) (G x)} `{N:Natural C D F G α}:
  ∀ {x y} (m: C x y), map G m ∘ α _ == α _ ∘ map F m := N.

#[program]
Definition Funct (K L: Category): Category := {|
  Obj := Functor K L ;
  Mor A B := { f | Natural f } ;
  Mor_Setoid _ _ := {| equiv f g := ∀ x, f x == g x |} ;
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
  repeat rewrite compose_assoc.
  rewrite natural.
  repeat rewrite <- compose_assoc.
  apply compose_compat.
  1: reflexivity.
  rewrite natural.
  reflexivity.
Qed.

Next Obligation.
Proof.
  intros ? ? p ? ? q ?.
  cbn in *.
  rewrite (p _), (q _).
  reflexivity.
Qed.
