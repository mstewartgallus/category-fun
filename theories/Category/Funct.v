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

#[program]
Definition Funct (K L: Category): Category := {|
  Obj := Functor K L ;
  Mor A B := (∀ x, L (op x) (op x)) /~ {| equiv f g := ∀ x, f x == g x |} ;
  id _ _ := id _ ;
  compose _ _ _ f g _ := f _ ∘ g _ ;
|}.

Next Obligation.
Proof.
  exists.
  all: unfold Reflexive, Symmetric, Transitive; cbn.
  - intros.
    reflexivity.
  - intros ? ? p t.
    symmetry.
    apply (p t).
  - intros ? ? ? p q t.
    rewrite (p t), (q t).
    reflexivity.
Qed.

Next Obligation.
Proof.
  apply compose_compat.
  all:auto.
Qed.
