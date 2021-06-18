Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Category.Monic.
Require Import Blech.Category.Epic.

Require Blech.Reflect.

Import BishopNotations.
Import CategoryNotations.
Import MonicNotations.

Open Scope category_scope.
Open Scope bishop_scope.

Obligation Tactic := Reflect.category_simpl.

Record zigzag [K: Category] [A B: K] (F: K A B) := {
  pull: K ;
  epi: Epic K A pull ;
  mono: K ₊ pull B ;
  commutes: proj1_sig mono ∘ proj1_sig epi == F
}.

Arguments pull [K A B F].
Arguments epi [K A B F].
Arguments mono [K A B F].
Arguments commutes [K A B F].

#[local]
 #[program]
 Definition mor [K: Category] [A B: K] [F: K A B] (X Y: zigzag F) :=
  {f: K (pull X) (pull Y) |
    proj1_sig (epi Y) == f ∘ proj1_sig (epi X) ∧
    proj1_sig (mono Y) ∘ f == proj1_sig (mono X)} /~ {| equiv x y := proj1_sig x == proj1_sig y |}.

Next Obligation.
Proof.
  exists.
  - intros ?.
    reflexivity.
  - intros ? ? ?.
    symmetry.
    auto.
  - intros ? ? ? p q.
    rewrite p, q.
    reflexivity.
Qed.

#[program]
Definition Epimono [K: Category] [A B: K] (F: K A B) : Category := {|
  Obj := zigzag F ;
  Mor A B := mor A B ;

  id _ := id _ ;
  compose _ _ _ := @compose _ _ _ _ ;
|}.

Next Obligation.
Proof.
  split.
  - rewrite e1.
    rewrite <- compose_assoc.
    rewrite e.
    reflexivity.
  - rewrite compose_assoc.
    rewrite e2.
    rewrite <- e0.
    reflexivity.
Qed.

Next Obligation.
Proof.
  rewrite H, H0.
  reflexivity.
Qed.
