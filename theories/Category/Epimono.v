Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Monic.
Require Import Blech.Monic.Mono.
Require Import Blech.Category.Epic.

Require Blech.Reflect.

Import BishopNotations.
Import CategoryNotations.
Import MonoNotations.

Open Scope category_scope.
Open Scope bishop_scope.

#[local]
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
    proj1_sig (mono Y) ∘ f == proj1_sig (mono X)}.

#[program]
Definition Epimono [K: Category] [A B: K] (F: K A B) : Category := {|
  Obj := zigzag F ;
  Mor A B := mor A B ;
  Mor_Setoid _ _ := {| equiv x y := proj1_sig x == proj1_sig y |} ;

  id _ := id _ ;
  compose _ _ _ := @compose _ _ _ _ ;
|}.

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

Next Obligation.
Proof.
  destruct x as [x p], x0 as [y q].
  cbn in *.
  destruct p as [p p'].
  destruct q as [q q'].
  split.
  - rewrite p.
    rewrite <- compose_assoc.
    rewrite q.
    reflexivity.
  - rewrite compose_assoc.
    rewrite p'.
    rewrite <- q'.
    reflexivity.
Qed.

Next Obligation.
Proof.
  intros ? ? p ? ? q.
  cbn in *.
  rewrite p, q.
  reflexivity.
Qed.
