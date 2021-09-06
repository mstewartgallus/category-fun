Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Type.Predicate.
Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Category.Prod.
Require Import Blech.Groupoid.
Require Import Blech.Groupoid.Core.
Require Import Blech.Bicategory.
Require Import Blech.Functor.
Require Import Blech.Category.Funct.
Require Blech.Reflect.
Require Blech.Functor.Id.
Require Blech.Functor.Curry.
Require Blech.Functor.Compose.

Import BishopNotations.
Import CategoryNotations.
Import ProdNotations.

Open Scope category_scope.
Open Scope bishop_scope.

#[local]
Obligation Tactic := Reflect.category_simpl.

#[program]
 #[local]
Definition godement {X Y Z}: Functor (Funct Y Z * Funct X Y * X) Z :=
 {|
  op '(F, G, x) := F (G x) ;
  map '(A, B, C) '(X, Y, Z) '(F, G, x) := F _ ∘ map A (G _ ∘ map B x) ;
 |}.

Next Obligation.
Proof.
  exists.
  all: cbn.
  - intros  [[? []]] [[? []]] [[? []]] [[[] []]] [[[] []]].
    cbn in *.
    repeat rewrite <- Category.compose_assoc.
    apply compose_compat.
    1: reflexivity.
    repeat rewrite <- map_composes.
    repeat rewrite Category.compose_assoc.
    apply compose_compat.
    2: reflexivity.
    repeat rewrite map_composes.
    rewrite natural.
    repeat rewrite <- Category.compose_assoc.
    repeat rewrite map_composes.
    apply compose_compat.
    1: reflexivity.
    apply map_compat.
    repeat rewrite <- Category.compose_assoc.
    apply compose_compat.
    1: reflexivity.
    rewrite n2.
    reflexivity.
  - intros [[]].
    cbn in *.
    repeat rewrite <- map_composes.
    repeat rewrite map_id.
    repeat rewrite Category.compose_id_right.
    reflexivity.
  - intros [[]] [[]] [[[] []]] [[[] []]] [[p q] r].
    cbn in *.
    rewrite p, q, r.
    reflexivity.
Qed.

#[program]
Definition Cat: Bicategory := {|
  Obj := Category ;
  Mor := Funct ;

  id := Id.id ;
  compose A B C := Curry.curry (@godement A B C) ;

  compose_id_left A B F :=
    {|
      to _ := Category.id _ ;
      from _ := Category.id _ ;
    |} ;
  compose_id_right A B F :=
    {|
      to _ := Category.id _ ;
      from _ := Category.id _ ;
    |} ;

  compose_assoc _ _ _ _ F G H :=
    {|
      to _ := Category.id _ ;
      from _ := Category.id _  ;
    |} ;
|}.

Next Obligation.
Proof.
  intros ? ? m.
  cbn in *.
  Reflect.category.
  reflexivity.
Qed.

Next Obligation.
Proof.
  intros ? ? m.
  cbn in *.
  Reflect.category.
  reflexivity.
Qed.

Next Obligation.
Proof.
  intros ? ? m.
  cbn in *.
  repeat rewrite Category.compose_id_right.
  repeat rewrite Category.compose_id_left.
  reflexivity.
Qed.

Next Obligation.
Proof.
  intros ? ? m.
  cbn in *.
  repeat rewrite Category.compose_id_right.
  repeat rewrite Category.compose_id_left.
  reflexivity.
Qed.

Next Obligation.
Proof.
  intros ? ? m.
  cbn in *.
  repeat rewrite Category.compose_id_right.
  repeat rewrite Category.compose_id_left.
  reflexivity.
Qed.

Next Obligation.
Proof.
  intros ? ? m.
  cbn in *.
  repeat rewrite Category.compose_id_right.
  repeat rewrite Category.compose_id_left.
  reflexivity.
Qed.
