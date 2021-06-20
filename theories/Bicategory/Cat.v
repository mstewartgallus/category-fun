Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

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

Import BishopNotations.
Import CategoryNotations.
Import ProdNotations.

Open Scope category_scope.
Open Scope bishop_scope.

#[local]
Obligation Tactic := Reflect.category_simpl.

#[program]
 #[local]
Definition godement {X Y Z}: Functor (Funct Y Z * Funct X Y) (Funct X Z) :=
 {|
  op '(F, G) := {|
                 op x := F (G x) ;
                 map _ _ x := map F (map G x) ;
               |} ;
  map '(A, C) '(B, D) '(F, G) x := map B (G x) ∘ F _ ;
  |}.

Next Obligation.
Proof.
  repeat rewrite <- map_composes.
  Reflect.category.
  reflexivity.
Qed.

Next Obligation.
Proof.
  repeat rewrite map_id.
  reflexivity.
Qed.

Next Obligation.
Proof.
  intros ? ? p.
  apply map_compat.
  apply map_compat.
  assumption.
Qed.

Next Obligation.
Proof.
  intros ? ? ?.
  cbn in *.
  repeat rewrite Category.compose_assoc.
  repeat rewrite map_composes.
  repeat rewrite (proj2_sig F).
  repeat rewrite <- Category.compose_assoc.
  apply compose_compat.
  1: reflexivity.
  repeat rewrite map_composes.
  apply map_compat.
  repeat rewrite (proj2_sig G).
  reflexivity.
Qed.

Next Obligation.
Proof.
  destruct X0, Y0, Z0.
  destruct x, y.
  cbn in *.
  repeat rewrite <- map_composes.
  repeat rewrite <- Category.compose_assoc.
  apply compose_compat.
  1: reflexivity.
  repeat rewrite Category.compose_assoc.
  apply compose_compat.
  2: reflexivity.
  rewrite (proj2_sig fst2).
  reflexivity.
Qed.

Next Obligation.
Proof.
  rewrite map_id.
  Reflect.category.
  reflexivity.
Qed.

Next Obligation.
Proof.
  intros ? ? p ?.
  destruct p.
  cbn.
  apply compose_compat.
  - apply map_compat.
    apply (H0 _).
  - apply (H _).
Qed.

#[program]
Definition Cat: Bicategory := {|
  Obj := Category ;
  Mor := Funct ;

  id := Id.id ;
  compose := @godement ;

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
