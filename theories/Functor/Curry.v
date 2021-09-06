Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Functor.
Require Import Blech.Category.Funct.
Require Import Blech.Category.Prod.
Require Blech.Reflect.

Import CategoryNotations.
Import FunctorNotations.
Import BishopNotations.
Import ProdNotations.

Open Scope category_scope.
Open Scope bishop_scope.


#[local]
Obligation Tactic := Reflect.category_simpl.


(* FIXME figure out some form of HOAS ? *)
#[program]
 Definition curry [A B C] (f: Functor (A * B) C): Functor A (Funct B C) := {|
  op (a: A) := {|
                op (b: B) := f (a, b) ;
                map _ _ b := map f ((id a, b): Prod A B (a, _) (a, _)) ;
              |} ;
  map _ _ a b := map f ((a, id b): Prod A B (_, b) (_, b))  ;
|}.

Next Obligation.
Proof.
  exists.
  - intros.
    repeat rewrite map_composes.
    apply map_compat.
    cbn in *.
    split.
    2: reflexivity.
    Reflect.category.
    reflexivity.
  - intros.
    rewrite <- map_id.
    reflexivity.
  - intros ? ? ? ? ?.
    apply map_compat.
    cbn.
    split.
    1: reflexivity.
    assumption.
Qed.

Next Obligation.
Proof.
  intros ? ? ?.
  cbn in *.
  repeat rewrite map_composes.
  cbn in *.
  apply map_compat.
  cbn in *.
  split.
  all: Reflect.category.
  all: reflexivity.
Qed.

Next Obligation.
Proof.
  exists.
  all:cbn.
  - intros.
    repeat rewrite map_composes.
    apply map_compat.
    cbn in *.
    split.
    1: reflexivity.
    Reflect.category.
    reflexivity.
  - intros.
    rewrite <- map_id.
    reflexivity.
  - intros ? ? ? ? p ?.
    cbn.
    apply map_compat.
    split.
    2: reflexivity.
    assumption.
Qed.
