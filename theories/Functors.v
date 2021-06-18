Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Functor.
Require Import Blech.Product.
Require Blech.Reflect.

Import CategoryNotations.
Import FunctorNotations.
Import BishopNotations.
Import ProductNotations.

Open Scope category_scope.
Open Scope bishop_scope.


Obligation Tactic := Reflect.category_simpl.


(* FIXME figure out some form of HOAS ? *)
#[program]
 Definition curry [A B C] (f: Funct (A * B) C): Funct A (Funct B C) := {|
  op (a: A) := {|
                op (b: B) := f (a, b) ;
                map _ _ b := map f ((id a, b): Prod A B (a, _) (a, _)) ;
              |} ;
  map _ _ a b := map f ((a, id b): Prod A B (_, b) (_, b))  ;
|}.

Next Obligation.
Proof.
  repeat rewrite map_composes.
  apply map_compat.
  cbn in *.
  split.
  2: reflexivity.
  Reflect.category.
  reflexivity.
Qed.

Next Obligation.
Proof.
  rewrite map_id.
  reflexivity.
Qed.

Next Obligation.
Proof.
  apply map_compat.
  cbn.
  split.
  1: reflexivity.
  assumption.
Qed.

Next Obligation.
Proof.
  repeat rewrite map_composes.
  apply map_compat.
  cbn in *.
  split.
  1: reflexivity.
  Reflect.category.
  reflexivity.
Qed.

Next Obligation.
Proof.
  rewrite map_id.
  reflexivity.
Qed.

Next Obligation.
Proof.
  apply map_compat.
  cbn.
  split.
  2: reflexivity.
  assumption.
Qed.

#[program]
 Definition id A: Funct A A :=
  {|
  op x := x ;
  map _ _ x := x ;
  |}.

#[program]
 Definition compose [A B C] (f: Funct B C) (g: Funct A B): Funct A C :=
  {|
  op x := f (g x) ;
  map _ _ x := map f (map g x)
  |}.

Next Obligation.
Proof.
  repeat rewrite map_composes.
  reflexivity.
Qed.

Next Obligation.
Proof.
  repeat rewrite map_id.
  reflexivity.
Qed.

Next Obligation.
Proof.
  rewrite H.
  reflexivity.
Qed.
