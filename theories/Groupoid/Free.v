Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Category.Bsh.
Require Import Blech.Groupoid.
Require Import Blech.Functor.
Require Blech.Reflect.

Import CategoryNotations.
Import GroupoidNotations.
Import BishopNotations.

Open Scope category_scope.
Open Scope bishop_scope.


#[local]
Obligation Tactic := Reflect.category_simpl.


#[program]
Definition Free (S: Bishop): Groupoid := {|
  C := {|
    Obj := S ;
    Mor := equiv ;
    Mor_Setoid _ _ := {| equiv _ _ := True |} ;
  |} ;
|}.

Next Obligation.
Proof.
  exists.
  all: exists.
Defined.

Next Obligation.
Proof.
  rewrite H0, H.
  reflexivity.
Defined.

Next Obligation.
Proof.
  symmetry.
  assumption.
Defined.

#[program]
Definition Free_map {A B: Bishop} (f: Bsh A B): Functor (Free A) (Free B) := {|
  op := proj1_sig f ;
  map _ _ f := _ ;
|}.
