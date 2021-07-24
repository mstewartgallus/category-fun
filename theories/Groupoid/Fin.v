Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Vectors.Fin.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Groupoid.
Require Blech.Reflect.

Import CategoryNotations.
Import GroupoidNotations.
Import BishopNotations.

Open Scope category_scope.
Open Scope bishop_scope.


#[local]
Obligation Tactic := Reflect.category_simpl.

(* I need a better name perhaps *)
#[program]
Definition Fin (n: nat): Groupoid := {|
  C := {|
    Obj := t n ;
    Mor A B := (A = B) ;
    Mor_Setoid _ _ := {| equiv _ _ := True |} ;
  |} ;
|}.

Next Obligation.
Proof.
  exists.
  all: exists.
Defined.
