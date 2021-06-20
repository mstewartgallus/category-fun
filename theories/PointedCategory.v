Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Functor.
Require Import Blech.Category.Funct.

Import CategoryNotations.
Import BishopNotations.

Open Scope category_scope.
Open Scope bishop_scope.

#[local]
Obligation Tactic := Reflect.category_simpl.

#[universes(cumulative)]
Class Category := Point {
  C: Category.Category ;
  pt: C ;
}.

#[universes(cumulative)]
Class Functor (A B: Category) := {
  F: Functor.Functor (@C A) (@C B) ;
  F_pt: F (@pt A) ~> @pt B ;
}.

Module Import PointedNotations.
  Coercion C: Category >-> Category.Category.
  Existing Instance C.

  Coercion F: Functor >-> Functor.Functor.
  Existing Instance F.
End PointedNotations.

#[program]
Definition Funct (K L: Category): Category := {|
  C := {|
    Obj := Functor K L ;
    Mor A B := Funct K L A B ;

    id _ := id _ ;
    compose _ _ _ := @compose _ _ _ _ ;
  |} ;

  pt := {|
    F := {|
      Functor.op _ := pt ;
      Functor.map _ _ _ := id _ ;
        |} ;
    F_pt := id _ ;
   |} ;
|}.

Next Obligation.
Proof.
  intros ? ? ?.
  reflexivity.
Qed.
