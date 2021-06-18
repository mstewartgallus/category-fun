Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Functor.
Require Blech.Reflect.

Import CategoryNotations.
Import BishopNotations.
Import FunctorNotations.

Open Scope category_scope.
Open Scope bishop_scope.


#[universes(cumulative)]
Class Category := Point {
  C: Category.Category ;
  pt: C ;
}.

#[universes(cumulative)]
Class funct (A B: Category) := {
  F: functor (@C A) (@C B) ;
  F_pt: F (@pt A) ~> @pt B ;
}.

Module Import PointedNotations.
  Coercion C: Category >-> Category.Category.
  Existing Instance C.

  Coercion F: funct >-> functor.
  Existing Instance F.
End PointedNotations.

#[program]
Definition Funct (K L: Category): Category := {|
  C := {|
    Obj := functor K L ;
    Mor A B := Funct K L A B ;

    id _ := id _ ;
    compose _ _ _ := @compose _ _ _ _ ;
  |} ;

  pt := {|
    F := {|
      op _ := pt ;
      map _ _ _ := id _ ;
        |} ;
    F_pt := id _ ;
   |} ;
|}.

Next Obligation.
Proof.
  rewrite (H x), (H0 x).
  reflexivity.
Qed.
