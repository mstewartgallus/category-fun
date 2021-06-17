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
Record Category := Point {
  C: Category.Category ;
  pt: C ;
}.

#[universes(cumulative)]
Record funct (A B: Category) := {
  F: Funct (C A) (C B) ;
  F_pt: F (pt A) ~> pt B ;
}.

Module PointedNotations.
  Coercion C: Category >-> Category.Category.
  Existing Instance C.

  Coercion F: funct >-> Obj.
End PointedNotations.
