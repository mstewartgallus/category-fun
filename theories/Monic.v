Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.

Import CategoryNotations.
Import BishopNotations.

Open Scope category_scope.
Open Scope bishop_scope.

#[universes(cumulative)]
Class Monic := {
  C: Category ;

  monic [X Y Z] (f: C Y Z) (x y: C X Y): f ∘ x == f ∘ y → x == y ;
}.

Existing Instance C.
Coercion C: Monic >-> Category.
