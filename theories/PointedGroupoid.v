Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Functor.
Require Import Blech.Groupoid.

Require Blech.Reflect.

Import BishopNotations.
Import CategoryNotations.
Import FunctorNotations.
Import GroupoidNotations.

Open Scope category_scope.
Open Scope bishop_scope.


Class Groupoid := Point { G: Groupoid.Groupoid ; pt: G ; }.

Module PointedNotations.
  Coercion G: Groupoid >-> Groupoid.Groupoid.
  Existing Instance G.
End PointedNotations.
