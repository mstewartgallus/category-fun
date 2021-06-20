Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Blech.Reflect.

Import CategoryNotations.
Import BishopNotations.

Open Scope category_scope.
Open Scope bishop_scope.

Import BishopNotations.


Reserved Notation "∅".
Reserved Notation "X · Y" (at level 30, right associativity).


Class Monoid := {
  S: Bishop.Bishop ;

  unit: S ;
  app: S → S → S
  where "f · g" := (app f g) ;

  app_assoc (f: S) (g: S) (h: S):
    (f · (g · h)) == ((f · g) · h );
  app_unit_left (f: S): (unit · f) == f ;
  app_unit_right (f: S): (f · unit) == f ;

  app_compat: Proper (equiv ==> equiv ==> equiv) app ;
}.

Coercion S: Monoid >-> Bishop.Bishop.
Existing Instance S.

Existing Instance app_compat.

Module MonoidNotations.
  Declare Scope monoid_scope.
  Delimit Scope monoid_scope with monoid.

  Bind Scope monoid_scope with Monoid.
  Bind Scope monoid_scope with S.

  Notation "∅" := unit : monoid_scope.
  Notation "f · g" := (app f g) : monoid_scope.
End MonoidNotations.
