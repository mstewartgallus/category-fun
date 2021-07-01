Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Import BishopNotations.

Open Scope bishop_scope.

Import BishopNotations.

Reserved Notation "X · Y" (at level 50, left associativity).

Class Monoid := {
  S: Bishop ;

  (* I think this name is stupid but it is convention *)
  e: S ;
  app: S → S → S
  where "f · g" := (app f g) ;

  app_assoc (f: S) (g: S) (h: S):
    f · (g · h) == (f · g) · h;
  app_e_left (f: S): e · f == f ;
  app_e_right (f: S): f · e == f ;

  app_compat: Proper (equiv ==> equiv ==> equiv) app ;
}.

Coercion S: Monoid >-> Bishop.
Existing Instance S.

Existing Instance app_compat.

Module MonoidNotations.
  Declare Scope monoid_scope.
  Delimit Scope monoid_scope with monoid.

  Bind Scope monoid_scope with Monoid.
  Bind Scope monoid_scope with S.

  Infix "·" := app : monoid_scope.
End MonoidNotations.
