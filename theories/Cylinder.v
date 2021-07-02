Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Functor.
Require Import Blech.Category.
Require Import Blech.Category.Funct.
Require Import Blech.Category.Prod.
Require Import Blech.Category.Op.

Import BishopNotations.
Import CategoryNotations.
Import OpNotations.
Import FunctorNotations.

Open Scope category_scope.
Open Scope bishop_scope.

#[local]
Obligation Tactic := Reflect.category_simpl.

Reserved Notation "⊤".
Reserved Notation "X × Y" (at level 50, left associativity).

Reserved Notation "∅".

Reserved Notation "[ X , Y ]".

#[universes(cumulative)]
Class Closed := {
  C: Category ;

  pt: C ;
  prod: Functor (C * C) C ;

  mt: C ;
  sum: Functor (C * C) C ;

  (* FIXME add curry/laws *)
  exp: Functor (C ᵒᵖ * C) C ;
}.

Existing Instance C.
Coercion C: Closed >-> Category.

Notation "⊤" := pt.
Notation "A × B" := (prod (A, B)).

Notation "∅" := mt.
Notation "A + B" := (sum (A, B)).
Notation "[ A , B ]" := (exp (A, B)).

(* FIXME laws *)
Reserved Notation "◇".
Reserved Notation "□".

Class Var (C: Closed) := {
  necessarily: Functor C C ;
  possibly: Functor C C;

  K {A B}: necessarily [A, B] ~> [necessarily A, necessarily B] ;
  T {A}: necessarily A ~> A ;

  perhaps {A}: A ~> necessarily (possibly A) ;
}.

Arguments necessarily {C}.
Arguments possibly {C}.

(* Like universal *)
Notation "□" := necessarily.
(* Like existential *)
Notation "◇" := possibly.

  (* FIXME require finite ? *)
Class Cylinder (α: Type) := {
  H: Closed ;

  var: α → Var H ;
  (* FIXME laws *)
}.

Existing Instance H.
Coercion H: Cylinder >-> Closed.

Notation "!" := var.

Require Import Coq.Strings.String.
Open Scope string.

Section open.
  Context `{Cylinder string}.

  Definition foo: ⊤ ~> □ (! "A") (◇ (! "A") ⊤) := perhaps.
End open.
