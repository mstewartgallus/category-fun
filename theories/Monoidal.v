Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Functor.
Require Import Blech.Product.

Import BishopNotations.
Import CategoryNotations.
Import FunctorNotations.

Open Scope category_scope.
Open Scope bishop_scope.

Obligation Tactic := Reflect.category_simpl.

Reserved Notation "·".
Reserved Notation "X ⊗ Y" (at level 30, right associativity).

#[universes(cumulative)]
Class Category := {
  C: Category.Category ;

  pt: C ;
  app: Functor.functor (C * C) C ;

  (* FIXME add laws *)
}.
(* Lax monoidal functor *)

#[universes(cumulative)]
Class functor (M N: Category) := {
  F: Functor.functor (@C M) (@C N) ;
  mon_pt: C pt (F pt) ;
  mon_app {A B}: C (app (F A, F B)) (F (app (A, B)));
}.

Arguments F [M N].

Module Import MonoidalNotations.
  Existing Instance C.
  Coercion C: Category >-> Category.Category.

  Notation "·" := pt.
  Notation "x ⊗ y" := (app (x, y)).

  Existing Instance F.
  Coercion F: functor >-> Functor.functor.
End MonoidalNotations.

#[program]
Definition Funct (K L: Category): Category.Category := {|
  Obj := functor K L ;
  Mor A B := Funct _ _ (F A) (F B) ;

  id _ := id _ ;
  compose _ _ _ := @compose _ _ _ _ ;
|}.

Next Obligation.
Proof.
  rewrite (H x), (H0 x).
  reflexivity.
Qed.
