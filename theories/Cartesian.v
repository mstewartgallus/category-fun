Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Functor.
Require Import Blech.Category.
Require Import Blech.Category.Funct.
Require Import Blech.Category.Prod.

Import BishopNotations.
Import CategoryNotations.
Import FunctorNotations.

Open Scope category_scope.
Open Scope bishop_scope.

#[local]
Obligation Tactic := Reflect.category_simpl.

#[universes(cumulative)]
Class Category := {
  C: Category.Category ;

  unit: C ;
  prod: Functor.Functor (C * C) C ;

  bang a: a ~> unit ;
  fanout {a b c}: c ~> a → c ~> b → c ~> prod (a, b) ;
  fst {a b}: prod (a, b) ~> a ;
  snd {a b}: prod (a, b) ~> b ;

  (* FIXME more laws ? *)
  bang_left {a b} (f: a ~> b): bang _ ∘ f == bang _ ;
  bang_right {b} (f: unit ~> b): f ∘ bang _ == f ;

  fanout_fst_snd {a b}: fanout fst snd == id (prod (a, b)) ;
  fst_fanout {a b c} (f: c ~> a) (g: c ~> b): fst ∘ fanout f g == f ;
  snd_fanout {a b c} (f: c ~> a) (g: c ~> b): snd ∘ fanout f g == g ;
}.

Existing Instance C.
Coercion C: Category >-> Category.Category.

Module CartesianNotations.
  Infix "*" := prod : object_scope.
End CartesianNotations.
