Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.Bsh.
Require Import Blech.Category.
Require Import Blech.Monoid.

Require Blech.Monoid.Reflect.

Import CategoryNotations.
Import MonoidNotations.
Import BishopNotations.

Open Scope category_scope.
Open Scope bishop_scope.
Open Scope monoid_scope.

#[local]
Obligation Tactic := Reflect.monoid_simpl.

Class Mon_Mor [A B: Monoid] (f: A → B): Prop := {
  prp: Proper (equiv ==> equiv) f ;
  map_e: f e == e ;
  map_app x y: f (x · y) == f x · f y ;
}.

Existing Instance prp.

#[program]
Definition Mon: Category := {|
  Obj := Monoid ;
  Mor A B := { f: A → B | Mon_Mor f} /~ {| equiv x y := ∀ t, x t == y t |} ;

  id _  x := x ;
  compose _ _ _ f g x := f (g x) ;
|}.

Next Obligation.
Proof.
  exists.
  - intros ? ?.
    reflexivity.
  - intros ? ? p t.
    rewrite (p t).
    reflexivity.
  - intros ? ? ? p q t.
    rewrite (p t), (q t).
    reflexivity.
Qed.

Next Obligation.
Proof.
  exists.
  - intros ? ? p.
    rewrite p.
    reflexivity.
  - reflexivity.
  - intros.
    reflexivity.
Qed.

Next Obligation.
Proof.
  exists.
  - intros ? ? p.
    rewrite p.
    reflexivity.
  - repeat rewrite map_e.
    reflexivity.
  - intros.
    repeat rewrite map_app.
    reflexivity.
Qed.

Next Obligation.
Proof.
  intros f g p f' g' q x.
  cbn in *.
  destruct f, g, f', g'.
  cbn in *.
  rewrite (q _).
  rewrite (p _).
  reflexivity.
Qed.
