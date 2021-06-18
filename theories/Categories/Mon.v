Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Categories.Bsh.
Require Import Blech.Category.
Require Import Blech.Monoid.
Require Blech.Reflect.

Import CategoryNotations.
Import MonoidNotations.
Import BishopNotations.

Open Scope category_scope.
Open Scope bishop_scope.
Open Scope monoid_scope.

Obligation Tactic := Reflect.category_simpl.

Class Mon_Mor [A B: Monoid] (f: A → B): Prop := {
  map_unit: f ∅ == ∅ ;
  map_app x y: f (x · y) == f x · f y ;
}.

#[program]
 Definition Mon: Category := {|
  Obj := Monoid ;
  Mor A B := { f: Bsh A B | Mon_Mor f} /~ {| equiv x y := proj1_sig x == (y :>) |} ;

  id _ := exist _ (id _) _ ;
  compose _ _ _ f g := exist _ (proj1_sig f ∘ g) _ ;
|}.

Next Obligation.
Proof.
  intros ? ? p.
  rewrite p.
  reflexivity.
Qed.

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
  - repeat rewrite map_unit.
    reflexivity.
  - intros.
    repeat rewrite map_app.
    reflexivity.
Qed.

Next Obligation.
Proof.
  rewrite (H _), (H0 _).
  reflexivity.
Qed.
