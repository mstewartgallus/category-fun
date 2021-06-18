Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Type.Some.
Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Functor.
Require Import Blech.Category.Bsh.
Require Import Blech.Bishop.Trv.
Require Blech.Reflect.

Import CategoryNotations.
Import BishopNotations.
Import FunctorNotations.
Import SomeNotations.

Open Scope category_scope.
Open Scope bishop_scope.


#[local]
Obligation Tactic := Reflect.category_simpl.


#[local]
Definition Obj [C] (P: Functor C Bsh) := Σ c: C, P c.


#[local]
 #[program]
 Definition Mor [C] (P: Functor C Bsh) (A B: Obj P) :=
  { u: head A ~> head B |
    map P u ∘ const (tail A) == const (tail B) }
    /~ {|
      equiv x y := proj1_sig x == y ;
    |}.

Next Obligation.
Proof.
  exists.
  - intros ?.
    reflexivity.
  - intros ? ? ?.
    symmetry.
    assumption.
  - intros ? ? ? p q.
    rewrite p, q.
    reflexivity.
Qed.


#[program]
 #[local]
 Definition id [C: Category] (P: Functor C Bsh) (A: Obj P): Mor P A A.
Proof.
  exists (id _).
  rewrite map_id.
  apply compose_id_left.
Defined.

#[program]
 #[local]
 Definition compose [C: Category] (P: Functor C Bsh)
 (a b c: Obj P) (f: Mor P b c) (g: Mor P a b): Mor P a c.
Proof.
  exists (proj1_sig f ∘ proj1_sig g).
  rewrite <- map_composes.
  rewrite <- compose_assoc.
  rewrite (proj2_sig g).
  rewrite (proj2_sig f).
  reflexivity.
Defined.


#[program]
Definition El [A: Category] (P: Functor A Bsh) := {|
  Category.Obj := Obj P ;
  Category.Mor := Mor P ;

  Category.id := id P ;
  Category.compose := compose P ;
|}.

Next Obligation.
Proof.
  rewrite H, H0.
  reflexivity.
Qed.
