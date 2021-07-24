Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Type.Some.
Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Functor.
Require Import Blech.Proset.
Require Import Blech.Category.PreOrd.
Require Import Blech.Proset.Trv.
Require Blech.Reflect.

Import CategoryNotations.
Import BishopNotations.
Import FunctorNotations.
Import ProsetNotations.
Import SomeNotations.

Open Scope category_scope.
Open Scope bishop_scope.


#[local]
Obligation Tactic := Reflect.category_simpl.


#[local]
Definition Obj [C] (P: Functor C PreOrd) := Σ c: C, P c.

#[program]
 Definition const {A: Proset} (a: A): PreOrd Trv A := λ _, a.

Next Obligation.
Proof.
  intros ? ? p.
  reflexivity.
Qed.

(* FIXME this looks wrong to me *)
#[local]
 #[program]
 Definition Mor [C] (P: Functor C PreOrd) (A B: Obj P) :=
  { u: head A ~> head B |
    map P u ∘ const (tail A) == const (tail B) }.

#[program]
 #[local]
 Definition id [C: Category] (P: Functor C PreOrd) (A: Obj P): Mor P A A.
Proof.
  exists (id _).
  rewrite map_id.
  apply compose_id_left.
Defined.

#[program]
 #[local]
 Definition compose [C: Category] (P: Functor C PreOrd)
 (a b c: Obj P) (f: Mor P b c) (g: Mor P a b): Mor P a c.
Proof.
  exists (proj1_sig f ∘ proj1_sig g).
  rewrite <- map_composes.
  rewrite <- compose_assoc.
  rewrite (proj2_sig g).
  rewrite (proj2_sig f).
  reflexivity.
Defined.

(* Just a small variation on the category of elements for preordered sets *)
#[program]
Definition ElPreOrd [A: Category] (P: Functor A PreOrd) := {|
  Category.Obj := Obj P ;
  Category.Mor := Mor P ;

  Mor_Setoid _ _ := {|
      equiv x y := proj1_sig x == y ;
    |} ;

  Category.id := id P ;
  Category.compose := compose P ;
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

Next Obligation.
Proof.
  intros ? ? p ? ? q.
  cbn in *.
  rewrite p, q.
  reflexivity.
Qed.
