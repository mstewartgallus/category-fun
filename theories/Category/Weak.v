Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Type.Predicate.
Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Category.Prod.
Require Import Blech.Groupoid.
Require Import Blech.Groupoid.Core.
Require Import Blech.Bicategory.
Require Import Blech.Functor.
Require Import Blech.Category.Funct.
Require Import Blech.Groupoid.
Require Import Blech.Type.Truncate.
Require Blech.Reflect.
Require Blech.Functor.Id.
Require Blech.Functor.Curry.
Require Blech.Functor.Compose.

Import BishopNotations.
Import CategoryNotations.
Import GroupoidNotations.
Import CoreNotations.
Import TruncateNotations.
Import ProdNotations.

Open Scope category_scope.
Open Scope bishop_scope.

#[local]
Obligation Tactic := Reflect.category_simpl.

#[program]
Definition Weak (C: Bicategory): Category := {|
  Category.Obj := C ;
  Category.Mor A B := C A B ;
  Category.Mor_Setoid A B := {| equiv x y := | x <~> y | |} ;

  Category.id := Bicategory.id ;
  Category.compose _ _ _ f g := Bicategory.compose (f, g) ;
|}.

Next Obligation.
Proof.
Admitted.

Next Obligation.
Proof.
  exists.
  apply Bicategory.compose_assoc.
Defined.

Next Obligation.
Proof.
  exists.
  apply Bicategory.compose_id_left.
Defined.

Next Obligation.
Proof.
  exists.
  apply Bicategory.compose_id_right.
Defined.

Next Obligation.
Proof.
  intros ? ? [p] ? ? [q].
  exists.
  eexists.
  Unshelve.
  3: {
    apply map.
    cbn.
    apply (to p, to q).
  }
  3: {
    apply map.
    cbn.
    apply (from p, from q).
  }
  - rewrite <- map_id.
    rewrite map_composes.
    apply map_compat.
    cbn.
    split.
    + rewrite to_from.
      reflexivity.
    + rewrite to_from.
      reflexivity.
  - rewrite <- map_id.
    rewrite map_composes.
    apply map_compat.
    cbn.
    split.
    + rewrite from_to.
      reflexivity.
    + rewrite from_to.
      reflexivity.
Qed.
