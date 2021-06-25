Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Monic.
Require Blech.Reflect.

Import CategoryNotations.
Import BishopNotations.

Open Scope category_scope.
Open Scope bishop_scope.


Reserved Notation "C ₊" (at level 1).

#[local]
Obligation Tactic := Reflect.category_simpl.

#[program]
 Definition Mono (C: Category): Monic :=
  {|
  C := {|
    Obj := C ;
    Mor A B := {f: C A B | ∀ (Z:C) (x y: C Z A), (f ∘ x == f ∘ y) → x == y } /~ {| equiv x y := (x :>) == (y :>) |} ;
    id := @id _ ;
    compose := @compose _ ;
  |} ;
|}.

Next Obligation.
Proof.
  exists.
  - intro.
    reflexivity.
  - intros ? ? ?.
    symmetry.
    auto.
  - intros ? ? ? p q.
    rewrite p, q.
    reflexivity.
Qed.

Next Obligation.
Proof.
  repeat rewrite compose_id_left in H.
  assumption.
Qed.

Next Obligation.
Proof.
  repeat rewrite <- compose_assoc in H.
  apply (H0 _ _ _ (H1 _ _ _ H)).
Qed.

Next Obligation.
Proof.
  intros ? ? p ? ? q.
  cbn.
  rewrite p, q.
  reflexivity.
Qed.

Module MonoNotations.
  Notation "C ₊" := (Mono C) : category_scope.
End MonoNotations.

Require Import Blech.Functor.

#[program]
Definition U C : Functor (Mono C) C := {|
  op x := x ;
  map _ _ f := f ;
|}.

Next Obligation.
Proof.
  intros ? ? p.
  assumption.
Qed.
