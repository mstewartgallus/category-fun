Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Blech.Reflect.

Import CategoryNotations.
Import BishopNotations.

Open Scope category_scope.
Open Scope bishop_scope.


Obligation Tactic := Reflect.category_simpl.


#[universes(cumulative)]
Class functor (C D: Category) := {
  op: C → D ;
  map [A B: C]: C A B → D (op A) (op B) ;

  map_composes [X Y Z] (x: C Y Z) (y: C X Y): map x ∘ map y == map (x ∘ y) ;

  map_id {A}: map (id A) == id _ ;
  map_compat [A B] (f f': C A B): f == f' → map f == map f' ;
}.

Arguments map [C D] functor [A B].

Add Parametric Morphism (C D: Category) (F: functor C D) (A B: C)  : (@map _ _ F A B)
    with signature equiv ==> equiv as map_mor.
Proof.
  intros ? ? ?.
  apply map_compat.
  assumption.
Qed.

#[program]
Definition Funct (K L: Category): Category := {|
  Obj := functor K L ;
  Mor A B := (∀ x, L (op x) (op x)) /~ {| equiv f g := ∀ x, f x == g x |} ;
  id _ _ := id _ ;
  compose _ _ _ f g _ := f _ ∘ g _ ;
|}.

Next Obligation.
Proof.
  exists.
  all: unfold Reflexive, Symmetric, Transitive; cbn.
  - intros.
    reflexivity.
  - intros ? ? p t.
    symmetry.
    apply (p t).
  - intros ? ? ? p q t.
    rewrite (p t), (q t).
    reflexivity.
Qed.

Next Obligation.
Proof.
  apply compose_compat.
  all:auto.
Qed.


Module FunctorNotations.
  Coercion op: functor >-> Funclass.
End FunctorNotations.
