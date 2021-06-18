Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.

Import CategoryNotations.
Import BishopNotations.

Open Scope category_scope.
Open Scope bishop_scope.

#[universes(cumulative)]
Class Functor (C D: Category) := {
  op: C → D ;
  map [A B: C]: C A B → D (op A) (op B) ;

  map_composes [X Y Z] (x: C Y Z) (y: C X Y): map x ∘ map y == map (x ∘ y) ;

  map_id {A}: map (id A) == id _ ;
  map_compat [A B] (f f': C A B): f == f' → map f == map f' ;
}.

Arguments map [C D] Functor [A B].

Add Parametric Morphism (C D: Category) (F: Functor C D) (A B: C)  : (@map _ _ F A B)
    with signature equiv ==> equiv as map_mor.
Proof.
  intros ? ? ?.
  apply map_compat.
  assumption.
Qed.

Module FunctorNotations.
  Coercion op: Functor >-> Funclass.
End FunctorNotations.
