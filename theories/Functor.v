Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.

Import CategoryNotations.
Import BishopNotations.

Open Scope morphism_scope.
Open Scope bishop_scope.

#[universes(cumulative)]
Class Functoral {C D: Category} (op: C → D) (map: ∀ {A B: C}, C A B → D (op A) (op B)) := {
  map_composes [X Y Z] (x: C Y Z) (y: C X Y): map x ∘ map y == map (x ∘ y) ;

  map_id {A}: map (id A) == id _ ;
  map_compat [A B]: Proper (equiv ==> equiv) (@map A B) ;
}.
Existing Instance map_compat.

#[universes(cumulative)]
Class Functor (C D: Category) := functor {
  op: C → D ;
  map [A B: C]: C A B → D (op A) (op B) ;
  functoral: Functoral op map ;
}.
Existing Instance functoral.

Arguments functor {C D} op map {functoral}.
Coercion op: Functor >-> Funclass.
Arguments map [C D] Functor [A B].

Module FunctorNotations.
End FunctorNotations.
