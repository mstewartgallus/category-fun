Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.

Import BishopNotations.


Reserved Notation "A ~> B" (at level 80, right associativity).
Reserved Notation "A ∘ B" (at level 30).


#[universes(cumulative)]
Class Category := {
  Obj: Type ;
  Mor: Obj → Obj → Bishop ;

  id A: Mor A A ;
  compose [A B C]: Mor B C -> Mor A B -> Mor A C
  where "f ∘ g" := (compose f g) ;

  compose_assoc [A B C D] (f: Mor C D) (g: Mor B C) (h: Mor A B):
    (f ∘ (g ∘ h)) == ((f ∘ g) ∘ h );
  compose_id_left [A B] (f: Mor A B): (id B ∘ f) == f ;
  compose_id_right [A B] (f: Mor A B): (f ∘ id A) == f ;

  compose_compat [A B C] (f f': Mor B C) (g g': Mor A B):
    f == f' → g == g' → f ∘ g == f' ∘ g' ;
}.

Arguments Obj: clear implicits.
Arguments Mor: clear implicits.


Module Import CategoryNotations.
  Declare Scope category_scope.
  Delimit Scope category_scope with category.

  Bind Scope category_scope with Category.
  Bind Scope category_scope with Obj.
  Bind Scope category_scope with Mor.

  Coercion Obj: Category >-> Sortclass.
  Coercion Mor: Category >-> Funclass.

  Notation "f ∘ g" := (compose f g) : category_scope.
  Notation "A → B" := (Mor _ A B) (only parsing) : category_scope.
  Notation "A ~> B" := (Mor _ A B) (only parsing) : category_scope.
End CategoryNotations.


Add Parametric Morphism [K:Category] (A B C: K) : (@compose K A B C)
    with signature equiv ==> equiv ==> equiv as compose_mor.
Proof.
  intros ? ? p ? ? q.
  apply compose_compat.
  - apply p.
  - apply q.
Qed.