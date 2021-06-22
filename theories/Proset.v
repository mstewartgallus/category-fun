Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Reserved Notation "A ⊑ B" (at level 70, no associativity).

#[universes(cumulative)]
Class Proset := {
  T: Type ;
  preorder: relation T ;
  Proset_PreOrder: PreOrder preorder ;
}.

Arguments T: clear implicits.
Existing Instance Proset_PreOrder.
Coercion T: Proset >-> Sortclass.

#[program]
Instance Proset_Setoid (C: Proset): Setoid (T C) := {
  equiv x y := preorder x y ∧ preorder y x ;
}.

Next Obligation.
Proof.
  exists.
  - intros ?.
    split.
    all: reflexivity.
  - intros ? ? p.
    destruct p.
    split.
    all: assumption.
  - intros ? ? ? p q.
    destruct p as [p p'], q as [q q'].
    split.
    + rewrite p, q.
      reflexivity.
    + rewrite q', p'.
      reflexivity.
Qed.

Instance subrelation_equiv_preorder `(Proset) : subrelation equiv preorder.
Proof.
  intros ? ? p.
  destruct p.
  auto.
Qed.

Module Import ProsetNotations.
  Infix "⊑" := preorder.

  Declare Scope proset_scope.
  Delimit Scope proset_scope with proset.

  Bind Scope proset_scope with Proset.
End ProsetNotations.
