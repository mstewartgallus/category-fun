Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Proset.

Import ProsetNotations.

#[universes(cumulative)]
Record bundle (P: Proset) (t: P) := sup { s: P ; π: s ⊑ t ; }.

Arguments sup [P] [t] _.
Arguments s [P] [t] _.
Arguments π [P] [t] _.

Coercion s: bundle >-> T.

#[program]
Definition Over (P: Proset) (t: P): Proset := {|
  T := bundle P t ;
  preorder A B := s A ⊑ s B ;
|}.

Next Obligation.
Proof.
  exists.
  - intros ?.
    reflexivity.
  - intros ? ? ? p q.
    rewrite p, q.
    reflexivity.
Qed.
