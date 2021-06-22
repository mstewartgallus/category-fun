Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Proset.

Import ProsetNotations.

#[universes(cumulative)]
Record cobundle (P: Proset) (s: P) := inf { t: P ; i: s ⊑ t ; }.

Arguments inf [P] [s] _.
Arguments t [P] [s] _.
Arguments i [P] [s] _.

Coercion t: cobundle >-> T.

#[program]
Definition Under (P: Proset) (s: P): Proset := {|
  T := cobundle P s ;
  preorder A B := t A ⊑ t B ;
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
