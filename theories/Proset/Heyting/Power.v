Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Proset.
Require Import Blech.Proset.Heyting.

Import ProsetNotations.

(* Ostensibly, a first order system of logic is a free heyting algebra over the
set of free variables *)

#[program]
Definition Power (S: Bishop) : Heyting := {|
  P := {|
        T := { p: S → Prop | ∀ x y, x == y → p x ↔ p y } ;
        preorder p q := ∀ x, q x → p x ;
  |} ;

  Heyting.top _ := True ;
  Heyting.bot _ := False ;

  Heyting.meet p q x := p x ∧ q x ;
  Heyting.join p q x := p x ∨ q x ;
  Heyting.impl p q x := p x → q x ;
|}.

Next Obligation.
Proof.
  exists.
  - intros ? ? x.
    auto.
  - intros ? ? ? f g ? ?.
    apply f.
    apply g.
    auto.
Qed.

Next Obligation.
Proof.
  split.
  all: auto.
Qed.

Next Obligation.
Proof.
  split.
  all: contradiction.
Qed.

Next Obligation.
Proof.
  split.
  - intro pq.
    destruct pq.
    split.
    + apply (H1 x y).
      all: auto.
    + apply (H0 x y).
      all: auto.
  - intro pq.
    destruct pq.
    split.
    + apply (H1 x y).
      all: auto.
    + apply (H0 x y).
      all: auto.
Qed.

Next Obligation.
Proof.
  split.
  - intro pq.
    destruct pq.
    + left.
      apply (H1 x y).
      all: auto.
    + right.
      apply (H0 x y).
      all: auto.
  - intro pq.
    destruct pq.
    + left.
      apply (H1 x y).
      all: auto.
    + right.
      apply (H0 x y).
      all: auto.
Qed.

Next Obligation.
Proof.
  split.
  - intros f z.
    apply (H0 x y).
    all: auto.
    apply f.
    apply (H1 x y).
    all: auto.
  - intros f z.
    apply (H0 x y).
    all: auto.
    apply f.
    apply (H1 x y).
    all: auto.
Qed.
