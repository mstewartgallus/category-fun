Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Bishop.Exp.
Import ExpNotations.
Require Import Blech.Pointed.

Import BishopNotations.
Import PointedNotations.

Definition pt_eqv (A B: Pointed) (x y: A + B) :=
  match (x, y) with
  | (inl x', inl y') => x' == y'
  | (inr x', inr y') => x' == y'

  | (inl x', inr y') => x' == pt ∧ y' == pt
  | (inr x', inl y') => x' == pt ∧ y' == pt
  end.

Require Import Blech.Bishop.Sum.
Require Import Blech.Pointed.
Require Import Blech.Pointed.Exp.

Import ExpNotations.
Import SumNotations.

Close Scope nat.

#[program]
 Definition sum (A B: Pointed): Pointed :=
  point ((A + B) /~ {| equiv := pt_eqv A B |}) (inl pt).

Next Obligation.
Proof.
  admit.
Admitted.

#[program]
Definition fanin {C A B: Pointed} (f: exp A C) (g: exp B C): exp (sum A B) C := fanin f g.

Next Obligation.
Proof.
  intros x y p.
  rewrite p.
  reflexivity.
Qed.

Next Obligation.
Proof.
  intros ? ? p.
  rewrite p.
  reflexivity.
Qed.

Next Obligation.
Proof.
  exists.
  - intros ? ? p.
    destruct x, y.
    all: cbn in *.
    all: try destruct p as [p q].
    all: try rewrite p.
    all: try rewrite q.
    all: repeat rewrite map_pt.
    all: reflexivity.
  - cbn.
    rewrite map_pt.
    reflexivity.
Qed.

#[program]
Definition inl {A B: Pointed}: exp A (sum A B) := inl.

Next Obligation.
Proof.
  exists.
  - intros ? ? p.
    cbn.
    assumption.
  - cbn.
    reflexivity.
Qed.

#[program]
Definition inr {A B: Pointed}: exp B (sum A B) := inr.

Next Obligation.
Proof.
  exists.
  - intros ? ? p.
    cbn.
    assumption.
  - cbn.
    split.
    all: reflexivity.
Qed.

Module SumNotations.
  Infix "+" := sum : pointed_scope.
End SumNotations.
