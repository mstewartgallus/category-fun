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
  destruct x, y.
  all: cbn in *.
  - rewrite p.
    reflexivity.
  - destruct p.
    rewrite H1, H2.
    rewrite H0, H.
    reflexivity.
  - destruct p.
    rewrite H1, H2.
    rewrite H, H0.
    reflexivity.
  - rewrite p.
    reflexivity.
Qed.

#[program]
Definition inl {A B: Pointed}: exp A (sum A B) := inl.

Next Obligation.
Proof.
  intros ? ? p.
  cbn.
  assumption.
Qed.

Next Obligation.
Proof.
  unfold pt_eqv.
  reflexivity.
Qed.

#[program]
Definition inr {A B: Pointed}: exp B (sum A B) := inr.

Next Obligation.
  intros ? ? p.
  cbn.
  assumption.
Qed.

Next Obligation.
Proof.
  unfold pt_eqv.
  split.
  all: reflexivity.
Qed.

Module SumNotations.
  Infix "+" := sum : bishop_scope.
End SumNotations.
