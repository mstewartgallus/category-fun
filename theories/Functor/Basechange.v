Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Functor.
Require Import Blech.Category.Over.
Require Import Blech.Category.Bsh.

Require Blech.Reflect.

Import CategoryNotations.
Import FunctorNotations.
Import BishopNotations.
Import OverNotations.

Open Scope category_scope.
Open Scope object_scope.
Open Scope bishop_scope.

#[local]
Obligation Tactic := Reflect.category_simpl.

#[local]
Definition pullback {A B C: Bsh} (f: Bsh A C) (g: Bsh B C) :=
  { '(x, y) | proj1_sig f x == proj1_sig g y }.

#[program]
Instance pullback_Setoid {A B C: Bsh} (f: Bsh A C) (g: Bsh B C): Setoid (pullback f g) := {
  equiv x y := fst (proj1_sig x) == fst (proj1_sig y) ∧ snd (proj1_sig x) == snd (proj1_sig y) ;
}.

Next Obligation.
Proof.
  exists.
  - intros [[? ?] p].
    cbn in *.
    split.
    all: reflexivity.
  - intros [[? ?] p] [[? ?] q] [r l].
    cbn in *.
    rewrite r, l.
    split.
    all: reflexivity.
  - intros [[? ?] ?] [[? ?] ?] [[? ?] ?] [p q] [r s].
    cbn in *.
    rewrite p, q, r, s.
    split.
    all: reflexivity.
Qed.

#[program]
Definition Basechange {A B: Bsh} (f: Bsh A B): Functor (Bsh/B) (Bsh/A) := {|
  op (u: Bsh/B) := lub (pullback f (π u) /~ pullback_Setoid f (π u)), λ x, fst (proj1_sig x) ;
  map '(lub _, _) '(lub _, _) f '(x, y) := (x, f y) ;
|}.

Next Obligation.
Proof.
  intros ? ? [p q].
  auto.
Qed.

Next Obligation.
Proof.
  rewrite (H _).
  cbn in *.
  destruct pat.
  cbn in *.
  destruct x0.
  cbn in *.
  inversion Heq_anonymous.
  subst.
  apply e.
Qed.

Next Obligation.
Proof.
  intros ? ? [p q].
  cbn.
  rewrite p, q.
  split.
  all: reflexivity.
Qed.

Next Obligation.
Proof.
  exists.
  all: cbn.
  - intros.
    split.
    all: reflexivity.
  - intros.
    split.
    all: reflexivity.
  - intros ? ? [? ?] [? ?] r [[? ?] ?].
    cbn in *.
    split.
    1: reflexivity.
    apply r.
Qed.
