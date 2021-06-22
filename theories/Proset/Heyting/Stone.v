Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Category.Bsh.
Require Import Blech.Category.Op.
Require Import Blech.Category.Heyt.
Require Import Blech.Functor.
Require Import Blech.Proset.
Require Import Blech.Proset.Heyting.
Require Import Blech.Proset.Heyting.Power.

Import OpNotations.
Import BishopNotations.
Import ProsetNotations.
Import HeytingNotations.
Import FunctorNotations.
Import CategoryNotations.

(*

Ostensibly by Stone duality Set ~ Heyt^op ?

I don't really get it though.

Also constructive issues I guess.
*)

#[program]
Definition Dual: Functor (Bsh ᵒᵖ) Heyt := {|
  op (S: Bsh) := Power S ;
  map A B f x y := x (f y) ;
|}.

Next Obligation.
Proof.
  split.
  - intro.
    apply (H0 (proj1_sig f x0) (proj1_sig f y)).
    all: auto.
    apply (proj2_sig f).
    auto.
  - intro.
    apply (H0 (proj1_sig f x0) (proj1_sig f y)).
    all: auto.
    apply (proj2_sig f).
    auto.
Qed.

Next Obligation.
Proof.
  exists.
  - split.
    all: exists.
  - cbn.
    split.
    all: contradiction.
  - cbn.
    intros.
    split.
    all: intros ? r.
    all: auto.
  - cbn.
    intros.
    split.
    all: intros ? r.
    all: auto.
  - cbn.
    intros.
    split.
    all: intros ? r.
    all: auto.
  - intros ? ? p ? ?.
    cbn in *.
    apply p.
    auto.
Qed.

Next Obligation.
Proof.
  intros ? ? p f.
  cbn in *.
  destruct f as [f fp].
  cbn in *.
  split.
  all: intros s t.
  - apply (fp _ _ (p s)).
    auto.
  - apply (fp _ _ (p s)).
    auto.
Qed.
