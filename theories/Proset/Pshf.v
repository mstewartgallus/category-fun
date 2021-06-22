Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Proset.
Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Category.PreOrd.
Require Import Blech.Proset.Funct.
Require Import Blech.Proset.Op.
Require Import Blech.Proset.Prp.
Require Import Blech.Proset.Complete.

Import ProsetNotations.
Import CategoryNotations.
Import OpNotations.

Definition Pshf (S: Proset): Proset := Funct (S ᵒᵖ) Prp.

#[program]
 Definition Yo {S: Proset}: PreOrd S (Pshf S) := λ y x, (x: S) ⊑ y.

Next Obligation.
Proof.
  intros ? ? p q.
  cbn in *.
  rewrite p.
  rewrite q.
  reflexivity.
Defined.

Next Obligation.
Proof.
  intros ? ? p ? q.
  cbn in *.
  rewrite q, p.
  reflexivity.
Defined.

