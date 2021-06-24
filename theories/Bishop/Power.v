Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Proset.
Require Import Blech.Proset.Sub.
Require Import Blech.Category.
Require Import Blech.Category.Over.
Require Import Blech.Category.Bsh.

Import CategoryNotations.
Import BishopNotations.
Import OverNotations.

Definition Power (S: Bishop): Bishop := Sub Bsh S /~ Proset_Setoid _.

#[program]
Definition pred {S: Bishop} (p: S → Prop):Power S :=
  lub ({ x | p x }/~ {| equiv x y := proj1_sig x == y |}),
  λ x, proj1_sig x.

Next Obligation.
Proof.
  admit.
Admitted.

Next Obligation.
Proof.
  intros ? ? ?.
  auto.
Qed.

#[program]
Definition fiber {S: Bishop} (p:Power S) (y: S): Prop :=
  ∃ x, y == π p x.
