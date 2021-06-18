Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Bishop.Exp.

Import BishopNotations.

#[program]
Definition mt: Bishop := False /~ {| equiv x := match x with end |}.

Next Obligation.
Proof.
  exists.
  all:intro;contradiction.
Qed.


#[program]
Definition absurd {A: Bishop}: exp mt A := λ x, match x with end.

Next Obligation.
Proof.
  intro.
  contradiction.
Qed.

Module MtNotations.
  Notation "∅" := mt : bishop_scope.
End MtNotations.
