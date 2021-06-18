Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Bishop.Exp.

Import BishopNotations.

Close Scope nat.

#[program]
Definition Trv: Bishop := True /~ {| equiv _ _ := True |}.

Next Obligation.
Proof.
  exists.
  all:exists.
Qed.

#[program]
 Definition bang {A}: exp A Trv := λ _, I.

Next Obligation.
Proof.
  intros ? ? p.
  reflexivity.
Qed.

#[program]
 Definition const {A: Bishop} (x: A): exp Trv A := λ _, x.

Next Obligation.
Proof.
  intros ? ? p.
  reflexivity.
Qed.

Module TrvNotations.
  Notation "·" := Trv : bishop_scope.
End TrvNotations.
