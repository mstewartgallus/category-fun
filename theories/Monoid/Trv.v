Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Bishop.Trv.
Require Import Blech.Monoid.

Import BishopNotations.
Import MonoidNotations.

Open Scope bishop_scope.
Open Scope monoid_scope.

#[program]
Definition Trv: Monoid := {|
  S := trv ;
  e := I ;
  app _ _ := I ;
|}.

Next Obligation.
Proof.
  intros ? ? ? ? ? ?.
  exists.
Qed.
