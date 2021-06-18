Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Monoid.
Require Blech.Bishops.

Require Blech.Reflect.

Import BishopNotations.
Import MonoidNotations.

Open Scope bishop_scope.
Open Scope monoid_scope.

#[program]
 Definition Or: Monoid := {|
  S := Bishops.simple bool ;

  unit := false ;
  app := orb ;
|}.

Next Obligation.
Proof.
  destruct f, g, h.
  all: cbn in *.
  all: reflexivity.
Qed.

Next Obligation.
Proof.
  destruct f.
  all: cbn in *.
  all: reflexivity.
Qed.
