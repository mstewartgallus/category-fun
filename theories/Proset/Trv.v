Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Proset.

Import ProsetNotations.

#[program]
Definition Trv: Proset := {|
  T := True ;
  preorder _ _ := True ;
|}.

Next Obligation.
Proof.
  exists.
  all: exists.
Defined.
