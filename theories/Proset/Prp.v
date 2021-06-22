Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Bool.Bool.

Require Import Blech.Proset.
Require Import Blech.Proset.Complete.

Import ProsetNotations.

#[program]
 Definition Prp: Proset := {|
  T := Prop ;
  preorder x y := x → y ;
|}.

Next Obligation.
Proof.
  exists.
  - intros ? ?.
    auto.
  - intros x y z p q ?.
    apply q.
    apply p.
    auto.
Defined.
