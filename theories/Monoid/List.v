Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Lists.List.

Require Import Blech.Bishop.
Require Import Blech.Monoid.

Import BishopNotations.
Import MonoidNotations.

Open Scope bishop_scope.
Open Scope monoid_scope.

#[local]
 #[program]
 Instance list_Setoid (S: Bishop): Setoid (list S) := {
  equiv := Forall2 equiv ;
 }.
Next Obligation.
Proof.
  exists.
  - intro x.
    induction x.
    + constructor.
    + constructor.
      * reflexivity.
      * assumption.
  - intros x y p.
    induction p.
    + constructor.
    + constructor.
      * symmetry.
        assumption.
      * assumption.
  - intros x y z p q.
    admit.
Admitted.

#[program]
 Definition List (S: Bishop): Monoid := {|
  S := list S /~ list_Setoid S ;

  e := nil ;
  app := @List.app _ ;
|}.

Next Obligation.
Proof.
  rewrite List.app_assoc.
  replace (Forall2 equiv) with equiv.
  all: reflexivity.
Qed.

Next Obligation.
Proof.
  replace (Forall2 equiv) with equiv.
  all: reflexivity.
Qed.

Next Obligation.
Proof.
  rewrite app_nil_r.
  replace (Forall2 equiv) with equiv.
  all: reflexivity.
Qed.

Next Obligation.
Proof.
  intros ? ? p ? ? q.
  apply Forall2_app.
  all: assumption.
Qed.
