Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Proset.
Require Import Blech.Proset.Complete.
Require Import Blech.Proset.Op.
Require Import Blech.Proset.Sub.
Require Import Blech.Category.
Require Import Blech.Category.PreOrd.
Require Import Blech.Category.CABA.
Require Import Blech.Category.Bsh.
Require Import Blech.Category.Over.
Require Blech.Reflect.

Import BishopNotations.
Import CategoryNotations.
Import ProsetNotations.
Import OpNotations.
Import OverNotations.

Open Scope category_scope.
Open Scope bishop_scope.


#[local]
Obligation Tactic := Reflect.category_simpl.

(* The powerset can be considered the free CABA *)
#[program]
Definition Powerset (S: Bishop): CABA := {|
  P := Sub Bsh S ;
|}.

Next Obligation.
Proof.
  admit.
Admitted.

Next Obligation.
Proof.
  admit.
Admitted.

(* FIXME make a functor *)
#[program]
 Definition preimage {A B: Bishop} (f: Bsh B A): Powerset A ~> Powerset B :=
  λ s, lub ({ a | ∃ x, f a == proj1_sig (π s) x } /~ {| equiv x y := proj1_sig x == y |}),
     λ y, proj1_sig y.

Next Obligation.
Proof.
  exists.
  - intros ?.
    reflexivity.
  - intros ? ? ?.
    symmetry.
    assumption.
  - intros ? ? ? p q.
    rewrite p, q.
    reflexivity.
Qed.

Next Obligation.
Proof.
  intros ? ? p.
  assumption.
Defined.

Next Obligation.
Proof.
  intros x y p.
  destruct x as [sx px], y as [sy py].
  destruct px as [px], py as [py].
  cbn in *.
  destruct p.
  exists.
  eexists.
  Unshelve.
  2: {
    cbn in *.
    eexists.
    Unshelve.
    2: {
      cbn in *.
      eexists.
      Unshelve.
      2: {
        cbn in *.
        intro x.
        exists (proj1_sig x).
        destruct X.
        destruct x0.
        destruct x.
        cbn in *.
        destruct e3.
        exists (proj1_sig x0 x1).
        rewrite H.
        rewrite e1.
        reflexivity.
      }
      cbn in *.
      intros ? ? p.
      cbn in *.
      assumption.
    }
    cbn in *.
    intros ? ? ? p ?.
    apply p.
  }
  cbn in *.
  intros ?.
  reflexivity.
Qed.

Next Obligation.
Proof.
  exists.
  - admit.
  - admit.
Admitted.
