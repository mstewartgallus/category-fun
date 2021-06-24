Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Proset.
Require Import Blech.Proset.Sub.
Require Import Blech.Category.
Require Import Blech.Category.PreOrd.
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

Definition Subset: Bishop → Proset := Sub Bsh.

(* FIXME make CABA category basically *)
Definition Pow: Category := {|
  Obj := Bishop ;
  Mor A B := PreOrd (Subset A) (Subset B) ;

  id A := @id PreOrd (Subset A) ;
  compose A B C := @compose PreOrd (Subset A) (Subset B) (Subset C) ;

  compose_assoc _ _ _ _ := @compose_assoc PreOrd _ _ _ _ ;
  compose_id_left _ _ _ := @compose_id_left PreOrd _ _ _ ;
  compose_id_right _ _ _ := @compose_id_right PreOrd _ _ _ ;
|}.

#[program]
 Definition preimage {A B: Bishop} (f: Bsh B A): Pow A B
  := λ s,
     lub ({ a | ∃ x, f a == proj1_sig (π s) x } /~ {| equiv x y := proj1_sig x == y |}),
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
