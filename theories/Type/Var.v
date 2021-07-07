Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Import IfNotations.
Import ListNotations.

Inductive var : list string → Type :=
| tip {H T}: var (H :: T)
| inch {H T}: var T → var (H :: T).

#[program]
Fixpoint v (s: string) {xs: list string} {p: In s xs}: var xs :=
  match xs with
  | cons H T =>
    if string_dec H s
    then tip
    else inch (@v s T _)
  | _ => _
  end.

Next Obligation.
Proof.
  induction T.
  - cbn in *.
    destruct p.
    all: contradiction.
  - cbn in *.
    destruct p.
    + contradiction.
    + destruct H1.
      * subst.
        left.
        exists.
      * right.
        assumption.
Qed.

Next Obligation.
Proof.
  induction xs.
  1:contradiction.
  cbn in *.
  constructor.
Qed.

Notation "!" := v.

(* Substitution of free boolean algebras, not sure is right *)

Definition substitute {H T} (P: var (H :: T) → Prop): var T → Prop.
Proof.
  intro x.
  apply P.
  apply inch.
  apply x.
Defined.
