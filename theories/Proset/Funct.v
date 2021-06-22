Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Proset.
Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Category.PreOrd.

Import ProsetNotations.
Import CategoryNotations.

(* FIXME do some yoneda thing but for bool-valued presheafs *)
#[program]
Definition Funct (A B: Proset): Proset := {|
  Proset.T := PreOrd A B ;
  preorder x y := ∀ t, x t ⊑ y t ;
|}.

Next Obligation.
Proof.
  exists.
  - intros ? ?.
    reflexivity.
  - intros ? ? ? p q ?.
    rewrite p.
    rewrite q.
    reflexivity.
Qed.
