Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Bishop.Exp.
Require Import Blech.Pointed.

Import BishopNotations.
Import PointedNotations.

#[program]
 Definition exp (A B: Pointed): Pointed :=
  point
    (hom A B /~ {| equiv f g := ∀ t, f t == g t |})
    (λ _, pt).

Next Obligation.
Proof.
  exists.
  all: unfold Reflexive, Symmetric, Transitive.
  - intros.
    reflexivity.
  - intros.
    symmetry.
    auto.
  - intros ? ? ? p q t.
    rewrite (p _), (q _).
    reflexivity.
Qed.

Next Obligation.
Proof.
  intros ? ? ?.
  reflexivity.
Qed.

Next Obligation.
Proof.
  reflexivity.
Qed.

Module ExpNotations.
  Infix "→" := exp : pointed_scope.
End ExpNotations.
