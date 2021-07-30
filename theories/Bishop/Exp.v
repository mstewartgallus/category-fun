Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.

Import BishopNotations.

#[program]
Definition exp (A B: Bishop): Bishop := { f: A → B | Proper (equiv ==> equiv) f } /~ {| equiv f g := ∀ x, f x == g x |}.

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

#[global]
Hint Unfold exp: bishop.

Module ExpNotations.
  Infix "→" := exp : bishop_scope.
End ExpNotations.
