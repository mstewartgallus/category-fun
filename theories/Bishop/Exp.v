Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.

Import BishopNotations.

#[program]
Definition exp (A B: Bishop): Bishop := hom A B /~ {| equiv f g := ∀ x, f x == g x |}.

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

Add Parametric Morphism {A B} (f: exp A B) : (proj1_hom f)
    with signature equiv ==> equiv as exp_mor.
Proof.
  intros.
  destruct f.
  cbn.
  auto.
Qed.

Module ExpNotations.
  Infix "→" := exp : bishop_scope.
End ExpNotations.
