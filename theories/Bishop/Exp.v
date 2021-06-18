Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.

Import BishopNotations.

Open Scope bishop_scope.

Definition bishop_mor [A B:Bishop] (op: A → B) := ∀ x y, x == y → op x == op y.
Existing Class bishop_mor.

Definition Bishop_Mor (A B: Bishop) := { op: A → B | bishop_mor op }.

Definition proj1_Bishop_Mor [A B]: Bishop_Mor A B → A → B := @proj1_sig _ _.
Definition proj2_Bishop_Mor [A B] (f:Bishop_Mor A B): bishop_mor (proj1_Bishop_Mor f) := proj2_sig f.

#[program]
Definition exp (A B: Bishop): Bishop := Bishop_Mor A B /~ {| equiv f g := ∀ x, f x == g x |}.

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

Add Parametric Morphism {A B} (f: exp A B) : (proj1_sig f)
    with signature equiv ==> equiv as exp_mor.
Proof.
  intros.
  destruct f.
  cbn.
  auto.
Qed.

Module ExpNotations.
  Coercion proj1_Bishop_Mor: Bishop_Mor >-> Funclass.
  Coercion proj2_Bishop_Mor: Bishop_Mor >-> bishop_mor.
  Existing Instance proj2_Bishop_Mor.

  Infix "→" := exp : bishop_scope.
End ExpNotations.
