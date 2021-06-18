Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.setoid_ring.Ring_theory.

Require Import Blech.Bishop.
Require Psatz.

Import BishopNotations.

Open Scope bishop_scope.

Reserved Notation "A \ B" (at level 30, right associativity).

Inductive poly := X | add (_ _: poly) | mul (_ _:poly) | O | I.

Definition eval (x: nat) :=
  fix loop p :=
    match p with
    | X => x
    | add L R => loop L + loop R
    | mul L R => loop L * loop R
    | O => 0
    | I => 1
    end.

#[program]
Instance poly_Setoid: Setoid poly := {|
  equiv x y := ∀ t, eval t x = eval t y ;
|}.

Next Obligation.
Proof.
  exists.
  - intro.
    reflexivity.
  - intro.
    symmetry.
    apply (H t).
  - intro.
    symmetry.
    rewrite (H t), (H0 t).
    reflexivity.
Qed.

Add Parametric Morphism : add with signature (@equiv poly _ ==> @equiv poly _ ==> @equiv poly _) as add_mor.
  intros.
  intro t.
  cbn.
  rewrite (H t), (H0 t).
  reflexivity.
Qed.

Add Parametric Morphism : mul with signature (@equiv poly _ ==> @equiv poly _ ==> @equiv poly _) as mul_mor.
  intros.
  intro t.
  cbn.
  rewrite (H t), (H0 t).
  reflexivity.
Qed.

Definition poly_semi_ring: semi_ring_theory O I add mul (@equiv _ poly_Setoid).
Proof.
  cbn.
  exists.
  all: intros; cbn; Psatz.lia.
Qed.

Add Ring poly_semi : poly_semi_ring (abstract).

Definition substitute (x: poly) :=
  fix loop p :=
    match p with
    | X => x
    | add L R => add (loop L) (loop R)
    | mul L R => mul (loop L) (loop R)
    | O => O
    | I => I
    end.

Fixpoint D p :=
  match p with
  | X => I
  | mul L R => add (mul (D L) R) (mul L (D R))
  | add L R => add (D L) (D R)
  | O => O
  | I => O
  end.

Module Import PolynomialNotations.
  Notation "p \ q" := (substitute q p).
  Notation "0" := O.
  Notation "1" := I.
  Notation "p + q" := (add p q).
  Notation "p * q" := (mul p q).
End PolynomialNotations.

Add Parametric Morphism : substitute with signature (@equiv poly _ ==> @equiv poly _ ==> @equiv poly _) as substitute_mor.
  admit.
Admitted.
