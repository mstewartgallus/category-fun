Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Lists.List.
Require Import Coq.setoid_ring.Ring_theory.

Require Psatz.

Import ListNotations.

Reserved Notation "A \ x , B" (at level 100, right associativity, x ident).

Definition poly C := list (list C).

Definition pure {C} (c: C): poly C := [[ c ]].
Definition O {C}: poly C := [].
Definition I {C}: poly C := [[]].
Definition var {C} (c: C): poly C := [[c]].

Definition eval {C} (O: C) (I: C) (add: C → C → C) (mul: C → C → C) (xs: poly C): C :=
  let sum := fold_right add O in
  let prod := fold_right mul I in
  sum (map prod xs).

Definition add {C}: poly C → poly C → poly C := @app _.
(* Define multiplicate in terms of distribution
mul (add n m) p = add (mul n p) (mul m p).
 *)
Definition scale {C} (c: list C): poly C → poly C := map (λ y', app c y').
Definition mul {C} (x: poly C) (y: poly C): poly C :=
  flat_map (λ x', scale x' y) x.

Lemma add_O_l {C} (n: poly C): add O n = n.
Proof.
  unfold add.
  cbn.
  reflexivity.
Qed.

Lemma add_O_r {C} (n: poly C): add n O = n.
Proof.
  unfold add.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma add_assoc {C} (n m p: poly C): add n (add m p) = add (add n m) p.
Proof.
  unfold add.
  cbn in *.
  rewrite app_assoc.
  reflexivity.
Qed.

Lemma mul_I_l {C} (n: poly C): mul I n = n.
Proof.
  unfold mul.
  cbn.
  induction n.
  - cbn.
    reflexivity.
  - cbn in *.
    rewrite IHn.
    reflexivity.
Qed.

Lemma mul_O_l {C} (n: poly C): mul O n = O.
Proof.
  unfold mul, O.
  induction n.
  - cbn.
    reflexivity.
  - cbn in *.
    reflexivity.
Qed.

Lemma mul_O_r {C} (n: poly C): mul n O = O.
Proof.
  unfold mul, scale, O.
  induction n.
  - cbn.
    reflexivity.
  - cbn in *.
    rewrite IHn.
    reflexivity.
Qed.

Lemma distr_l {C} (n m p: poly C): mul (add n m) p = add (mul n p) (mul m p).
Proof.
  unfold mul, add.
  cbn in *.
  repeat rewrite flat_map_app.
  reflexivity.
Qed.

Lemma distr_r {C} (n m p: poly C): mul p (add n m) = add (mul p n) (mul p m).
Proof.
  admit.
Admitted.

Lemma prim_assoc {C} a (m p: poly C): mul (var a) (mul m p) = mul (mul (var a) m) p.
Proof.
  induction m.
  - cbn.
    reflexivity.
  - replace (a0 :: m) with (add [a0] m).
    2: reflexivity.
    repeat rewrite distr_l.
    repeat rewrite distr_r.
    repeat rewrite distr_l.
    repeat rewrite IHm.
    replace (mul (var a) (mul [a0] p)) with (mul (mul (var a) [a0]) p).
    1: reflexivity.
    cbn.
    repeat rewrite app_nil_r.
    unfold scale.
    rewrite map_map.
    cbn.
    reflexivity.
Qed.

Lemma scale_assoc {C} a (m p: poly C): mul [a] (mul m p) = mul (mul [a] m) p.
Proof.
  induction a.
  - replace [[]] with (@I C).
    2: reflexivity.
    repeat rewrite mul_I_l.
    reflexivity.
  - replace [a :: a0] with (mul (var a) [a0]).
    2: reflexivity.
    repeat rewrite app_nil_r in *.
    repeat rewrite <- prim_assoc.
    rewrite IHa.
    reflexivity.
Qed.

Lemma mul_assoc {C} (n m p: poly C): mul n (mul m p) = mul (mul n m) p.
Proof.
  induction n.
  - cbn.
    reflexivity.
  - replace (a :: n) with (add [a] n).
    2: reflexivity.
    repeat rewrite distr_l.
    rewrite IHn.
    rewrite scale_assoc.
    reflexivity.
Qed.

Inductive eqv {C}: relation (poly C) :=
| reflexive : reflexive (poly C) eqv
| symmetric : symmetric (poly C) eqv
| transitive : transitive (poly C) eqv

| add_comm n m : eqv (add n m) (add m n)
| add_compat : Proper (eqv ==> eqv ==> eqv) (@add _)

| mul_comm n m : eqv (mul n m) (mul m n)
| mul_compat : Proper (eqv ==> eqv ==> eqv) (@add _)
.

Existing Instance add_compat.
Existing Instance mul_compat.

#[program]
Instance poly_Setoid C: Setoid (poly C) := {|
  equiv := eqv ;
|}.

Next Obligation.
Proof.
  exists.
  - apply reflexive.
  - apply symmetric.
  - apply transitive.
Qed.

Theorem poly_semi_ring C: semi_ring_theory O I add mul (@equiv _ (poly_Setoid C)).
Proof.
  exists.
  - intros.
    rewrite add_O_l.
    reflexivity.
  - intros.
    rewrite add_comm.
    reflexivity.
  - intros.
    rewrite add_assoc.
    reflexivity.
  - intros.
    rewrite mul_I_l.
    reflexivity.
  - intros.
    rewrite mul_O_l.
    reflexivity.
  - intros.
    rewrite mul_comm.
    reflexivity.
  - intros.
    rewrite mul_assoc.
    reflexivity.
  - intros.
    rewrite distr_l.
    reflexivity.
Qed.

Definition map {A B} (f: A → B) (x: poly A): poly B := map (map f) x.
(* Monadic join is substitution *)
Definition join {C}: poly (poly C) → poly C := eval O I add mul.

Definition bind {A B} (x:poly A) (f: A → poly B): poly B := join (map f x).

Module Import PolynomialNotations.
  Notation "A \ x , B" := (bind A (λ x, B)).
  Notation "0" := O.
  Notation "1" := I.
  Notation "p + q" := (add p q).
  Notation "p * q" := (mul p q).
End PolynomialNotations.
