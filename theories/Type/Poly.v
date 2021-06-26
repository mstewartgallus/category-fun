Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Lists.List.

Require Psatz.

Import ListNotations.

Reserved Notation "A \ x , B" (at level 100, right associativity, x ident).

(* Unfortunately the builtin solver cannot be used because it expects
semirings to have commutative multiplication which is wrong *)

Definition poly C := list (list C).

Definition O {C}: poly C := [].
Definition I {C}: poly C := [[]].

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

Inductive eqv {C}: relation (list C) :=
| reflexive : reflexive (list C) eqv
| symmetric : symmetric (list C) eqv
| transitive : transitive (list C) eqv

| app_comm n m : eqv (app n m) (app m n)
| app_compat : Proper (eqv ==> eqv ==> eqv) (@app _)
.

Existing Instance app_compat.

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

(* Monadic join is substitution *)
Definition join {C} (xs: poly (poly C)): poly C :=
  let sum := fold_right add O in
  let prod := fold_right mul I in
  sum (map prod xs).

Definition map {A B} (f: A → B) (x: poly A): poly B := map (map f) x.

Definition bind {A B} (x:poly A) (f: A → poly B): poly B := join (map f x).

Definition var {C} (c: C): poly C := [[c]].

Module Import PolynomialNotations.
  Notation "A \ x , B" := (bind A (λ x, B)).
  Notation "0" := O.
  Notation "1" := I.
  Notation "p + q" := (add p q).
  Notation "p * q" := (mul p q).
End PolynomialNotations.

