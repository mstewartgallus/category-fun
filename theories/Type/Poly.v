Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.setoid_ring.Ring_theory.

Require Psatz.

Reserved Notation "A \ x , B" (at level 100, right associativity, x ident).

Inductive poly C := var (_: C) | add (_ _: poly C) | mul (_ _:poly C) | O | I.

Arguments var {C}.
Arguments add {C}.
Arguments mul {C}.
Arguments O {C}.
Arguments I {C}.

Inductive eqv {C}: relation (poly C) :=
| reflexive : reflexive (poly C) eqv
| symmetric : symmetric (poly C) eqv
| transitive : transitive (poly C) eqv

| add_O_l n : eqv (add O n) n
| add_comm n m : eqv (add n m) (add m n)
| add_assoc n m p : eqv (add n (add m p)) (add (add n m) p)

| mul_I_l n : eqv (mul I n) n
| mul_O_l n : eqv (mul O n) O

| mul_comm n m : eqv (mul n m) (mul m n)
| mul_assoc n m p : eqv (mul n (mul m p)) (mul (mul n m) p)

| distr_l n m p : eqv (mul (add n m) p) (add (mul n p) (mul m p))

| add_compat : Proper (eqv ==> eqv ==> eqv) add
| mul_compat : Proper (eqv ==> eqv ==> eqv) mul
.

#[program]
Instance poly_Setoid C: Setoid (poly C) := {|
  equiv := @eqv C;
|}.

Next Obligation.
Proof.
  exists.
  - apply reflexive.
  - apply symmetric.
  - apply transitive.
Qed.

Existing Instance add_compat.
Existing Instance mul_compat.

Definition poly_semi_ring C: semi_ring_theory O I add mul (@equiv _ (poly_Setoid C)) :=
  {|
    SRadd_0_l := add_O_l ;
    SRadd_comm := add_comm ;
    SRadd_assoc := add_assoc ;
    SRmul_1_l := mul_I_l ;
    SRmul_0_l := mul_O_l ;
    SRmul_comm := mul_comm ;
    SRmul_assoc := mul_assoc ;
    SRdistr_l := distr_l ;
 |}.

(* Substitution of polynomials is just monadic join *)
Fixpoint join {C} (p : poly (poly C)): poly C :=
  match p with
  | var x => x
  | add L R => add (join L) (join R)
  | mul L R => mul (join L) (join R)
  | O => O
  | I => I
  end.

Definition map {A B} (f: A → B): poly A → poly B :=
  fix loop p :=
    match p with
    | var x => var (f x)
    | add L R => add (loop L) (loop R)
    | mul L R => mul (loop L) (loop R)
    | O => O
    | I => I
    end.

Definition bind {A B} (x:poly A) (f: A → poly B): poly B := join (map f x).

Fixpoint eval (p: poly nat) :=
  match p with
  | var n => n
  | mul L R => eval L * eval R
  | add L R => eval L + eval R
  | O => 0
  | I => 1
  end.

Fixpoint D {C} (p: poly C): poly C :=
  match p with
  | var xs => I
  | mul L R => add (mul (D L) R) (mul L (D R))
  | add L R => add (D L) (D R)
  | O => O
  | I => O
  end.

Module Import PolynomialNotations.
  Notation "A \ x , B" := (bind A (λ x, B)).
  Notation "0" := O.
  Notation "1" := I.
  Notation "p + q" := (add p q).
  Notation "p * q" := (mul p q).
End PolynomialNotations.

Inductive XS := X.
