Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Bishop.Exp.

Import BishopNotations.

Close Scope nat.

Definition sum_eqv (A B: Bishop) (x y: A + B) :=
  match (x, y) with
  | (inl x', inl y') => x' == y'
  | (inr x', inr y') => x' == y'
  | _ => False
  end.

#[program]
Definition sum (A B: Bishop): Bishop := (A + B) /~ {| equiv := sum_eqv A B |}.

Next Obligation.
Proof.
  admit.
Admitted.

#[program]
Definition fanin {C A B: Bishop} (f: exp A C) (g: exp B C): exp (sum A B) C := λ x,
                                                                          match x with
                                                                          | inl x' => f x'
                                                                          | inr x' => g x'
                                                                          end.

Next Obligation.
Proof.
  admit.
Admitted.

#[program]
Definition inl {A B: Bishop}: exp A (sum A B) := inl.

Next Obligation.
Proof.
  intros ? ? p.
  cbn.
  assumption.
Qed.

#[program]
Definition inr {A B: Bishop}: exp B (sum A B) := inr.

Next Obligation.
Proof.
  intros ? ? p.
  cbn.
  assumption.
Qed.

Module SumNotations.
  Infix "+" := sum : bishop_scope.
End SumNotations.
