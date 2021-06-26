Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Bishop.Mt.
Require Import Blech.Category.
Require Import Blech.Functor.
Require Import Blech.Type.Some.
Require Blech.Reflect.

Import CategoryNotations.
Import BishopNotations.
Import FunctorNotations.
Import SomeNotations.

Open Scope category_scope.
Open Scope bishop_scope.

Close Scope nat.


#[local]
Obligation Tactic := Reflect.category_simpl.

Section sum.
  Context {C D: Category}.

  Definition sum (A B: C + D) :=
    match (A, B) with
    | (inl A', inl B') => A' ~> B'
    | (inr A', inr B') => A' ~> B'
    | _ => mt
    end.
End sum.

#[program]
 Definition Sum (C D: Category): Category := {|
  Obj := C + D ;
  Mor A B := sum A B ;
|}.

Next Obligation.
Proof.
  destruct A.
  all: cbn.
  all: apply id.
Defined.

Next Obligation.
Proof.
  destruct A, B, C0.
  all: cbn in *.
  all: try contradiction.
  all: apply (X ∘ X0).
Defined.

Next Obligation.
Proof.
  destruct A, B, C0, D0.
  all: cbn in *.
  all: try contradiction.
  all: apply compose_assoc.
Qed.

Next Obligation.
Proof.
  destruct A, B.
  all: cbn in *.
  all: try contradiction.
  all: apply compose_id_left.
Qed.

Next Obligation.
Proof.
  destruct A, B.
  all: cbn in *.
  all: try contradiction.
  all: apply compose_id_right.
Qed.

Next Obligation.
Proof.
  intros ? ? p ? ? q.
  destruct A, B, C0.
  all: cbn in *.
  all: try contradiction.
  all: rewrite p, q.
  all: reflexivity.
Qed.

Module Export SumNotations.
  Infix "+" := Sum : category_scope.
End SumNotations.
