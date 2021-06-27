Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Bishop.Mt.
Require Import Blech.Category.
Require Import Blech.Category.Op.
Require Import Blech.Category.Prod.
Require Import Blech.Category.Bsh.
Require Import Blech.Functor.
Require Import Blech.Type.Some.
Require Blech.Reflect.

Import CategoryNotations.
Import BishopNotations.
Import FunctorNotations.
Import OpNotations.
Import ProdNotations.
Import SomeNotations.

Open Scope category_scope.
Open Scope bishop_scope.

Close Scope nat.


#[local]
Obligation Tactic := Reflect.category_simpl.

Section sum.
  Context {C D E: Category}.

  Definition cograph (F: Functor C E) (G: Functor D E) (A B: C + D) :=
    match (A, B) with
    | (inl A', inr B') => F A' ~> G B'
    | (inl A', inl B') => A' ~> B'
    | (inr A', inr B') => A' ~> B'
    | _ => mt
    end.
End sum.

#[program]
Definition Cograph {C D E: Category} (F: Functor C E) (G: Functor D E): Category := {|
  Obj := C + D ;
  Mor A B := cograph F G A B ;
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
  1,4: apply (X ∘ X0).
  - apply (X ∘ map F X0).
  - apply (map G X ∘ X0).
Defined.

Next Obligation.
Proof.
  destruct A, B, C0, D0.
  all: cbn in *.
  all: try contradiction.
  1,5: apply compose_assoc.
  - rewrite <- map_composes.
    rewrite compose_assoc.
    reflexivity.
  - rewrite compose_assoc.
    reflexivity.
  - rewrite <- map_composes.
    rewrite compose_assoc.
    reflexivity.
Qed.

Next Obligation.
Proof.
  destruct A, B.
  all: cbn in *.
  all: try contradiction.
  2: rewrite map_id.
  all: apply compose_id_left.
Qed.

Next Obligation.
Proof.
  destruct A, B.
  all: cbn in *.
  all: try contradiction.
  2: rewrite map_id.
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
