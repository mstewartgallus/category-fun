Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Bishop.Trv.
Require Import Blech.Bishop.Mt.
Require Import Blech.Category.
Require Import Blech.Functor.
Require Blech.Reflect.

Import CategoryNotations.
Import BishopNotations.
Import FunctorNotations.

Open Scope category_scope.
Open Scope bishop_scope.

Close Scope nat.

#[local]
Obligation Tactic := Reflect.category_simpl.


#[program]
 Definition Opt (C: Category): Category := {|
  Obj := option C ;
  Mor A B :=
    match A with
    | Some A' =>
      match B with
      | Some B' => A' ~> B'
      | _ => mt
      end
    | _ =>
      match B with
      | Some B' => mt
      | _ => trv
      end
    end ;

  id A := match A with
          | Some _ => id _
          | None => I
          end ;
|}.

Next Obligation.
Proof.
  destruct A, B, C0.
  all: try contradiction.
  all: try (apply I).
  apply (X ∘ X0).
Defined.

Next Obligation.
Proof.
  destruct A, B, C0, D.
  all: cbn in *.
  all: try contradiction.
  2: apply I.
  apply compose_assoc.
Qed.

Next Obligation.
Proof.
  destruct A, B.
  all: cbn in *.
  all: try contradiction.
  2: apply I.
  apply compose_id_left.
Qed.

Next Obligation.
Proof.
  destruct A, B.
  all: cbn in *.
  all: try contradiction.
  2: apply I.
  apply compose_id_right.
Qed.

Next Obligation.
Proof.
  intros ? ? p ? ? q.
  destruct A, B, C0.
  all: cbn in *.
  all: try contradiction.
  2: apply I.
  rewrite p, q.
  reflexivity.
Qed.
