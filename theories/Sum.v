Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Functor.
Require Import Blech.Bsh.
Require Import Blech.Some.
Require Blech.Bishops.
Require Blech.Reflect.

Import CategoryNotations.
Import BishopNotations.
Import Bishops.BishopsNotations.
Import SomeNotations.
Import FunctorNotations.

Open Scope category_scope.
Open Scope bishop_scope.

Close Scope nat.

Obligation Tactic := Reflect.category_simpl.

(* Still have no good idea how to write this. *)

    Bsh
      (match A with
       | inl A' => D x A'
       | _ => Bishops.False
       end)
      (match B with
       | inl B' => D x B'
       | _ => Bishops.True
       end) ;

  right x:
    Bsh
      (match A with
       | inr A' => E x A'
       | _ => Bishops.False
       end)
      (match B with
       | inr B' => E x B'
       | _ => Bishops.True
       end) ;
}.

Arguments left [D E A B].
Arguments right [D E A B].

#[local]
 Definition sum_eq {D E: Category} {A B: D + E} (f g: sum_mor A B): Prop :=
  (∀ t, left f t == left g t) ∧ (∀ t, right f t == right g t).

#[program]
Definition Sum (D E: Category): Category := {|
  Obj := D + E ;
  Mor A B := sum_mor A B /~ {| equiv := sum_eq |} ;

  id A :=
    match A with
      | inl _ => {| left _ := id _ |}
      | inr _ => {| right _ := id _ |}
    end ;
|}.

Next Obligation.
Proof.
  exists.
  - intros ?.
    split.
    all: reflexivity.
  - intros ? ? p.
    destruct p.
    split.
    all: symmetry.
    all: auto.
  - intros ? ? ? p q.
    destruct p as [p p'], q as [q q'].
    split.
    + intro.
      rewrite (p _), (q _).
      reflexivity.
    + intro.
      rewrite (p' _), (q' _).
      reflexivity.
Qed.

Next Obligation.
Proof.
  exists (λ x: False, match x with end).
  intro.
  contradiction.
Qed.

Next Obligation.
Proof.
  exists (λ x: False, match x with end).
  intro.
  contradiction.
Qed.

Next Obligation.
Proof.
  exists.
  - destruct A, B, C.
    all: intros.
    all: try contradiction.
    all: try (apply (match valid X with end)).
    all: try (apply (match valid X0 with end)).
    + apply (left X ∘ left X0).
    + apply I.
  - destruct A, B, C.
    all: try (apply (match valid X with end)).
    all: try (apply (match valid X0 with end)).
    + apply I.
    + apply (right X ∘ right X0).
  - destruct A, B, C.
    all: try (apply (match valid X with end)).
    all: try (apply (match valid X0 with end)).
    all: apply I.
Defined.

Next Obligation.
Proof.
  destruct A, B, C, D0.
  all: try (apply (match valid f with end)).
  all: try (apply (match valid g with end)).
  all: try (apply (match valid h with end)).
  - split.
    + apply compose_assoc.
    + apply I.
  - split.
    + apply I.
    + apply compose_assoc.
Qed.

Next Obligation.
Proof.
  destruct A, B.
  all: try (apply (match valid f with end)).
  - split.
    + apply compose_id_left.
    + apply I.
  - split.
    + apply I.
    + apply compose_id_left.
Qed.

Next Obligation.
Proof.
  destruct A, B.
  all: try (apply (match valid f with end)).
  - split.
    + apply compose_id_right.
    + apply I.
  - split.
    + apply I.
    + apply compose_id_right.
Qed.

Next Obligation.
Proof.
  destruct A, B, C.
  all: try (apply (match valid f with end)).
  all: try (apply (match valid f' with end)).
  all: try (apply (match valid g with end)).
  all: try (apply (match valid g' with end)).
  all: split.
  all: cbn in *.
  2,3: apply I.
  all: apply compose_compat.
  all: destruct H, H0.
  all: assumption.
Qed.

Module Export SumNotations.
  Infix "+" := Sum : category_scope.
End SumNotations.
