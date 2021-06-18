Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Categories.Bsh.
Require Blech.Reflect.

Import BishopNotations.
Import CategoryNotations.

Open Scope bishop_scope.
Open Scope category_scope.

Close Scope nat.


Obligation Tactic := Reflect.category_simpl.


Definition simple (t:Type): Bishop := t /~ {| equiv := eq |}.

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
Definition fanin {C A B: Bishop} (f: Bsh A C) (g: Bsh B C): Bsh (sum A B) C := λ x,
                                                                          match x with
                                                                          | inl x' => f x'
                                                                          | inr x' => g x'
                                                                          end.

Next Obligation.
Proof.
  admit.
Admitted.

#[program]
Definition inl {A B: Bishop}: Bsh A (sum A B) := inl.

Next Obligation.
Proof.
  intros ? ? p.
  cbn.
  assumption.
Qed.

#[program]
Definition inr {A B: Bishop}: Bsh B (sum A B) := inr.

Next Obligation.
Proof.
  intros ? ? p.
  cbn.
  assumption.
Qed.

#[program]
Definition True: Bishop := True /~ {| equiv _ _ := True |}.

Next Obligation.
Proof.
  exists.
  all:exists.
Qed.

#[program]
 Definition bang {A}: Bsh A True := λ _, I.

#[program]
 Definition False: Bishop := False /~ {| equiv x := match x with end |}.

Next Obligation.
Proof.
  exists.
  all:intro;contradiction.
Qed.


#[program]
 Definition const [A: Bishop] (x: A): Bsh True A := λ _, x.

Next Obligation.
Proof.
  intros ? ? p.
  reflexivity.
Qed.

#[program]
 Definition prod (A B: Bishop): Bishop := A * B /~ {| equiv x y := fst x == fst y ∧ snd x == snd y |}.

Next Obligation.
Proof.
  exists.
  all: unfold Reflexive, Symmetric, Transitive.
  - split.
    all: reflexivity.
  - split.
    all: symmetry.
    all: apply H.
  - intros ? ? ? p q.
    destruct p as [p p'], q as [q q'].
    rewrite p, q, p', q'.
    split.
    all: reflexivity.
Qed.

#[program]
 Definition fanout {C A B: Bishop} (f: Bsh C A) (g: Bsh C B): Bsh C (prod A B) := λ x, (f x, g x).

Next Obligation.
Proof.
  admit.
Admitted.


#[program]
 Definition fst {A B: Bishop}: Bsh (prod A B) A := fst.

Next Obligation.
Proof.

  intros ? ? p.
  destruct p as [p q].
  apply p.
Qed.

#[program]
 Definition snd {A B: Bishop}: Bsh (prod A B) B := snd.

Next Obligation.
Proof.
  intros ? ? p.
  destruct p as [p q].
  apply q.
Qed.

Module BishopsNotations.
  Infix "*" := prod : bishop_scope.
End BishopsNotations.
