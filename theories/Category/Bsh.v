Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Blech.Reflect.

Import CategoryNotations.
Import BishopNotations.

Open Scope category_scope.
Open Scope bishop_scope.


#[local]
Obligation Tactic := Reflect.category_simpl.

#[program]
Definition Bsh: Category := {|
  Obj := Bishop ;
  Mor A B := {f: A → B | Proper (equiv ==> equiv) f };
  Mor_Setoid _ _ := {| equiv f g := ∀ x, f x == g x |};

  id _ x := x ;
  compose _ _ _ f g x := f (g x) ;
|}.

Next Obligation.
Proof.
  exists.
  - intros ? ?.
    reflexivity.
  - intros ? ? p ?.
    rewrite (p _).
    reflexivity.
  - intros ? ? ? p q ?.
    rewrite (p _).
    rewrite (q _).
    reflexivity.
Qed.

Next Obligation.
Proof.
  intros ? ? ?.
  assumption.
Qed.

Next Obligation.
Proof.
  intros ? ? ?.
  rewrite H1.
  reflexivity.
Qed.

Next Obligation.
Proof.
  intros f g p f' g' q x.
  cbn in *.
  rewrite (p _).
  apply (proj2_sig g).
  rewrite (q _).
  reflexivity.
Qed.

Definition Mor_proj {A B}: Bsh A B → A → B := @proj1_sig _ _.

Definition Mor_Proper {A B}: ∀ (f: Bsh A B), Proper _ _ := @proj2_sig _ _.
Existing Instance Mor_Proper.

Instance curry_Proper (A B: Bishop): Proper (@equiv _ (@Mor_Setoid Bsh A B) ==> equiv ==> equiv) ( @proj1_sig (A → B) (Proper (@equiv _ Bishop_Setoid ==> @equiv _ Bishop_Setoid))).
Proof.
  intros ? ? p ? ? q.
  rewrite q.
  apply p.
Defined.
