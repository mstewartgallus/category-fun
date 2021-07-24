Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Type.Predicate.
Require Import Blech.Bishop.
Require Import Blech.Bishop.Exp.
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
  Mor := exp;
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
  apply (proj2_sig f).
  apply (proj2_sig g).
  assumption.
Qed.

Next Obligation.
Proof.
  intros f g p f' g' q x.
  cbn in *.
  rewrite (p _), (q _).
  reflexivity.
Qed.
