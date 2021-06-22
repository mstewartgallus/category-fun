Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Functor.
Require Import Blech.Category.Bsh.
Require Import Blech.Category.Funct.
Require Import Blech.Category.Prod.
Require Import Blech.Category.CoPSh.
Require Import Blech.Category.Op.
Require Import Blech.Functor.Curry.
Require Blech.Reflect.

Import CategoryNotations.
Import FunctorNotations.
Import BishopNotations.
Import ProdNotations.
Import OpNotations.

Open Scope category_scope.
Open Scope bishop_scope.

#[local]
Obligation Tactic := Reflect.category_simpl.

#[program]
 Definition CoYo C: Funct (C ᵒᵖ) (CoPSh C) := curry {|
  op (ab: (C ᵒᵖ) * C) := C (fst ab) (snd ab): Bsh ;
  map _ _ '(a, b) (f: C _ _) := (b: C _ _) ∘ f ∘ (a : C _ _) ;
|}.

Next Obligation.
Proof.
  cbn in *.
  intros ? ? p.
  rewrite p.
  reflexivity.
Qed.

Next Obligation.
Proof.
  intros ? ? p ?.
  destruct p as [p q].
  cbn in *.
  rewrite p, q.
  reflexivity.
Qed.
