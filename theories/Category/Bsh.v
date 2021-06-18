Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

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

  id _ x := x ;
  compose _ _ _ f g x := f (g  x) ;
|}.

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
  rewrite (H _).
  apply (proj2_sig f').
  rewrite (H0 _).
  reflexivity.
Qed.

Add Parametric Morphism {A B} (f: Bsh A B) : (proj1_sig f)
    with signature equiv ==> equiv as fn_mor.
Proof.
  intros.
  destruct f.
  cbn.
  auto.
Qed.

Definition simple (t:Type): Bsh := t /~ {| equiv := eq |}.
