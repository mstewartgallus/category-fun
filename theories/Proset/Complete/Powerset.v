Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Proset.
Require Import Blech.Proset.Complete.
Require Import Blech.Proset.Op.
Require Import Blech.Proset.Sub.
Require Import Blech.Category.
Require Import Blech.Category.PreOrd.
Require Import Blech.Category.Bsh.
Require Import Blech.Category.Over.
Require Import Blech.Monic.
Require Import Blech.Monic.Mono.
Require Import Blech.Type.Some.
Require Blech.Reflect.

Import BishopNotations.
Import CategoryNotations.
Import ProsetNotations.
Import OpNotations.
Import OverNotations.
Import SomeNotations.

Open Scope category_scope.
Open Scope bishop_scope.

(* The powerset can be considered the free CABA *)
#[program]
 Definition Powerset (S: Proset): Complete := {|
  P :=
    {|
      T := S → Prop ;
      preorder p q := ∀ x, q x → p x ;
    |}
|}.

Next Obligation.
Proof.
  exists.
  - intros ? ? t.
    apply t.
  - intros ? ? ? p q ? ?.
    apply p.
    apply q.
    assumption.
Qed.

Next Obligation.
Proof.
  destruct X.
  cbn in *.
  apply (∀ a, x a X0).
Qed.

Next Obligation.
Proof.
  destruct X.
  cbn in *.
  apply (∀ a, x a X0).
Qed.

(* Doesn't seem right to me ? *)
#[program]
Definition Yo (S: Proset): PreOrd (S ᵒᵖ) (Powerset S) := λ x y, y ⊑ x.

Next Obligation.
Proof.
  intros ? ? p ? q.
  cbn in *.
  rewrite q.
  apply p.
Qed.

#[program]
 Definition Spec S: PreOrd (Powerset (S ᵒᵖ)) (Powerset S) := λ p x, p x.

Next Obligation.
Proof.
  intros ? ? p ? x.
  cbn in *.
  apply (p _ x).
Defined.

#[program]
 Definition Cospec S: PreOrd (Powerset S) (Powerset (S ᵒᵖ)) := λ p x, p x.

Next Obligation.
Proof.
  intros ? ? p ? x.
  cbn in *.
  apply (p _ x).
Defined.
