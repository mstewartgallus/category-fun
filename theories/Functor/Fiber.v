Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Functor.
Require Import Blech.Category.Bsh.
Require Import Blech.Category.Funct.
Require Import Blech.Category.Prod.
Require Import Blech.Category.El.
Require Import Blech.Category.Over.
Require Import Blech.Category.PSh.
Require Import Blech.Category.Trv.
Require Import Blech.Groupoid.
Require Import Blech.Groupoid.Dis.
Require Import Blech.Category.Op.
Require Import Blech.Functor.Curry.
Require Import Blech.Type.Some.
Require Import Blech.Proset.
Require Blech.Functor.Compose.
Require Blech.Functor.Id.
Require Blech.Reflect.

Import CategoryNotations.
Import FunctorNotations.
Import OverNotations.
Import BishopNotations.
Import ProdNotations.
Import OpNotations.
Import SomeNotations.

Open Scope category_scope.
Open Scope bishop_scope.

#[local]
Obligation Tactic := Reflect.category_simpl.

Class Discrete {C B} (F: Functor C B) := {
  inv: Functor B C ;
  (* FIXME use a less strict notion not even sure is right *)
  to x: F (inv x) = x ;
  from x: inv (F x) = x ;
}.

Arguments inv {C B} F {Discrete}.

(* FIXME make actual functor *)
#[program]
Definition fiber {C B} (F: Functor C B) `{@Discrete _ _ F}: PSh B := {|
  op (x: B ᵒᵖ) := {y: C | x = F y }/~{| equiv f g := proj1_sig f = proj1_sig g |} : Bsh;
  map X Y (f: B ᵒᵖ _ Y) x := inv F Y ;
|}.

Next Obligation.
Proof.
  admit.
Admitted.

Next Obligation.
Proof.
  rewrite to.
  reflexivity.
Qed.

Next Obligation.
Proof.
  rewrite from.
  reflexivity.
Qed.
