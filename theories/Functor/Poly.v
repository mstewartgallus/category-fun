Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Bicategory.
Require Import Blech.Functor.

Require Import Blech.Category.Comma.
Require Import Blech.Category.Op.
Require Import Blech.Bicategory.Cat.
Require Import Blech.Bicategory.Over.

Require Blech.Reflect.

Import CategoryNotations.
Import OpNotations.
Import FunctorNotations.
Import BishopNotations.


Open Scope category_scope.
Open Scope bishop_scope.

#[local]
Obligation Tactic := Reflect.category_simpl.


Definition Σ {B: Bicategory} {C D} (F: B C D) (P: Over B C): Over B D :=
  {|
    pos := pos P ;
    dir := compose (F, dir P) ;
  |}.

(* Vaguely corresponds to substitution/composition *)

#[program]
#[local]
Definition dom {A B C} (F: Functor A C) (G: Functor B C): Functor (Comma F G) A :=
  {|
  op x := s x ;
  map _ _ f := s_Mor f ;
  |}.

Next Obligation.
Proof.
  intros ? ? [p ?].
  rewrite p.
  reflexivity.
Qed.

#[program]
Definition Basechange {C D} (F: Functor D C) (P: Over Cat C): Over Cat D :=
  {|
    pos := Comma F (dir P) ;
    dir := dom F (dir P) ;
  |}.

Module Import PolyNotations.
  Infix "*" := Basechange.
End PolyNotations.
