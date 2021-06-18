Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Blech.Bishops.
Require Blech.Reflect.

Import CategoryNotations.
Import BishopNotations.

Open Scope category_scope.
Open Scope bishop_scope.

Obligation Tactic := Reflect.category_simpl.

#[program]
Definition Trv: Category := {|
  Obj := True ;
  Mor _ _ := Bishops.True  ;

  id _ := I ;
  compose _ _ _ _ _ := I ;
|}.


Module TrvNotations.
  Notation "·" := Trv.
End TrvNotations.
