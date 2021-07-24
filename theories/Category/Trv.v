Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Bishop.Trv.
Require Import Blech.Category.
Require Blech.Reflect.

Import CategoryNotations.
Import BishopNotations.

Open Scope category_scope.

#[local]
Obligation Tactic := Reflect.category_simpl.

#[program]
Definition Trv: Category := {|
  Obj := True ;
  Mor _ _ := True  ;
  Mor_Setoid _ _ := {| equiv _ _ := True |} ;

  id _ := I ;
  compose _ _ _ _ _ := I ;
|}.

Next Obligation.
Proof.
  exists.
  all: exists.
Qed.

Module TrvNotations.
  Notation "·" := Trv : category_scope.
End TrvNotations.
