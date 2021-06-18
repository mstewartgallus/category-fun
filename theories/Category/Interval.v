Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Bool.Bool.

Require Import Blech.Bishop.
Require Import Blech.Category.

Require Blech.Reflect.

Import BishopNotations.
Import CategoryNotations.

Open Scope bishop_scope.
Open Scope category_scope.

Reserved Notation "'I₊'".

Obligation Tactic := Reflect.category_simpl.

#[program]
Definition Interval: Category := {|
  Obj := bool ;
  Mor A B := Is_true (implb B A) /~ {| equiv _ _ := True |} ;
|}.

Next Obligation.
Proof.
  exists.
  all: exists.
Qed.

Next Obligation.
Proof.
  destruct A.
  all: cbn.
  all: exists.
Defined.

Next Obligation.
Proof.
  destruct A, B, C.
  all: cbn in *.
  all: try contradiction.
  all: exists.
Defined.

Module IntervalNotations.
  Notation "'I₊'" := Interval.
End IntervalNotations.
