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
Definition Typ: Category := {|
  Obj := Type ;
  Mor A B := (A -> B) /~ {| equiv := eq |};

  id _ x := x ;
  compose _ _ _ f g x := f (g  x) ;
|}.
