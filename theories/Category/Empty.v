Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.

Import BishopNotations.
Import CategoryNotations.

#[program]
Definition Empty: Category := {|
  Obj := False ;
  Mor x := match x with end ;

  id x := match x with end ;
  compose x := match x with end ;
|}.

Solve All Obligations with contradiction.

Module EmptyNotations.
  Notation "∅" := Empty.
End EmptyNotations.
