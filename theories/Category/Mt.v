Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Category.

Import CategoryNotations.

#[program]
Definition Mt: Category := {|
  Obj := False ;
  Mor x := match x with end ;

  id x := match x with end ;
  compose x := match x with end ;
|}.

Solve All Obligations with contradiction.

Module MtNotations.
  Notation "∅" := Mt : category_scope.
End MtNotations.
