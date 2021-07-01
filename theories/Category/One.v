Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Monoid.
Require Blech.PointedCategory.

Require Blech.Monoid.Reflect.

Import BishopNotations.
Import CategoryNotations.
Import MonoidNotations.

Open Scope bishop_scope.
Open Scope category_scope.
Open Scope monoid_scope.

Reserved Notation "'𝑩₊'".

#[local]
Obligation Tactic := Reflect.monoid_simpl.

#[program]
 Definition One (M: Monoid): PointedCategory.Category := {|
  PointedCategory.C := {|
                Obj := True ;
                Mor _ _ := M ;

                id _ := e ;
                compose _ _ _ := app ;
              |} ;
  PointedCategory.pt := I ;
|}.

Module OneNotations.
  Notation "'𝑩₊'" := One.
End OneNotations.
