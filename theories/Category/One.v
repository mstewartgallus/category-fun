Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Monoid.
Require Blech.PointedCategory.

Require Blech.Reflect.

Import BishopNotations.
Import CategoryNotations.
Import MonoidNotations.

Open Scope bishop_scope.
Open Scope category_scope.
Open Scope monoid_scope.

Reserved Notation "'𝑩₊'".


#[local]
Obligation Tactic := Reflect.category_simpl.

#[program]
 Definition One (M: Monoid): PointedCategory.Category := {|
  PointedCategory.C := {|
                Obj := True ;
                Mor _ _ := M ;

                id _ := ∅ ;
                compose _ _ _ := app ;
              |} ;
  PointedCategory.pt := I ;
|}.

Next Obligation.
Proof.
  apply app_assoc.
Qed.

Next Obligation.
Proof.
  apply app_unit_left.
Qed.

Next Obligation.
Proof.
  apply app_unit_right.
Qed.

Next Obligation.
Proof.
  rewrite H, H0.
  reflexivity.
Qed.


Module OneNotations.
  Notation "'𝑩₊'" := One.
End OneNotations.