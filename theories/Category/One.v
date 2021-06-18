Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Monoid.
Require Blech.Pointed.

Require Blech.Reflect.

Import BishopNotations.
Import CategoryNotations.
Import MonoidNotations.

Open Scope bishop_scope.
Open Scope category_scope.
Open Scope monoid_scope.

Reserved Notation "'𝑩₊'".


Obligation Tactic := Reflect.category_simpl.

#[program]
 Definition One (M: Monoid): Pointed.Category := {|
  Pointed.C := {|
                Obj := True ;
                Mor _ _ := M ;

                id _ := ∅ ;
                compose _ _ _ := app ;
              |} ;
  Pointed.pt := I ;
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
