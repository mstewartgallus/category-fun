Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Bool.Bool.

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


Reserved Notation "'I₊'".
Reserved Notation "'S₁₊'".


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

Module CategoriesNotations.
  Notation "'I₊'" := Interval.
  Notation "'𝑩₊'" := One.
End CategoriesNotations.

#[program]
Definition Empty: Category := {|
  Obj := False ;
  Mor x := match x with end ;
  id x := match x with end ;
  compose x := match x with end ;
|}.

Solve All Obligations with contradiction.
