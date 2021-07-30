Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.Bsh.
Require Import Blech.Category.
Require Import Blech.Monoid.
Require Import Blech.Group.
Require Blech.Reflect.

Import CategoryNotations.
Import MonoidNotations.
Import GroupNotations.
Import BishopNotations.

Open Scope morphism_scope.
Open Scope group_scope.
Open Scope bishop_scope.
Open Scope monoid_scope.

#[local]
Obligation Tactic := Reflect.category_simpl.

Class Grp_Mor [A B: Group] (F: A → B): Prop := {
  map_e: F e == e ;
  map_app x y: F (x · y) == F x · F y ;
  map_invert x: F (x ⁻¹) == F x ⁻¹ ;
}.

#[program]
Definition Grp: Category := {|
  Obj := Group ;
  Mor A B := {f: Bsh A B | Grp_Mor f} /~ {| equiv x y := proj1_sig x == proj1_sig y |};

  id _ := exist _ (id _) _ ;
  compose _ _ _ f g := exist _ (proj1_sig f ∘ g) _ ;
|}.

Next Obligation.
Proof.
  admit.
Admitted.

Next Obligation.
Proof.
  admit.
Admitted.

Next Obligation.
Proof.
  admit.
Admitted.
