Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Blech.Reflect.

Import CategoryNotations.
Import BishopNotations.

Open Scope category_scope.
Open Scope bishop_scope.


Reserved Notation "C 'ᵒᵖ'" (at level 1).


#[local]
Obligation Tactic := Reflect.category_simpl.


#[program]
Definition Op (K: Category): Category := {|
  Obj := K ;
  Mor A B := K B A ;

  id A := @id K A ;
  compose A B C f g := g ∘ f ;

  compose_id_left _ _ := @compose_id_right K _ _ ;
  compose_id_right _ _ := @compose_id_left K _ _ ;
  compose_compat _ _ _ f f' g g' p q := compose_compat _ _ _ _ q p ;
|}.


Module OpNotations.
  Notation "C 'ᵒᵖ'" := (Op C).
End OpNotations.
