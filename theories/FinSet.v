Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Bsh.
Require Import Blech.Category.
Require Blech.Reflect.

Import CategoryNotations.
Import BishopNotations.

Open Scope category_scope.
Open Scope bishop_scope.


#[local]
#[program]
Definition fin N := {x | x ≤ N} /~ {| equiv x y := proj1_sig x = proj1_sig y |}.

Next Obligation.
Proof.
  cbn in *.
  exists.
  - intros ?.
    reflexivity.
  - intros ? ? ?.
    symmetry.
    assumption.
  - intros ? ? ? p q.
    rewrite p, q.
    reflexivity.
Qed.

#[program]
Definition FinSet: Category := {|
  Obj := nat ;
  Mor A B := Bsh (fin A) (fin B) ;

  id _ := id _ ;
  compose _ _ _ := @compose _ _ _ _ ;

  compose_assoc _  _ _ _ f g h := @compose_assoc Bsh _ _ _ _ f g h ;
  compose_id_left _ _ f := @compose_id_left Bsh _ _ f ;
  compose_id_right _ _ f := @compose_id_right Bsh _ _ f ;
|}.

Next Obligation.
Proof.
  apply (@compose_compat Bsh _ _ _ f f' g g').
  all: assumption.
Qed.
