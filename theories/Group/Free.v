Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Monoid.
Require Import Blech.Group.

Import BishopNotations.
Import MonoidNotations.
Import GroupNotations.

Open Scope bishop_scope.
Open Scope monoid_scope.
Open Scope group_scope.

(* The abstract AST of a monoid subject to setoid quotient. Very
inefficient. You probably want List *)

#[universes(cumulative)]
Inductive free (S: Bishop) := η (_: S) | e | app (_ _: free S) | invert (_: free S).

Arguments η {S}.
Arguments e {S}.
Arguments app {S}.
Arguments invert {S}.

Inductive equiv {S: Bishop} : relation (free S) :=
| reflexive: reflexive _ equiv
| symmetric: symmetric _ equiv
| transitive: transitive _ equiv

| η_compat: Proper (SetoidClass.equiv ==> equiv) η

| app_assoc f g h: equiv (app f (app g h)) (app (app f g) h)
| app_e_left f: equiv (app e f) f
| app_e_right f: equiv (app f e) f

| app_compat: Proper (equiv ==> equiv ==> equiv) app

| app_invert_left f: equiv (app (invert f) f) e
| app_invert_right f: equiv (app f (invert f)) e

| invert_compat: Proper (equiv ==> equiv) invert
.
#[global]
Existing Instance η_compat.
#[global]
Existing Instance app_compat.
#[global]
Existing Instance invert_compat.

#[global]
#[program]
Instance free_Setoid (S: Bishop): Setoid (free S) := {
  equiv := equiv ;
}.
Next Obligation.
Proof.
  exists.
  - apply reflexive.
  - apply symmetric.
  - apply transitive.
Qed.

Definition Free (S: Bishop): Group := {|
  M := {|
    S := free S /~ free_Setoid S ;

    Monoid.e := e ;
    Monoid.app := app ;

    Monoid.app_assoc := app_assoc ;
    Monoid.app_e_left := app_e_left ;
    Monoid.app_e_right := app_e_right ;
    Monoid.app_compat := app_compat ;
  |} ;

  Group.invert := invert ;
  Group.app_invert_left := app_invert_left ;
  Group.app_invert_right := app_invert_right ;
  Group.invert_compat := invert_compat ;
|}.

Fixpoint ε {G: Group} (g: Free G): G :=
  match g with
  | η x => x
  | e => Monoid.e
  | app x y => ε x · ε y
  | invert x => (ε x) ⁻¹
  end.
