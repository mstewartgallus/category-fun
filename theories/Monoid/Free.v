Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Monoid.

Import BishopNotations.
Import MonoidNotations.

Open Scope bishop_scope.
Open Scope monoid_scope.

(* The abstract AST of a monoid subject to setoid quotient. Very
inefficient. You probably want List *)

#[universes(cumulative)]
Inductive free (S: Bishop) := η (_: S) | e | app (_ _: free S).

Arguments η {S}.
Arguments e {S}.
Arguments app {S}.

Inductive equiv {S: Bishop} : relation (free S) :=
| reflexive: reflexive _ equiv
| symmetric: symmetric _ equiv
| transitive: transitive _ equiv

| app_assoc f g h: equiv (app f (app g h)) (app (app f g) h)
| app_e_left f: equiv (app e f) f
| app_e_right f: equiv (app f e) f

| app_compat: Proper (equiv ==> equiv ==> equiv) app
.
Existing Instance app_compat.

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

#[program]
Definition Free (S: Bishop): Monoid := {|
  S := free S /~ free_Setoid S ;

  Monoid.e := e ;
  Monoid.app := app ;

  Monoid.app_assoc := app_assoc ;
  Monoid.app_e_left := app_e_left ;
  Monoid.app_e_right := app_e_right ;
  Monoid.app_compat := app_compat ;
|}.

Fixpoint ε {M: Monoid} (m: Free M): M :=
  match m with
  | η x => x
  | e => Monoid.e
  | app x y => ε x · ε y
  end.
