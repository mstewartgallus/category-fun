Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Functor.
Require Blech.Reflect.

Import CategoryNotations.
Import FunctorNotations.
Import BishopNotations.

Open Scope category_scope.
Open Scope bishop_scope.

#[local]
Obligation Tactic := Reflect.category_simpl.

#[universes(cumulative)]
Record Arena := {
  pos: Type ;
  dir: pos -> Type ;
}.

#[universes(cumulative)]
Record Cofunctor (p q: Arena) := {
  Mor_pos: pos p → pos q ;
  Mor_dir {i: pos p}: dir q (Mor_pos i) → dir p i ;
}.

Arguments Mor_pos {p q}.
Arguments Mor_dir {p q} c {i}.

(* FIXME Poly should actually be a bicategory ? *)
#[program]
Definition Poly: Category := {|
  Obj := Arena ;
  Mor := Cofunctor ;
  Mor_Setoid _ _ := {| equiv := eq |} ;

  id A :=
    {|
      Mor_pos x := x ;
      Mor_dir i x := x ;
    |} ;
  compose A B C f g :=
    {|
      Mor_pos x := Mor_pos f (Mor_pos g x) ;
      Mor_dir i x := Mor_dir g (Mor_dir f x) ;
    |} ;
|}.
