Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Category.Prod.
Require Import Blech.Category.Typ.
Require Import Blech.Category.Funct.
Require Import Blech.Functor.
Require Import Blech.Functor.Curry.
Require Blech.Reflect.

Import CategoryNotations.
Import FunctorNotations.
Import ProdNotations.
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

Record extension (p: Poly) (x: Type): Type := ext {
  s: pos p ;
  π: dir p s → x ;
}.

Arguments ext {p x}.
Arguments s {p x}.
Arguments π {p x}.

#[local]
Definition ext_rmap {p A B} (f: A → B) (x:extension p A): extension p B :=
  ext _ (λ y, f (π x y)).

#[local]
Definition ext_lmap {p q A} (f: Cofunctor p q) (x:extension p A): extension q A :=
  ext (Mor_pos f (s x)) (λ y, π x (Mor_dir f y)).

#[program]
Definition Extension: Functor Poly (Funct Typ Typ) := curry {|
  op (px: Poly * Typ) := extension (fst px) (snd px) : Typ ;
  map '(p, A) '(q, B) '(F, G) x := ext_rmap G (ext_lmap F x) ;
|}.

Next Obligation.
Proof.
  intros [? ?] [? ?] [p q].
  unfold ext_lmap, ext_rmap in *.
  cbn in *.
  subst.
  reflexivity.
Qed.
