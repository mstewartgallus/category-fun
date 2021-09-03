Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Type.Some.
Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Functor.
Require Blech.Reflect.

Import CategoryNotations.
Import BishopNotations.
Import FunctorNotations.
Import SomeNotations.

Open Scope category_scope.
Open Scope bishop_scope.


#[local]
Obligation Tactic := Reflect.category_simpl.

Record Pullback [A B C] (F: Functor A C) (G: Functor B C) := arrow {
  s: A ;
  t: B ;
  π: F s ~> G t ;
}.

Arguments arrow [A B C F G].
Arguments s [A B C F G].
Arguments t [A B C F G].
Arguments π [A B C F G].

Record Mor [A B C] [F: Functor A C] [G: Functor B C] (X Y: Pullback F G) := mor {
  s_Mor: s Y ~> s X ;
  t_Mor: t Y ~> t X ;
  π_Mor: π X ∘ map F s_Mor == map G t_Mor ∘ π Y;
}.

Arguments mor [A B C F G X Y].
Arguments s_Mor [A B C F G X Y].
Arguments t_Mor [A B C F G X Y].
Arguments π_Mor [A B C F G X Y].

#[program]
#[local]
Definition id [A B C] [F: Functor A C] [G: Functor B C] (X: Pullback F G): Mor X X :=
  mor (id _) (id _) _.

Next Obligation.
Proof.
  repeat rewrite map_id.
  rewrite compose_id_left.
  rewrite compose_id_right.
  reflexivity.
Qed.


#[program]
#[local]
Definition compose [A B C] (F: Functor A C) (G: Functor B C)
(X Y Z: Pullback F G) (f: Mor Y Z) (g: Mor X Y): Mor X Z :=
  mor (s_Mor g ∘ s_Mor f) (t_Mor g ∘ t_Mor f) _.

Next Obligation.
Proof.
  rewrite <- map_composes.
  repeat rewrite compose_assoc.
  rewrite π_Mor.
  repeat rewrite <- compose_assoc.
  rewrite π_Mor.
  repeat rewrite compose_assoc.
  rewrite <- map_composes.
  reflexivity.
Qed.

#[program]
Definition Comma [A B C] (F: Functor A C) (G: Functor B C) := {|
  Obj := Pullback F G ;
  Category.Mor := @Mor A B C F G ;
  Mor_Setoid _ _ := {|
      equiv x y := s_Mor x == s_Mor y ∧ t_Mor x == t_Mor y ;
    |} ;

  Category.id := @id A B C F G ;
  Category.compose := compose F G ;
|}.

Next Obligation.
Proof.
  exists.
  - intros ?.
    split.
    all: reflexivity.
  - intros ? ? [? ?].
    split.
    all: symmetry.
    all: assumption.
  - intros ? ? ? [p p'] [q q'].
    rewrite p, q.
    rewrite p', q'.
    split.
    all: reflexivity.
Qed.

Next Obligation.
Proof.
  intros ? ? [p p'] ? ? [q q'].
  cbn in *.
  rewrite p, q.
  rewrite p', q'.
  split.
  all: reflexivity.
Qed.
