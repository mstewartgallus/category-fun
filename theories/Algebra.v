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

Obligation Tactic := Reflect.category_simpl.

Module Import Algebra.
  #[universes(cumulative)]
   Record Algebra [C:Category] (F: Funct C C) := {
    s: C ;
    π: F s ~> s
   }.

  Arguments s [C F] _.
  Arguments π [C F] _.
End Algebra.

#[program]
Definition Algebra [C: Category] (F: Funct C C): Category := {|
  Obj := Algebra F ;
  Mor A B:=  {m: s A ~> s B | m ∘ π A == π B ∘ map F m }
               /~
               {| equiv x y := proj1_sig x == proj1_sig y |} ;

  id A := @id _ (s A) ;
  compose A B C := @compose _ (s A) (s B) (s C) ;
|}.

Next Obligation.
Proof.
  exists.
  all: unfold Reflexive, Symmetric, Transitive.
  - intros.
    reflexivity.
  - intros.
    symmetry.
    auto.
  - intros ? ? ? p q.
    rewrite p, q.
    reflexivity.
Qed.

Next Obligation.
Proof.
  rewrite map_id, compose_id_left, compose_id_right.
  reflexivity.
Qed.

Next Obligation.
Proof.
  rewrite <- map_composes.
  rewrite compose_assoc.
  rewrite <- H0.
  rewrite <- compose_assoc.
  rewrite H.
  rewrite compose_assoc.
  reflexivity.
Qed.

Next Obligation.
Proof.
  rewrite H, H0.
  reflexivity.
Qed.
