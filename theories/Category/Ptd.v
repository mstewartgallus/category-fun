Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Category.Under.
Require Blech.Reflect.

Import CategoryNotations.
Import BishopNotations.
Import UnderNotations.

Open Scope category_scope.
Open Scope bishop_scope.


#[local]
Obligation Tactic := Reflect.category_simpl.


#[program]
Definition Ptd (C: Category): Category := {|
  Obj := ∀ pt, C\pt ;
  Mor A B := (∀ pt, (C\pt) (A pt) (B pt)) ;
  Mor_Setoid _ _ := {| equiv f g := ∀ x, f x == g x |} ;

  id A _ := id _ ;
  compose A B C f g t := f t ∘ g t ;
|}.

Next Obligation.
Proof.
  exists.
  all: unfold Reflexive, Symmetric, Transitive.
  - reflexivity.
  - symmetry.
    auto.
  - intros ? ? ? p q t.
    rewrite p, q.
    reflexivity.
Qed.

Next Obligation.
Proof.
  intros ? ? p ? ? q t.
  cbn in *.
  rewrite (p t), (q t).
  reflexivity.
Qed.
