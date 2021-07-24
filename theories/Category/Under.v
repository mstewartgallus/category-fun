Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Blech.Reflect.

Import CategoryNotations.
Import BishopNotations.

Open Scope morphism_scope.
Open Scope bishop_scope.

Reserved Notation "A \ B" (right associativity, at level 30).
Reserved Notation "'gub' A , P" (right associativity, at level 200).

#[local]
Obligation Tactic := Reflect.category_simpl.

#[universes(cumulative)]
Record bundle (C: Category) (s: C) := infima { t: C ; i: C s t ; }.

Arguments t [C] [s] _.
Arguments i [C] [s] _.


#[program]
Definition Under (C: Category) (s: C): Category := {|
  Obj := bundle C s ;
  Mor A B := {f: t A ~> t B | i B == f ∘ i A } ;
  Mor_Setoid _ _ := {| equiv f g := proj1_sig f == (g :>) |} ;

  id A := id (t A) ;
  compose A B C := @compose _ (t A) (t B) (t C) ;
|}.

Next Obligation.
Proof.
  exists.
  all: unfold Reflexive, Symmetric, Transitive.
  - reflexivity.
  - symmetry.
    assumption.
  - intros ? ? ? p q.
    rewrite p, q.
    reflexivity.
Qed.

Next Obligation.
Proof.
  rewrite <- compose_assoc.
  rewrite H0, H.
  reflexivity.
Qed.

Next Obligation.
Proof.
  intros ? ? p ? ? q.
  cbn.
  rewrite p, q.
  reflexivity.
Qed.

Coercion t: bundle >-> Obj.

Module UnderNotations.
  Notation "'gub' A , P" := {| t := A ; i := P |}.
  Infix "\" := Under : category_scope.
End UnderNotations.
