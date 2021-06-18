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


Reserved Notation "'lub' A , P" (right associativity, at level 200).


#[universes(cumulative)]
Record bundle (C: Category) (t: C) := supremum { s: C ; π: C s t ; }.

Arguments s [C] [t] _.
Arguments π [C] [t] _.


Obligation Tactic := Reflect.category_simpl.

#[program]
Definition Over (C: Category) (t: C): Category := {|
  Obj := bundle C t ;
  Mor A B := {f: s A ~> s B | π B ∘ f == π A } /~ {| equiv f g := (f :>) == (g :>) |} ;

  id A := id (s A) ;
  compose A B C := @compose _ (s A) (s B) (s C) ;
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
  rewrite compose_assoc.
  rewrite H0, H.
  reflexivity.
Qed.

Next Obligation.
Proof.
  rewrite H, H0.
  reflexivity.
Qed.

Module OverNotations.
  Notation "'lub' A , P" := {| s := A ; π := P |}.
  Infix "/" := Over : category_scope.
  Coercion s: bundle >-> Obj.
End OverNotations.
