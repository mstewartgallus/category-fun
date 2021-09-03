Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Functor.
Require Import Blech.Category.Bsh.

Require Blech.Reflect.

Import CategoryNotations.
Import FunctorNotations.
Import BishopNotations.


Open Scope category_scope.
Open Scope bishop_scope.

#[local]
Obligation Tactic := Reflect.category_simpl.

Record fiber {C D} (F: Functor C D) (d: D) := sup {
  tag: C ;
  field: F tag ~> d ;
}.
Arguments sup {C D F d}.
Arguments tag {C D F d}.
Arguments field {C D F d}.

#[local]
Definition Mor {C D} {F: Functor C D} {d: D} (x y: fiber F d) :=
 {f: C (tag y) (tag x) | field x ∘ map F f == field y }.

(* In general fiber is a category *)
#[program]
Definition Fiber {C D} (F: Functor C D) (d: D): Category := {|
  Obj := fiber F d ;
  Category.Mor := Mor ;
  Mor_Setoid _ _ := {| equiv x y := proj1_sig x == proj1_sig y |} ;

  id _ := id _ ;
  compose _ _ _ f g := g ∘ f ;
|}.

Next Obligation.
Proof.
Admitted.

Next Obligation.
Proof.
  rewrite map_id.
  rewrite compose_id_right.
  reflexivity.
Qed.

Next Obligation.
Proof.
  rewrite <- map_composes.
  rewrite compose_assoc.
  rewrite (proj2_sig g).
  rewrite (proj2_sig f).
  reflexivity.
Qed.

(* FIXME write out the truncation for discrete fibrations.
Maybe use an explicit truncation to set ?
 *)

Next Obligation.
Proof.
  intros ? ? p ? ? q.
  cbn in *.
  rewrite p, q.
  reflexivity.
Qed.
