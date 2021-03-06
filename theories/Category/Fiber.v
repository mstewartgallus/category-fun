Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Type.Some.
Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Functor.
Require Import Blech.Category.Bsh.
Require Import Blech.Category.Op.
Require Import Blech.Bishop.Trv.
Require Blech.Reflect.

Import CategoryNotations.
Import BishopNotations.
Import FunctorNotations.
Import SomeNotations.
Import OpNotations.

Open Scope category_scope.
Open Scope bishop_scope.

(*
Do a Grothendieck thing.

Functor A B → PFunctor (B ᵒᵖ) Cat
*)
#[local]
Obligation Tactic := Reflect.category_simpl.

#[universes(cumulative)]
Record fiber [E B: Category] (P: Functor E B) (c: B) :=
  sup {
      tag: E ;
      field: P tag ~> c ;
    }.

Arguments sup [E B P c].
Arguments tag [E B P c].
Arguments field [E B P c].

(* FIXME make a pseudofunctor

  Only equivalent if a fibration or something iirc.
 *)
#[program]
Definition Fiber [E B: Category] (P: Functor E B) (c: B): Category := {|
  Obj := fiber P c ;
  Mor '(sup e1 f1) '(sup e2 f2) := { u: e1 ~> e2 | f2 ∘ map P u == f1 } ;
  Mor_Setoid _ _ := {| equiv x y := proj1_sig x == proj1_sig y |} ;

  id _ := exist _ (id _) _ ;
  compose _ _ _ f g := proj1_sig f ∘ g ;
|}.

Next Obligation.
Proof.
  exists.
  - intros ?.
    reflexivity.
  - intros ? ? ?.
    symmetry.
    assumption.
  - intros ? ? ? p q.
    rewrite p, q.
    reflexivity.
Qed.

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
  rewrite <- H.
  rewrite H0.
  reflexivity.
Qed.

Next Obligation.
Proof.
  intros ? ? p ? ? q.
  cbn in *.
  rewrite p, q.
  reflexivity.
Qed.
