Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Groupoid.
Require Import Blech.Functor.
Require Import Blech.Category.Op.

Require Blech.Reflect.


Import CategoryNotations.
Import FunctorNotations.
Import BishopNotations.
Import GroupoidNotations.
Import OpNotations.

#[universes(cumulative)]
Record iso [K: Category] (A B: K) := {
  to: K A B ;
  from: K B A ;
  to_from: to ∘ from == id _ ;
  from_to: from ∘ to == id _ ;
}.

Arguments to [K A B] _.
Arguments from [K A B] _.
Arguments to_from [K A B] _.
Arguments from_to [K A B] _.

#[local]
Obligation Tactic := Reflect.category_simpl.

#[program]
Definition Core (K: Category): Groupoid := {|
  C := {|
        Obj := K ;
        Mor A B := iso A B ;
        Mor_Setoid _ _ := {| equiv f g := to f == to g ∧ from f == from g |} ;

        id A := {| to := id _ ; from := id _ |} ;
        compose A B C f g :=
          {|
            to := to f ∘ to g ;
            from := from g ∘ from f
          |} ;
      |} ;
  invert _ _ f := {|
                   to := from f ;
                   from := to f ;
                   to_from := from_to f ;
                   from_to := to_from f ;
                 |} ;
|}.

Next Obligation.
Proof.
  exists.
  - split.
    all: reflexivity.
  - intros ? ? p.
    destruct p.
    split.
    all: symmetry.
    all: auto.
  - intros ? ? ? p q.
    destruct p as [p1 p2].
    destruct q as [q1 q2].
    split.
    + rewrite p1, q1.
      reflexivity.
    + rewrite p2, q2.
      reflexivity.
Qed.

Next Obligation.
Proof.
  rewrite <- compose_assoc.
  rewrite -> (compose_assoc (to g)).
  rewrite to_from.
  rewrite compose_id_left.
  rewrite to_from.
  reflexivity.
Qed.

Next Obligation.
Proof.
  rewrite <- compose_assoc.
  rewrite -> (compose_assoc (from f)).
  rewrite from_to.
  rewrite compose_id_left.
  rewrite from_to.
  reflexivity.
Qed.

Next Obligation.
Proof.
  intros ? ? p ? ? q.
  destruct p, q.
  split.
  + apply compose_compat.
    all:assumption.
  + apply compose_compat.
    all:assumption.
Qed.

Next Obligation.
Proof.
  split.
  all: apply from_to.
Qed.

Next Obligation.
Proof.
  split.
  all: apply to_from.
Qed.

Next Obligation.
Proof.
  intros ? ? p.
  cbn.
  destruct p.
  split.
  all: assumption.
Qed.

Module CoreNotations.
  Notation "A <~> B" := (Core _ A B) : category_scope.
End CoreNotations.

Instance to_Functoral {C: Category}: Functoral (λ x: Core C, x: C) (@to C).
Proof.
  exists.
  all: cbn.
  all: intros.
  all: try reflexivity.
  intros ? ? [? ?].
  auto.
Qed.

Definition To {C}: Functor (Core C) C :=
{|
  map _ _ (f: Core C _ _) := to f ;
|}.

Instance from_Functoral {C: Category}: @Functoral (Core C) (C ᵒᵖ) (λ x, x) (@from C).
Proof.
  exists.
  all: cbn.
  all: intros.
  all: try reflexivity.
  intros ? ? [? ?].
  auto.
Qed.

Definition From {C}: Functor (Core C) (C ᵒᵖ) :=
{|
  map _ _ (f: Core C _ _) := from f: (C ᵒᵖ)%category _ _ ;
|}.
