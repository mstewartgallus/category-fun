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

#[local]
Obligation Tactic := Reflect.category_simpl.

#[universes(cumulative)]
Record twisted (K: Category) := tw { s: K ; t: K ; π: s ~> t ; }.

Arguments tw [K s t].
Arguments s [K].
Arguments t [K].
Arguments π [K].

#[universes(cumulative)]
Record Tw_Mor [K] (A B: twisted K) := tw_Mor {
  s_Mor: s A ~> s B ;
  t_Mor: t B ~> t A ;
  π_Mor: π A == t_Mor ∘ π B ∘ s_Mor ;
}.

Arguments tw_Mor [K A B].
Arguments s_Mor [K A B].
Arguments t_Mor [K A B].
Arguments π_Mor [K A B].

#[program]
Definition Tw (K: Category): Category := {|
  Obj := twisted K ;
  Mor A B := Tw_Mor A B ;
  Mor_Setoid _ _ := {| equiv f g := (t_Mor f == t_Mor g) ∧ (s_Mor f == s_Mor g) |} ;

  id _ := tw_Mor (id _) (id _) _ ;
  compose _ _ _ f g := {| t_Mor := t_Mor g ∘ t_Mor f ;
                          s_Mor := s_Mor f ∘ s_Mor g |} ;
|}.

Next Obligation.
Proof.
  exists.
  all:unfold Reflexive, Symmetric, Transitive; cbn.
  - split.
    all:reflexivity.
  - intros ? ? p.
    destruct p as [p q].
    rewrite p, q.
    split.
    all: reflexivity.
  - intros ? ? ? p q.
    destruct p as [p p'], q as [q q'].
    split.
    1: rewrite p, q.
    2: rewrite p', q'.
    all: reflexivity.
Qed.

Next Obligation.
Proof.
  admit.
Admitted.

Next Obligation.
Proof.
  intros ? ? p ? ? q.
  cbn.
  destruct p as [p p'], q as [q q'].
  rewrite p, p', q, q'.
  split.
  all:reflexivity.
Qed.
