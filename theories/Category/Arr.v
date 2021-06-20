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

#[local]
Obligation Tactic := Reflect.category_simpl.

#[universes(cumulative)]
Record arrow (K: Category) := arr { s: K ; t: K ; π: s ~> t ; }.

Arguments arr [K s t].
Arguments s [K].
Arguments t [K].
Arguments π [K].

#[universes(cumulative)]
Record Arr_Mor [K] (A B: arrow K) := arr_Mor {
  s_Mor: s A ~> s B ;
  t_Mor: t A ~> t B ;
  π_Mor: t_Mor ∘ π A == π B ∘ s_Mor ;
}.

Arguments arr_Mor [K A B].
Arguments s_Mor [K A B].
Arguments t_Mor [K A B].
Arguments π_Mor [K A B].

#[program]
Definition Arr (K: Category): Category := {|
  Obj := arrow K ;
  Mor A B := Arr_Mor A B /~ {| equiv f g := (t_Mor f == t_Mor g) ∧ (s_Mor f == s_Mor g) |} ;

  id _ := arr_Mor (id _) (id _) _ ;
  compose _ _ _ f g := {| t_Mor := t_Mor f ∘ t_Mor g ;
                          s_Mor := s_Mor f ∘ s_Mor g |} ;
|}.

Next Obligation.
Proof.
  exists.
  all:unfold Reflexive, Symmetric, Transitive; cbn.
  - split.
    all:reflexivity.
  - split.
    all: destruct H.
    all: symmetry.
    all: assumption.
  - intros ? ? ? p q.
    destruct p as [p p'], q as [q q'].
    split.
    1: rewrite p, q.
    2: rewrite p', q'.
    all: reflexivity.
Qed.

Next Obligation.
Proof.
  rewrite <- compose_assoc.
  rewrite (π_Mor g).
  rewrite compose_assoc.
  rewrite compose_assoc.
  rewrite (π_Mor f).
  reflexivity.
Qed.

Next Obligation.
Proof.
  intros ? ? p ? ? q.
  cbn.
  destruct p as [p p'], q as [q q'].
  rewrite p, p', q, q'.
  split.
  all:reflexivity.
Qed.
