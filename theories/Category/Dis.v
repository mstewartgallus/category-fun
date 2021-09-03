Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Category.Prod.
Require Import Blech.Category.Typ.
Require Import Blech.Category.Bsh.
Require Import Blech.Category.Funct.
Require Import Blech.Groupoid.
Require Import Blech.Groupoid.Core.
Require Import Blech.Groupoid.Free.
Require Import Blech.Functor.
Require Import Blech.Category.Comma.
Require Blech.Functor.Compose.
Require Blech.Functor.Id.
Require Import Blech.Functor.Curry.
Require Import Blech.Type.Truncate.
Require Blech.Reflect.

Import CategoryNotations.
Import GroupoidNotations.
Import FunctorNotations.
Import ProdNotations.
Import BishopNotations.
Import TruncateNotations.

Open Scope category_scope.
Open Scope bishop_scope.

#[local]
Obligation Tactic := Reflect.category_simpl.

#[universes(cumulative)]
Record dis (C: Category) := {
  pos: Bsh ;
  dir: Functor (Free pos) C ;
}.

Arguments pos {C}.
Arguments dir {C}.

#[universes(cumulative)]
Record Mor {C} (p q: dis C) := {
  Mor_pos: pos p ~> pos q ;
  Mor_dir: Funct _ _ (Compose.compose (dir q) (Free_map Mor_pos)) (dir p) ;
}.

Arguments Mor_pos {C p q}.
Arguments Mor_dir {C p q}.

#[local]
#[program]
Definition mor_equiv {C} {A B: dis C} (x y: Mor A B) :=
  ∃ (F:Mor_pos x == Mor_pos y),
    (Mor_dir x == (Mor_dir y ∘ _)).

Next Obligation.
Proof.
  eexists.
  Unshelve.
  2: {
    intros i.
    apply (map (dir B)).
    cbn in *.
    apply (F i).
  }
  intros ? ? p.
  cbn in *.
  repeat rewrite map_composes.
  apply map_compat.
  cbn.
  apply I.
Defined.

#[program]
Definition Dis C: Category := {|
  Obj := dis C ;
  Category.Mor := Mor ;
  Mor_Setoid A B :=
    {| equiv := mor_equiv |} ;

  id A :=
    {|
      Mor_pos := id _ ;
      Mor_dir i := id _ ;
    |} ;
  compose A B C f g :=
    {|
      Mor_pos := Mor_pos f ∘ Mor_pos g ;
      Mor_dir := Mor_dir g ∘ _ ;
    |} ;
|}.

Next Obligation.
Proof.
Admitted.

Next Obligation.
Proof.
  cbn in *.
  intros ? ? p.
  cbn in *.
  repeat rewrite compose_id_left.
  repeat rewrite compose_id_right.
  apply map_compat.
  cbn.
  apply I.
Defined.

Next Obligation.
Proof.
  exists (λ i, proj1_sig (Mor_dir f) _).
  intros ? ? p.
  cbn in *.
  destruct f as [[? ?] [? ?]], g as [[? ?] [? ?]].
  cbn in *.
  unfold Natural in *.
  cbn in *.
  rewrite (n _ _).
  apply compose_compat.
  1: reflexivity.
  apply map_compat.
  cbn.
  apply I.
Defined.

Next Obligation.
Proof.
  eexists.
  Unshelve.
  2: {
    intro.
    reflexivity.
  }
  intros ?.
  cbn.
  destruct f as [[? ?] [? ?]], g as [[? ?] [? ?]], h as [[? ?] [? ?]].
  cbn in *.
  unfold Natural in *.
  cbn in *.
  repeat rewrite <- compose_assoc.
  apply compose_compat.
  1: reflexivity.
  apply compose_compat.
  1: reflexivity.
  transitivity (x1 (x2 (x4 x)) ∘ id _).
  1: {
    rewrite compose_id_right.
    reflexivity.
  }
  apply compose_compat.
  1: reflexivity.
  rewrite <- map_id.
  apply map_compat.
  cbn.
  apply I.
Defined.

Next Obligation.
Proof.
  eexists.
  Unshelve.
  2: {
    cbn.
    intro.
    reflexivity.
  }
  cbn.
  intro.
  apply compose_compat.
  1: reflexivity.
  rewrite <- map_id.
  apply map_compat.
  cbn.
  apply I.
Defined.

Next Obligation.
Proof.
  eexists.
  Unshelve.
  2: {
    cbn.
    intro.
    reflexivity.
  }
  cbn.
  intro.
  rewrite compose_id_left.
  transitivity (proj1_sig (Mor_dir f) x ∘ id _).
  1: {
    rewrite compose_id_right.
    reflexivity.
  }
  apply compose_compat.
  1: reflexivity.
  rewrite <- map_id.
  cbn.
  apply map_compat.
  cbn.
  apply I.
Defined.

Next Obligation.
Proof.
  eexists.
  Unshelve.
  2: {
    cbn.
    intro.
    destruct H, H0.
    cbn in *.
    rewrite (x2 _).
    rewrite (x3 _).
    reflexivity.
  }
  cbn.
  intros.
  destruct H, H0.
  cbn in *.
  rewrite (e _).
  rewrite (e0 _).
  repeat rewrite <- compose_assoc.
  apply compose_compat.
  1: reflexivity.
  destruct x as [[? ?] [? ?]], y as [[? ?] [? ?]].
  cbn in *.
  unfold Natural in *.
  cbn in *.
  rewrite <- e.
  rewrite n.
  rewrite e.
  cbn.
  repeat rewrite <- compose_assoc.
  apply compose_compat.
  1: reflexivity.
  rewrite map_composes.
  apply map_compat.
  cbn.
  apply I.
Defined.

Definition Σ {C D} (F: Functor C D) (P: Dis C): Dis D :=
  {|
    pos := pos P ;
    dir := Compose.compose F (dir P) ;
  |}.


#[program]
Definition Basechange {C D} (F: Functor D C) (P: Dis C): Dis D :=
  {|
    pos := Pullback (dir P) F /~ {| equiv x y := | Core (Comma (dir P) F) x y | |} ;
    dir :=
      {|
        op x := t x ;
        map _ _ f := _ ;
      |} ;
  |}.

Next Obligation.
Proof.
Admitted.

Next Obligation.
Proof.
Admitted.

Next Obligation.
Proof.
Admitted.

Next Obligation.
Proof.
Admitted.

Next Obligation.
Proof.
Admitted.


(* Probably very wrong *)
#[program]
Definition Π {C D} (F: Functor D C) (P: Dis C): Dis D :=
  {|
    pos := Pullback F (Id.id _) /~ {| equiv x y := | Core (Comma F _) x y | |} ;
    dir :=
      {|
        op x := s x ;
        map _ _ f := _ ;
      |} ;
  |}.

Next Obligation.
Proof.
Admitted.

Next Obligation.
Proof.
Admitted.

Next Obligation.
Proof.
Admitted.

Next Obligation.
Proof.
Admitted.

Next Obligation.
Proof.
Admitted.
