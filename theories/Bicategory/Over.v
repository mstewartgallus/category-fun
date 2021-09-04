Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Category.Prod.
Require Import Blech.Category.Funct.
Require Import Blech.Groupoid.
Require Import Blech.Groupoid.Core.
Require Import Blech.Groupoid.Free.
Require Import Blech.Functor.
Require Import Blech.Functor.Curry.
Require Import Blech.Category.Comma.
Require Blech.Functor.Compose.
Require Blech.Functor.Id.
Require Import Blech.Type.Truncate.
Require Import Blech.Bicategory.

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
Record bundle (C: Bicategory) (c: C) := {
  pos: C ;
  dir: Mor pos c ;
}.

Arguments pos {C c}.
Arguments dir {C c}.

#[universes(cumulative)]
Record slice {C: Bicategory} {c} (p q: bundle C c) := {
  Mor_pos: Mor (pos p) (pos q) ;
  Mor_dir: C (pos p) c (compose (dir q, Mor_pos)) (dir p) ;
}.

Arguments Mor_pos {C c p q}.
Arguments Mor_dir {C c p q}.

#[program]
Definition Mor2 {C c} {A B: bundle C c} (x y: slice A B) := {
  f: C (pos A) (pos B) (Mor_pos x) (Mor_pos y) |
  Mor_dir y ∘ map (@compose C (pos A) (pos B) c) (Category.id (dir B), f) == Mor_dir x
}.

#[program]
Definition Mor2_Setoid {C c} {A B: bundle C c} (x y: slice A B): Setoid (Mor2 x y) := {|
  equiv x y := proj1_sig x == proj1_sig y ;
|}.
Next Obligation.
Proof.
  exists.
  - intros ?.
    reflexivity.
  - intros ? ? p.
    symmetry.
    apply p.
  - intros ? ? ? p q.
    rewrite p, q.
    reflexivity.
Qed.

#[program]
Definition Fiber {C c} (A B: bundle C c): Category := {|
  Category.Obj := slice A B ;
  Category.Mor := Mor2 ;
  Mor_Setoid := Mor2_Setoid ;

  Category.id A := Category.id (Mor_pos A) ;
  Category.compose A B C f g := proj1_sig f ∘ proj1_sig g ;
|}.


Next Obligation.
Proof.
  rewrite map_id.
  rewrite Category.compose_id_right.
  reflexivity.
Qed.

Next Obligation.
Proof.
  rewrite <- (proj2_sig g).
  cbn.
  rewrite <- (proj2_sig f).
  cbn.
  repeat rewrite <- Category.compose_assoc.
  apply compose_compat.
  1: reflexivity.
  rewrite map_composes.
  cbn.
  apply map_compat.
  cbn.
  split.
  2: reflexivity.
  rewrite Category.compose_id_right.
  reflexivity.
Qed.

Next Obligation.
Proof.
  intros ? ? p ? ? q.
  cbn in *.
  rewrite p, q.
  reflexivity.
Qed.

#[local]
Definition id {C c} (A: bundle C c): Fiber A A :=
 {|
     Mor_pos := id (pos A) ;
     Mor_dir := map To (compose_id_right (dir A)) ;
  |}.

#[local]
#[program]
Definition lift {C D} (F: Functor C D): Functor (Core C) (Core D) :=
  {|
  op := F ;
  map _ _ x := {| to := map F (map To x) ; from := map F (map From x)  |} ;
  |}.

Next Obligation.
Proof.
  rewrite map_composes.
  rewrite to_from.
  rewrite map_id.
  reflexivity.
Qed.

Next Obligation.
Proof.
  rewrite map_composes.
  rewrite from_to.
  rewrite map_id.
  reflexivity.
Qed.

Next Obligation.
Proof.
  repeat rewrite map_composes.
  split.
  all: reflexivity.
Qed.

Next Obligation.
Proof.
  repeat rewrite map_id.
  split.
  all: reflexivity.
Qed.

Next Obligation.
Proof.
  intros ? ? [p q].
  cbn.
  split.
  - rewrite p.
    reflexivity.
  - rewrite q.
    reflexivity.
Qed.

#[local]
#[program]
Definition mon {C D}: Functor (Core C * Core D) (Core (C * D)) :=
  {|
  op x := x ;
  map '(X, Y) '(Z, W) '(f, g) :=
    {| to := (map To f, map To g) ;
       from := (map From f, map From g) ;
    |}
  |}.

Next Obligation.
Proof.
  repeat rewrite to_from.
  split.
  all: reflexivity.
Qed.

Next Obligation.
Proof.
  repeat rewrite from_to.
  split.
  all: reflexivity.
Qed.

Next Obligation.
Proof.
  all: repeat split.
  all: reflexivity.
Qed.
Next Obligation.
Proof.
  all: repeat split.
  all: reflexivity.
Qed.
Next Obligation.
Proof.
  intros ? ? [[p q] [r s]].
  cbn in *.
  rewrite p, q, r, s.
  all: repeat split.
  all: reflexivity.
Qed.

#[local]
#[program]
Definition compose {K k} {A B C: bundle K k} (f: Fiber B C) (g: Fiber A B): Fiber A C :=
{|
  Mor_pos := compose (Mor_pos f, Mor_pos g) ;
  Mor_dir :=
    Mor_dir g
    ∘ map (@compose K (pos A) (pos B) k) (Mor_dir f, Category.id (Mor_pos g))
    ∘ map To (compose_assoc _ _ _) ;
|}.

#[program]
Definition compose' {K k} {A B C: bundle K k}: Functor (Fiber B C * Fiber A B) (Fiber A C) :=
  {|
  op '(f, g) := compose f g ;
  map '(X, Y) '(Z, W) '(f, g) :=
    map (@Bicategory.compose K (pos A) (pos B) (pos C)) (proj1_sig f, proj1_sig g) ;
  |}.

Next Obligation.
Proof.
  rewrite <- (proj2_sig g).
  cbn.
  repeat rewrite <- Category.compose_assoc.
  apply compose_compat.
  1: reflexivity.
  repeat rewrite Category.compose_assoc.
  repeat rewrite map_composes.
  cbn.
  repeat rewrite <- Category.compose_assoc.
Admitted.

Next Obligation.
Proof.
  rewrite map_composes.
  cbn.
  reflexivity.
Qed.

Next Obligation.
Proof.
  rewrite map_id.
  reflexivity.
Qed.

Next Obligation.
Proof.
  intros [? ?] [? ?] [p q].
  cbn in *.
  apply map_compat.
  cbn in *.
  split.
  all: auto.
Qed.

#[program]
Definition Over C c: Bicategory := {|
  Obj := bundle C c ;
  Mor := Fiber ;

  Bicategory.id := id ;
  Bicategory.compose := @compose' C c ;
  compose_id_left _ _ f := {|
                      to := to (compose_id_left (Mor_pos f)) ;
                      from := from (compose_id_left (Mor_pos f)) ;
                      |} ;
  compose_id_right _ _ f := {|
                      to := to (compose_id_right (Mor_pos f)) ;
                      from := from (compose_id_right (Mor_pos f)) ;
                      |} ;
  compose_assoc _ _ _ _ f g h := {|
                      to := to (compose_assoc (Mor_pos f) (Mor_pos g) (Mor_pos h)) ;
                      from := from (compose_assoc (Mor_pos f) (Mor_pos g) (Mor_pos h)) ;
                      |} ;
|}.

Next Obligation.
Proof.
  rewrite <- Category.compose_assoc.
  apply compose_compat.
  1: reflexivity.
Admitted.

Next Obligation.
Proof.
  repeat rewrite <- Category.compose_assoc.
Admitted.

Next Obligation.
Proof.
  rewrite to_from.
  reflexivity.
Qed.

Next Obligation.
Proof.
  rewrite from_to.
  reflexivity.
Qed.

Next Obligation.
Proof.
  repeat rewrite <- Category.compose_assoc.
  
Admitted.

Next Obligation.
Proof.
Admitted.

Next Obligation.
Proof.
  rewrite to_from.
  reflexivity.
Qed.

Next Obligation.
Proof.
  rewrite from_to.
  reflexivity.
Qed.

Next Obligation.
Proof.
Admitted.

Next Obligation.
Proof.
  repeat rewrite <- Category.compose_assoc.
  apply compose_compat.
  1: reflexivity.
Admitted.

Next Obligation.
Proof.
  rewrite to_from.
  reflexivity.
Qed.

Next Obligation.
Proof.
  rewrite from_to.
  reflexivity.
Qed.
