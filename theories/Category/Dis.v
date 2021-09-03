Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Category.Prod.
Require Import Blech.Category.Typ.
Require Import Blech.Category.Bsh.
Require Import Blech.Category.Funct.
Require Import Blech.Category.PSh.
Require Import Blech.Category.Op.
Require Import Blech.Groupoid.
Require Import Blech.Groupoid.Core.
Require Import Blech.Groupoid.Free.
Require Import Blech.Functor.
Require Import Blech.Category.Comma.
Require Blech.Functor.Compose.
Require Blech.Functor.Id.
Require Import Blech.Functor.Curry.
Require Import Blech.Type.Truncate.
Require Import Blech.Bicategory.
Require Import Blech.Bicategory.Cat.
Require Import Blech.Bicategory.Over.
Require Blech.Reflect.

Import CategoryNotations.
Import GroupoidNotations.
Import FunctorNotations.
Import ProdNotations.
Import BishopNotations.
Import TruncateNotations.
Import OpNotations.

Open Scope category_scope.
Open Scope bishop_scope.

#[local]
Obligation Tactic := Reflect.category_simpl.

#[program]
Definition Objects (C: Category) := Category.Obj C /~ {| equiv x y := | Core C x y | |}.

Next Obligation.
Proof.
  exists.
  - intros ?.
    exists.
    apply (Category.id _: Core C x x).
  - intros ? ? [p].
    exists.
    apply (invert (p: Core C _ _)).
  - intros ? ? ? [p] [q].
    exists.
    apply ((q: Core C _ _) ∘ p).
Qed.

#[universes(cumulative)]
Record dis (C: Category) := {
  pos: Bsh ;
  dir: Bsh pos (Objects C) ;
}.

Arguments pos {C}.
Arguments dir {C}.

Definition Tr C := Free (Objects C).
Definition over {C:Category} (A: dis C): Over Cat (Tr C) :=
  {|
  Over.pos := (@Groupoid.C (Free (pos A))): Cat ;
  Over.dir := Free_map (dir A) ;
|}.

#[program]
Instance Dis (C: Category): Category := {
  Category.Obj := dis C ;
  Category.Mor A B := Over Cat (Tr C) (over A) (over B) /~ {| equiv x y := | Core (Over Cat (Tr C) _ _) x y | |} ;

  Category.id _ := Bicategory.id _ ;
  Category.compose _ _ _ f g := Bicategory.compose (f, g) ;
}.

Next Obligation.
Proof.
  exists.
  - intros ?.
    exists.
    apply (Category.id _: Core _ _ _).
  - intros ? ? [p].
    exists.
    apply (invert (p: Core _ _ _)).
  - intros ? ? ? [p] [q].
    exists.
    apply ((q: Core _ _ _) ∘ p).
Qed.

Next Obligation.
Proof.
  exists.
  apply (@compose_assoc (Over Cat (Tr C))).
Qed.

Next Obligation.
Proof.
  exists.
  apply (@compose_id_left (Over Cat (Tr C))).
Qed.

Next Obligation.
Proof.
  exists.
  apply (@compose_id_right (Over Cat (Tr C))).
Qed.

Next Obligation.
Proof.
  intros ? ? [p] ? ? [q].
  exists.
Admitted.

Definition Σ {C D} (F: Bsh (Objects C) (Objects D)) (P: Dis C): Dis D :=
  {|
    pos := pos P ;
    dir := F ∘ dir P ;
  |}.


#[program]
Definition Basechange {C D} (F: Bsh (Objects D) (Objects C)) (P: Dis C): Dis D :=
  {|
    pos := Pullback (Free_map (dir P)) (Free_map F) /~ {| equiv x y := | Core (Comma _ _) x y | |} ;
    dir x := t x ;
  |}.

Next Obligation.
Proof.
Admitted.

Next Obligation.
Proof.
  intros ? ? [[? [? [p]]]].
  exists.
  cbn in *.
  apply p.
Qed.

(* Probably very wrong *)
#[program]
Definition Π {C D} (F: Bsh (Objects D) (Objects C)) (P: Dis C): Dis D :=
  {|
    pos := Pullback (Free_map F) (Id.id _) /~ {| equiv x y := | Core (Comma (Free_map F) _) x y | |} ;
    dir x := s x ;
  |}.

Next Obligation.
Proof.
Admitted.

Next Obligation.
Proof.
Admitted.

