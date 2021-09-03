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

Definition over {C:Category} (A: dis C): Over Cat C :=
  {|
  Over.pos := (@Groupoid.C (Free (pos A))): Cat ;
  Over.dir := dir A ;
  |}.

#[program]
Instance Dis (C: Category): Category := {
  Category.Obj := dis C ;
  Category.Mor A B := Over Cat C (over A) (over B) /~ {| equiv x y := | Core (Over Cat C _ _) x y | |} ;

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
  apply (@compose_assoc (Over Cat C)).
Qed.

Next Obligation.
Proof.
  exists.
  apply (@compose_id_left (Over Cat C)).
Qed.

Next Obligation.
Proof.
  exists.
  apply (@compose_id_right (Over Cat C)).
Qed.

Next Obligation.
Proof.
  intros ? ? p ? ? q.
  destruct p, q.
  exists.
Admitted.

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
