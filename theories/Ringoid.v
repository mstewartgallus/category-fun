Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Bishop.Prod.
Require Import Blech.Functor.
Require Import Blech.Category.
Require Import Blech.Category.Funct.
Require Import Blech.Groupoid.
Require Import Blech.Category.Op.
Import GroupoidNotations.

Import BishopNotations.
Import CategoryNotations.
Import OpNotations.
Import ProdNotations.
Import FunctorNotations.

Open Scope category_scope.
Open Scope bishop_scope.

#[local]
Obligation Tactic := Reflect.category_simpl.

Reserved Notation "∅".
Reserved Notation "X ⊕ Y" (at level 30, right associativity).
Reserved Notation "X †" (at level 1).

#[universes(cumulative)]
Class Category := {
  C: Category.Category ;

  (* Enriched over a group structure *)
  zero {A B}: C A B ;
  plus {A B}: C A B → C A B → C A B ;
  neg {A B}: C A B → C A B ;

  compose_zero_left {X Y Z} (y: C X Y): @zero Y Z ∘ y == zero ;
  compose_zero_right {X Y Z} (x: C Y Z): x ∘ @zero X Y == zero ;

  neg_compose {X Y Z} (x: C Y Z) (y: C X Y):
  neg (x ∘ y) == neg x ∘ neg y ;
  neg_zero {A B} : neg (@zero A B) == zero ;
  plus_neg_right {A B} (x: C A B): plus x (neg x) == zero ;
  plus_zero_right {A B} (x: C A B): plus x zero == x ;
  plus_zero_left {A B} (x: C A B): plus zero x == x ;

  plus_compat {A B}: Proper (equiv ==> equiv ==> equiv) (@plus A B) ;
  neg_compat {A B}: Proper (equiv ==> equiv) (@neg A B) ;

  (* FIXME add laws such as commutativity *)
}.

Existing Instance C.
Coercion C: Category >-> Category.Category.

Existing Instance plus_compat.
Existing Instance neg_compat.

Module Import RingoidNotations.
  Notation "∅" := zero.
  Notation "x ⊕ y" := (plus x y).
  Notation "- x" := (neg x).
End RingoidNotations.

(* Doesn't seem quite right maybe I need an Ab enriched dagger category?

   Should also almost be a ringoid.
 *)
#[program]
Definition Complex (C: Category): Category.Category := {|
  Obj := C ;
  Mor A B := (C A B) * (C A B) ;

  id _ := (id _, ∅) ;
  compose X Y Z '(a, b) '(c, d) :=
    ((a ∘ c) ⊕ (- (b ∘ d)),
     (a ∘ d) ⊕ (b ∘ c)) ;
|}.

Next Obligation.
Proof.
  admit.
Admitted.

Next Obligation.
Proof.
  split.
  - rewrite compose_id_left.
    rewrite neg_compose.
    rewrite neg_zero.
    rewrite compose_zero_left.
    rewrite plus_zero_right.
    reflexivity.
  - rewrite compose_zero_left.
    rewrite plus_zero_right.
    rewrite compose_id_left.
    reflexivity.
Qed.

Next Obligation.
Proof.
  split.
  - rewrite compose_id_right.
    rewrite compose_zero_right.
    rewrite neg_zero.
    rewrite plus_zero_right.
    reflexivity.
  - rewrite compose_zero_right.
    rewrite compose_id_right.
    rewrite plus_zero_left.
    reflexivity.
Qed.

Next Obligation.
Proof.
  admit.
Admitted.

Definition neg' {C: Category} {A B: C} (f: (Complex C) A B) :=
  let '(a, b) := f in
  (- a, - b).

Definition j {C: Category} (A: C): (Complex C) A A := (∅, id _).

(* I think an appropriate generalization should probably obey j ∘ (j †) == -id *)
Definition j_squared {C: Category} (A: C): j A ∘ j A == neg' (@id (Complex C) A).
Proof.
  cbn.
  split.
  - rewrite compose_zero_left.
    rewrite plus_zero_left.
    rewrite compose_id_right.
    reflexivity.
  - rewrite neg_zero.
    rewrite compose_zero_left.
    rewrite compose_zero_right.
    rewrite plus_zero_left.
    reflexivity.
Qed.
