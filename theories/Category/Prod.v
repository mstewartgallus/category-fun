Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Blech.Bishop.Prod.
Require Import Blech.Category.
Require Import Blech.Functor.
Require Blech.Reflect.

Import CategoryNotations.
Import BishopNotations.
Import Prod.ProdNotations.
Import FunctorNotations.

Open Scope category_scope.
Open Scope bishop_scope.

Close Scope nat.

Reserved Notation "A # B" (at level 80, right associativity).


#[local]
Obligation Tactic := Reflect.category_simpl.


#[program]
 Definition Prod (C D: Category): Category := {|
  Obj := C * D ;
  Mor A B := (fst A ~> fst B) * (snd A ~> snd B) ;

  id _ := (id _, id _) ;
  compose _ _ _ f g := (fst f ∘ fst g, snd f ∘ snd g) ;
|}.

Next Obligation.
Proof.
  intros ? ? p ? ? q.
  destruct p as [p p'], q as [q q'].
  cbn in *.
  rewrite p, p', q, q'.
  split.
  all: reflexivity.
Qed.

#[program]
Definition fanout [A B C] (F: Functor C A) (G: Functor C B): Functor C (Prod A B) := {|
  op x := (F x, G x) ;
  map _ _ x := (map F x, map G x) ;
|}.

Next Obligation.
Proof.
  split.
  all: apply map_composes.
Qed.

Next Obligation.
Proof.
  split.
  all: apply map_id.
Qed.

Next Obligation.
Proof.
  intros ? ? p.
  cbn.
  rewrite p.
  split.
  all: reflexivity.
Qed.

#[program]
Definition fst {A B}: Functor (Prod A B) A := {|
  op := fst ;
  map _ _ := Prod.fst ;
|}.

#[program]
 Definition snd {A B}: Functor (Prod A B) B := {|
  op := snd ;
  map _ _ := Prod.snd ;
|}.

Module Export ProdNotations.
  Infix "#" := fanout.
  Infix "*" := Prod : category_scope.
End ProdNotations.
