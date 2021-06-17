Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Functor.
Require Blech.Bishops.
Require Blech.Reflect.

Import CategoryNotations.
Import BishopNotations.
Import Bishops.BishopsNotations.
Import FunctorNotations.

Open Scope category_scope.
Open Scope bishop_scope.

Close Scope nat.

Reserved Notation "A # B" (at level 80, right associativity).


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
  split.
  - rewrite H0, H.
    reflexivity.
  - rewrite H1, H2.
    reflexivity.
Qed.

#[program]
Definition fanout [A B C] (F: Funct C A) (G: Funct C B): Funct C (Prod A B) := {|
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
  split.
  all: rewrite H.
  all: reflexivity.
Qed.

#[program]
Definition fst {A B}: Funct (Prod A B) A := {|
  op := fst ;
  map _ _ := Bishops.fst ;
|}.

#[program]
 Definition snd {A B}: Funct (Prod A B) B := {|
  op := snd ;
  map _ _ := Bishops.snd ;
|}.

Module Export ProductNotations.
  Infix "#" := fanout.
  Infix "*" := Prod : category_scope.
End ProductNotations.
