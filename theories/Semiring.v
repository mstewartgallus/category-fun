Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.

Import BishopNotations.

Open Scope bishop_scope.

Reserved Notation "X ⊕ Y" (at level 50, left associativity).
Reserved Notation "X ⊗ Y" (at level 40, left associativity).

#[universes(cumulative)]
Class Semiring := {
  S: Bishop ;

  I: S ;
  add: S → S → S where "A ⊕ B" := (add A B) ;

  O: S ;
  mul: S → S → S where "A ⊗ B" := (mul A B) ;

  add_O_l x: O ⊕ x == x ;
  add_comm x y: x ⊕ y == y ⊕ x ;

  mul_I_l x: I ⊗ x == x ;
  mul_I_r x: x ⊗ I == x ;

  mul_O_l x: O ⊗ x == O ;

  add_compat: Proper (equiv ==> equiv ==> equiv) add ;
  mul_compat: Proper (equiv ==> equiv ==> equiv) mul ;
}.

Existing Instance S.
Coercion S: Semiring >-> Bishop.

Existing Instance add_compat.
Existing Instance mul_compat.

Module Import SemiringNotations.
  Notation "0" := O.
  Notation "1" := I.
  Infix "⊕" := add.
  Infix "⊗" := mul.
End SemiringNotations.
