Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Functor.
Require Import Blech.Category.
Require Import Blech.Category.Funct.
Require Import Blech.Category.Prod.
Require Import Blech.Category.Op.

Import BishopNotations.
Import CategoryNotations.
Import OpNotations.
Import FunctorNotations.

Open Scope category_scope.
Open Scope bishop_scope.

#[local]
Obligation Tactic := Reflect.category_simpl.

Reserved Notation "⊤".
Reserved Notation "X × Y" (at level 50, left associativity).

Reserved Notation "∅".

Reserved Notation "[ X , Y ]".

#[universes(cumulative)]
Class Closed := {
  C: Category ;

  pt: C ;
  prod: Functor (C * C) C ;

  mt: C ;
  sum: Functor (C * C) C ;

  (* FIXME add curry/laws *)
  exp: Functor (C ᵒᵖ * C) C ;
}.

Existing Instance C.
Coercion C: Closed >-> Category.

Notation "⊤" := pt.
Notation "A × B" := (prod (A, B)).

Notation "∅" := mt.
Notation "A + B" := (sum (A, B)).
Notation "[ A , B ]" := (exp (A, B)).

(* FIXME laws *)
Reserved Notation "◇".
Reserved Notation "□".

Class Comonad (C: Closed) := {
  W: Functor C C ;
  dup {A}: W A ~> W (W A) ;
  ext {A}: W A ~> A ;
}.

Existing Instance W.
Coercion W: Comonad >-> Functor.

Class Monad (C: Closed) := {
  M: Functor C C ;
  join {A}: M (M A) ~> M A ;
  pure {A}: A ~> M A ;
}.
Existing Instance M.
Coercion M: Monad >-> Functor.


(* FIXME possibly indexed monads/comonads would work better ? *)

Class Var (C: Closed) := {
  necessarily: Comonad C ;
  possibly: Monad C ;

  (* necessitation rule *)
  thunk {A}: ⊤ ~> A → ⊤ ~> necessarily A ;
}.

Arguments necessarily {C}.
Arguments possibly {C}.

(* Like universal *)
Notation "□" := necessarily.
(* Like existential *)
Notation "◇" := possibly.

Reserved Notation "!".

Class Cylinder := {
  H: Closed;
  (* FIXME require finite ? *)
  α: Type;

  var: α → Var H ;

  nec_comm {X Y A}: □ (var X) (□ (var Y) A) ~> □ (var Y) (□ (var X) A) ;
  pos_comm {X Y A}: ◇ (var X) (◇ (var Y) A) ~> ◇ (var Y) (◇ (var X) A) ;
  (* FIXME laws *)
}.

Existing Instance H.
Coercion H: Cylinder >-> Closed.
Coercion var: α >-> Var.

Notation "!" := var.

Section open.
  Context `{C: Cylinder}.

  Context {x y z w: α}.

  Definition foo: ⊤ ~> □ x (◇ x ⊤) := thunk pure.
End open.
