Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Proset.

Import ProsetNotations.

Class Heyting := {
  P: Proset ;

  top: P ;
  bot: P ;

  meet: P → P → P ;
  join: P → P → P ;
  impl: P → P → P ;

  (* FIXME laws *)
}.

Coercion P: Heyting >-> Proset.
Existing Instance P.

Module HeytingNotations.
  Notation "⊤" := top.
  Notation "⊥" := bot.
  Infix "∧" := meet.
  Infix "∨" := join.
  Infix "→" := impl.
End HeytingNotations.
