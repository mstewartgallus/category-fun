Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Monoid.

Require Psatz.

Import BishopNotations.
Import MonoidNotations.

Open Scope bishop_scope.
Open Scope monoid_scope.

(*
 Basically a mulitiset/free commutative monoid.

FIXME require Finite ?
 *)
#[local]
Definition eqv {S} (f g: option (S → nat)): Prop :=
  match (f, g) with
  | (Some f', Some g') => ∀ t, f' t = g' t
  | (None, None) => True
  | _ => False
  end.

#[local]
Definition sum {S} (f g: option (S → nat)): option (S → nat) :=
  match (f, g) with
  | (Some f', Some g') => Some (λ t, f' t + g' t)
  | (None, _) => g
  | (_, None) => f
  end.

#[program]
Definition Monomial (S: Bishop): Monoid := {|
  S := option (S → nat) /~ {| equiv := eqv |} ;

  unit := None ;
  app := sum ;
|}.

Next Obligation.
Proof.
  unfold eqv.
  exists.
  - intro x.
    destruct x.
    all: reflexivity.
  - intros x y ?.
    destruct x, y.
    all: try contradiction.
    2: apply I.
    symmetry.
    auto.
  - intros x y z p q.
    destruct x, y, z.
    all: try contradiction.
    2: apply I.
    intro t.
    rewrite (p t), (q t).
    reflexivity.
Qed.

Next Obligation.
Proof.
  unfold eqv.
  destruct f, g, h.
  all: cbn in *.
  all: Psatz.lia.
Qed.

Next Obligation.
Proof.
  destruct f.
  all: cbn in *.
  all: Psatz.lia.
Qed.


Next Obligation.
Proof.
  destruct f.
  all: cbn in *.
  all: Psatz.lia.
Qed.

Next Obligation.
Proof.
  intros x y p x' y' q.
  destruct x, y, x', y'.
  all: cbn in *.
  all: try contradiction.
  4: apply I.
  all: intro t.
  all: try rewrite (p t).
  all: try rewrite (q t).
  all: reflexivity.
Qed.
