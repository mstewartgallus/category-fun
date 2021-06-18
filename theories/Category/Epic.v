Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Blech.Reflect.

Import CategoryNotations.
Import BishopNotations.

Open Scope category_scope.
Open Scope bishop_scope.

#[local]
Obligation Tactic := Reflect.category_simpl.

#[program]
Definition Epic (C: Category): Category := {|
  Obj := C ;
  Mor A B := {f: C A B | ∀ (Z:C) (x y: C B Z), (x ∘ f == y ∘ f) → x == y} /~ {| equiv x y := (x :>) == (y :>) |} ;

  id := @id _ ;
  compose := @compose _ ;
|}.

Next Obligation.
Proof.
  exists.
  - intro.
    reflexivity.
  - intros ? ? ?.
    symmetry.
    auto.
  - intros ? ? ? p q.
    rewrite p, q.
    reflexivity.
Qed.

Next Obligation.
Proof.
  repeat rewrite compose_id_right in H.
  assumption.
Qed.

Next Obligation.
Proof.
  repeat rewrite compose_assoc in H.
  apply (H1 _ _ _ (H0 _ _ _ H)).
Qed.

Next Obligation.
Proof.
  rewrite H, H0.
  reflexivity.
Qed.
