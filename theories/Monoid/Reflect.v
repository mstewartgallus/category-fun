Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Lists.List.

From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

Require Import Blech.Bishop.
Require Import Blech.Monoid.
Require Import Blech.Monoid.List.
Require Blech.Monoid.Free.

Import ListNotations.
Import MonoidNotations.
Import BishopNotations.

Open Scope bishop_scope.

(* Loosely based around the cpdt reflection chapter
 http://adam.chlipala.net/cpdt/html/Reflection.html, FIXME give more
 proper credit *)

#[local]
Definition flatten {M: Monoid} (m: Free.Free M): M := ε (from_free m).

#[local]
Theorem denote_correct {M: Monoid} (x: Free.Free M): Free.ε x == ε (from_free x).
Proof.
  induction x.
  - cbn.
    rewrite app_e_right.
    reflexivity.
  - cbn.
    reflexivity.
  - cbn.
    rewrite counit_app.
    rewrite IHx1, IHx2.
    reflexivity.
Qed.

#[local]
 Theorem flatten_injective {M: Monoid} (x y: Free.Free M): flatten x == flatten y → Free.ε x == Free.ε y.
Proof.
  unfold flatten.
  cbn.
  repeat rewrite <- denote_correct.
  intro.
  assumption.
Qed.

#[local]
Ltac2 rec reify (p: constr) :=
  lazy_match! p with
| (@e ?m) => '(Free.e)
| (@app ?m ?x ?y) =>
  let rx := reify x in
  let ry := reify y in
  '(Free.app $rx $ry)
| ?p => '(Free.η $p)
end.

Ltac2 monoid () :=
  lazy_match! goal with
| [ |- ?x == ?y ] =>
  let rx := reify x in
  let ry := reify y in
  change (Free.ε $rx == Free.ε $ry) ; apply (flatten_injective $rx $ry); cbn
end.

Ltac monoid := ltac2:(Control.enter monoid).

Ltac monoid_simpl :=
  Tactics.program_simpl; repeat (try split; try monoid; reflexivity).
