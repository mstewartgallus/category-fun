Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Lists.List.

From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

Require Import Blech.Bishop.
Require Import Blech.Monoid.
Require Import Blech.Monoid.List.

Import ListNotations.
Import MonoidNotations.
Import BishopNotations.

Open Scope bishop_scope.

(* Loosely based around the cpdt reflection chapter
 http://adam.chlipala.net/cpdt/html/Reflection.html, FIXME give more
 proper credit *)

#[universes(cumulative)]
Inductive ast (M: Monoid) :=
| ast_e
| ast_app (x y: ast M)
| ast_var (m: M)
.

Arguments ast_e {M}.
Arguments ast_app {M}.
Arguments ast_var {M}.

#[local]
Fixpoint denote {M: Monoid} (m: ast M): M :=
  match m with
  | ast_e => e
  | ast_app x y => denote x · denote y
  | ast_var x => x
  end.

#[local]
Fixpoint tolist {M: Monoid} (m: ast M): List M :=
  match m with
  | ast_e => nil
  | ast_app x y => tolist x ++ tolist y
  | ast_var x => cons x nil
  end.

#[local]
Definition flatten {M: Monoid} (m: ast M): M := ε (tolist m).

#[local]
Theorem denote_correct {M: Monoid} (x: ast M): denote x == ε (tolist x).
Proof.
  induction x.
  - reflexivity.
  - cbn.
    unfold app.
    rewrite counit_app.
    rewrite IHx1, IHx2.
    reflexivity.
  - cbn.
    rewrite app_e_right.
    reflexivity.
Qed.

#[local]
 Theorem flatten_injective {M: Monoid} (x y: ast M): flatten x == flatten y → denote x == denote y.
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
| (@e ?m) => '(@ast_e $m)
| (@app ?m ?x ?y) =>
  let rx := reify x in
  let ry := reify y in
  '(@ast_app $m $rx $ry)
| ?p => '(ast_var $p)
end.

Ltac2 monoid () :=
  lazy_match! goal with
| [ |- ?x == ?y ] =>
  let rx := reify x in
  let ry := reify y in
  change (denote $rx == denote $ry) ; apply (flatten_injective $rx $ry); cbn
end.

Ltac monoid := ltac2:(Control.enter monoid).

Ltac monoid_simpl :=
  Tactics.program_simpl; repeat (try split; try monoid; reflexivity).
