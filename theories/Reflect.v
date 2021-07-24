Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Blech.Category.Free.
Require Blech.Category.Path.

Import CategoryNotations.
Import BishopNotations.

Open Scope morphism_scope.
Open Scope bishop_scope.

#[local]
 Lemma counit_compose {K: Category} {A B C: K} (f: Path.Path K _ B C) (g: Path.Path K _ A B):
  Path.ε (f ∘ g) == Path.ε f ∘ Path.ε g.
Proof.
  induction f.
  - cbn.
    rewrite compose_id_left.
    reflexivity.
  - cbn.
    rewrite <- compose_assoc.
    rewrite <- IHf.
    reflexivity.
Qed.

#[local]
 Fixpoint to_path {K: Category} {A B: K} (x: Free.Free K A B): Path.Path K _ A B :=
  match x with
  | Free.id _ => id _
  | Free.compose f g => to_path f ∘ to_path g
  | Free.η f => Path.η f
  end.

#[local]
Theorem flatten_correct [K: Category] [A B: K] (f: Free.Free K A B): Free.ε f == Path.ε (to_path f).
Proof.
  induction f.
  - cbn.
    rewrite compose_id_right.
    reflexivity.
  - cbn.
    reflexivity.
  - cbn.
    rewrite (counit_compose (to_path f1) (to_path f2)).
    rewrite IHf1, IHf2.
    reflexivity.
Qed.

#[local]
 Theorem flatten_injective [K: Category] [A B: K] (x y: Free.Free K A B):
  Path.ε (to_path x) == Path.ε (to_path y) → Free.ε x == Free.ε y.
Proof.
  cbn.
  repeat rewrite <- flatten_correct.
  intro.
  assumption.
Qed.

#[local]
Ltac2 rec reify (p: constr) :=
  lazy_match! p with
| (@id ?k ?a) => '(Free.id $a)
| (@compose ?k ?a ?b ?c ?f ?g) =>
  let nf := reify f in
  let ng := reify g in
  '(Free.compose $nf $ng)
| ?p => '(Free.η $p)
end.

Ltac2 category () :=
  lazy_match! goal with
| [ |- ?f == ?g ] =>
  let rf := reify f in
  let rg := reify g in
  change (Free.ε $rf == Free.ε $rg) ; apply (flatten_injective $rf $rg) ; cbn
end.

Ltac category := ltac2:(Control.enter category).
Ltac category_simpl :=
  Tactics.program_simpl; repeat (try split; try Reflect.category; reflexivity).
