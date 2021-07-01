Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

Require Import Blech.Bishop.
Require Import Blech.Category.

Import CategoryNotations.
Import BishopNotations.

Open Scope morphism_scope.
Open Scope bishop_scope.


#[universes(cumulative)]
Inductive ast {K: Category}: K → K → Type :=
| ast_id A: ast A A
| ast_compose {A B C}: ast B C → ast A B → ast A C
| ast_var {A B}: K A B → ast A B
.

#[local]
Fixpoint denote [K: Category] [A B] (p: ast A B): K A B :=
  match p with
  | ast_id _ => id _
  | ast_compose f g => denote f ∘ denote g
  | ast_var f => f
  end.

#[program]
Definition Ast {K: Category} (A B: K) := ast A B /~ {| equiv x y := denote x == denote y |}.

Next Obligation.
Proof.
  exists.
  - intros ?.
    reflexivity.
  - intro.
    symmetry.
    assumption.
  - intros ? ? ? p q.
    rewrite p, q.
    reflexivity.
Qed.

#[universes(cumulative)]
 Inductive path {K: Category} (A: K): K → Type :=
| path_id: path A A
| path_compose {B C}: K B C → path A B → path A C
.

Arguments path_id {K A}.
Arguments path_compose {K A B C}.

#[local]
 Fixpoint pdenote {K: Category} [A B: K] (f: path A B): K A B :=
  match f with
  | path_id => id _
  | path_compose h t => h ∘ pdenote t
  end.

#[program]
 Definition Path {K: Category} (A B: K) := path A B /~ {| equiv x y := pdenote x == pdenote y |}.

Next Obligation.
Proof.
  exists.
  - intros ?.
    reflexivity.
  - intro.
    symmetry.
    assumption.
  - intros ? ? ? p q.
    rewrite p, q.
    reflexivity.
Qed.

#[local]
 Definition sing {K: Category} {A B: K} (x: K A B): Path A B := path_compose x path_id.

Section app.
  Context [K: Category] [A B: K] (y: path A B).

  #[local]
   Fixpoint app' [C] (x: path B C): path A C :=
    match x with
    | path_id => y
    | path_compose h t => path_compose h (app' t)
    end.
End app.

#[local]
 Lemma app_composes [K: Category] [A B C: K] (f: path A B) (g: path B C):
  pdenote g ∘ pdenote f == pdenote (app' f g).
Proof.
  induction g.
  - cbn.
    rewrite compose_id_left.
    reflexivity.
  - cbn.
    rewrite <- compose_assoc.
    rewrite <- IHg.
    reflexivity.
Qed.

#[local]
 Definition app {K: Category} {A B C: K} (x:Path B C) (y: Path A B): Path A C := app' y x.

#[local]
 Fixpoint flatten' [K: Category] [A B: K] (x: ast A B): path A B :=
  match x with
  | ast_id _ => path_id
  | ast_compose f g => app (flatten' f) (flatten' g)
  | ast_var f => sing f
  end.

#[local]
 Theorem flatten_correct [K: Category] [A B: K] (f: ast A B): denote f == pdenote (flatten' f).
Proof.
  induction f.
  - reflexivity.
  - cbn.
    unfold app.
    rewrite <- app_composes.
    rewrite IHf1, IHf2.
    reflexivity.
  - cbn.
    rewrite compose_id_right.
    reflexivity.
Qed.

#[local]
 Definition flatten {K: Category} {A B: K} (x: Ast A B): Path A B := flatten' x.

#[local]
 Theorem flatten_injective [K: Category] [A B: K] (x y: Ast A B):
  flatten x == flatten y → x == y.
Proof.
  cbn.
  repeat rewrite <- flatten_correct.
  intro.
  assumption.
Qed.

#[local]
Ltac2 rec reify (p: constr) :=
  lazy_match! p with
| (@id ?k ?a) => '(ast_id $a)
| (@compose ?k ?a ?b ?c ?f ?g) =>
  let nf := reify f in
  let ng := reify g in
  '(ast_compose $nf $ng)
| ?p => '(ast_var $p)
end.

Ltac2 category () :=
  lazy_match! goal with
| [ |- ?f == ?g ] =>
  let rf := reify f in
  let rg := reify g in
  change (denote $rf == denote $rg) ; apply (flatten_injective $rf $rg) ; cbn
end.

Ltac category := ltac2:(Control.enter category).
Ltac category_simpl :=
  Tactics.program_simpl; repeat (try split; try Reflect.category; reflexivity).
