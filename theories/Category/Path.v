Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.

Import BishopNotations.
Import CategoryNotations.

Open Scope bishop_scope.
Open Scope morphism_scope.

#[universes(cumulative)]
 Inductive path {O} (K: O → O → Bishop) (A: O): O → Type :=
| id: path K A A
| compose {B C}: K B C → path K A B → path K A C
.

Arguments id {O K}.
Arguments compose {O K A B C}.

Definition η {O} {K:O → O → Bishop} {A B: O} (x: K A B): path K A B := compose x (id _).

Section app.
  Context {O: Type} {K: O → O → Bishop} [A B: O] (y: path K A B).

  #[local]
   Fixpoint app {C} (x: path K B C): path K A C :=
    match x with
    | id _ => y
    | compose h t => compose h (app t)
    end.
End app.

#[program]
Definition Path {O} (S: O → O → Bishop): Category := {|
  Obj := O ;
  (* FIXME , give a proper equality definition *)
  Mor A B := path S A B /~ {| equiv := eq |} ;

  Category.id := id ;
  Category.compose _ _ _ f g := app g f ;
|}.

Next Obligation.
Proof.
  induction f.
  - cbn.
    reflexivity.
  - cbn in *.
    rewrite IHf.
    reflexivity.
Qed.

Next Obligation.
Proof.
  induction f.
  - cbn.
    reflexivity.
  - cbn in *.
    rewrite IHf.
    reflexivity.
Qed.

Fixpoint ε {C: Category} {A B} (f: Path C A B): C A B :=
  match f with
  | id _ => Category.id _
  | compose x y => x ∘ ε y
  end.
