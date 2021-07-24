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
Inductive free {O} (S: O → O → Type): O → O → Type :=
| η {A B} (_: S A B): free S A B
| id A: free S A A
| compose {A B C} (f: free S B C) (g: free S A B): free S A C.

Arguments η {O S A B}.
Arguments id {O S}.
Arguments compose {O S A B C}.

Inductive equiv {O: Type} {S: O → O → Type} `{∀ A B, Setoid (S A B)} : forall {A B: O}, relation (free S A B) :=
| reflexive {A B}: reflexive _ (@equiv O S _ A B)
| symmetric {A B}: symmetric _ (@equiv O S _ A B)
| transitive {A B}: transitive _ (@equiv O S _ A B)

| η_compat {A B}: Proper (SetoidClass.equiv ==> @equiv O S _ A B) η

| compose_assoc {A B C D} (f: free S C D) (g: free S B C) (h: free S A B):
    equiv (compose f (compose g h)) (compose (compose f g) h)

| compose_id_left {A B} (f: free S A B): equiv (compose (id _) f) f
| compose_id_right {A B} (f: free S A B): equiv (compose f (id _)) f

| compose_compat {A B C}: Proper (@equiv O S _ B C ==> @equiv O S _ A B ==> @equiv O S _ A C) compose
.
Existing Instance η_compat.
Existing Instance compose_compat.

#[global]
#[program]
Instance free_Setoid O (S: O → O → Type) `(forall A B, Setoid (S A B)) A B: Setoid (@free O S A B) := {
  equiv := equiv ;
}.
Next Obligation.
Proof.
  exists.
  - apply reflexive.
  - apply symmetric.
  - apply transitive.
Qed.

Definition Free {O} (S: O → O → Type) `{∀ A B, Setoid (S A B)}: Category := {|
  Obj := O ;
  Mor A B := free S A B ;

  Mor_Setoid := free_Setoid O S _ ;

  Category.id := id ;
  Category.compose := @compose _ _ ;

  Category.compose_assoc := @compose_assoc _ _ _ ;
  Category.compose_id_left := @compose_id_left _ _ _ ;
  Category.compose_id_right := @compose_id_right _ _ _ ;
  Category.compose_compat := @compose_compat _ _ _ ;
|}.

Fixpoint ε {C: Category} {A B} (f: Free C A B): C A B :=
  match f with
  | η x => x
  | id _ => Category.id _
  | compose x y => ε x ∘ ε y
  end.
