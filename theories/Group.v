Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Groupoid.
Require Import Blech.Monoid.

Require Blech.Reflect.

Import CategoryNotations.
Import GroupoidNotations.
Import BishopNotations.
Import MonoidNotations.

Open Scope category_scope.
Open Scope monoid_scope.
Open Scope bishop_scope.

Class Group := {
  M: Monoid ;
  invert: M → M  where "f ⁻¹" := (invert f) ;

  app_invert_left (f: M): f ⁻¹ · f == ∅ ;
  app_invert_right (f: M): f · f ⁻¹ == ∅;

  invert_compat (f f': M): f == f' → f ⁻¹ == f' ⁻¹ ;
}.

Add Parametric Morphism [G: Group] : (@invert G)
    with signature equiv ==> equiv as group_mor.
Proof.
  intros ? ? p.
  apply invert_compat.
  apply p.
Qed.

Module Import GroupNotations.
  Declare Scope group_scope.
  Delimit Scope group_scope with group.

  Bind Scope group_scope with Group.
  Bind Scope group_scope with M.

  Coercion M: Group >-> Monoid.
  Existing Instance M.

  Notation "f ⁻¹" := (invert f) : monoid_scope.
End GroupNotations.
