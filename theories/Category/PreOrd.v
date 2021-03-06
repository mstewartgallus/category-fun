Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.Bsh.
Require Import Blech.Category.
Require Import Blech.Proset.
Require Blech.Reflect.

Import CategoryNotations.
Import ProsetNotations.
Import BishopNotations.

Open Scope category_scope.
Open Scope bishop_scope.
Open Scope proset_scope.

#[local]
Obligation Tactic := Reflect.category_simpl.

Definition Homomorphism [A B: Proset] (f : A → B) := Proper (preorder ==> preorder) f.
Existing Class Homomorphism.

Definition hom (A B: Proset) := { f: A → B | Homomorphism f }.

Definition proj1_hom [A B]: hom A B → A → B := @proj1_sig _ _.
Definition proj2_hom [A B]: ∀ (f: hom A B), Proper (preorder ==> preorder) (proj1_hom f) := @proj2_sig _ _.

Coercion proj1_hom: hom >-> Funclass.
Existing Instance proj2_hom.

#[program]
Definition PreOrd: Category := {|
  Obj := Proset ;
  Mor A B := hom A B ;
  Mor_Setoid _ _ := {| equiv x y := ∀ t, proj1_hom x t == proj1_hom y t |} ;

  id _ x := x ;
  compose _ _ _ f g x := f (g x) ;
|}.

Next Obligation.
Proof.
  exists.
  - intros ? ?.
    split.
    all: reflexivity.
  - intros ? ? p t.
    destruct (p t).
    split.
    all: auto.
  - intros ? ? ? p q t.
    destruct (p t) as [p0 p1].
    destruct (q t) as [q0 q1].
    split.
    + rewrite p0, q0.
      reflexivity.
    + rewrite q1, p1.
      reflexivity.
Qed.

Next Obligation.
Proof.
  intros ? ? ?.
  assumption.
Qed.

Next Obligation.
Proof.
  intros ? ? q.
  apply proj2_hom.
  apply proj2_hom.
  assumption.
Qed.

Next Obligation.
Proof.
  intros f g p f' g' q t.
  cbn in *.
  destruct f, g, f', g'.
  cbn in *.
  admit.
Admitted.
