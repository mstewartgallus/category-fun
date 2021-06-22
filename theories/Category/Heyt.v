Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Proset.
Require Import Blech.Proset.Heyting.
Require Import Blech.Category.
Require Blech.Reflect.

Import BishopNotations.
Import CategoryNotations.
Import ProsetNotations.
Import HeytingNotations.

Open Scope category_scope.
Open Scope bishop_scope.


#[local]
Obligation Tactic := Reflect.category_simpl.

Class Homomorphism [C D: Heyting] (F: C → D)  := {
  map_top: F ⊤ == ⊤ ;
  map_bot: F ⊥ == ⊥ ;
  map_meet p q: F (p ∧ q) == (F p ∧ F q) ;
  map_join p q: F (p ∨ q) == (F p ∨ F q) ;
  map_impl p q: F (impl p q) == impl (F p) (F q) ;
  map_compat: Proper (preorder ==> preorder) F ;
}.

Existing Instance map_compat.

Instance Homomorphism_Proper [C D: Heyting] (F: C → D) `(@Homomorphism C D F):  Proper (equiv ==> equiv) F.
Proof.
  intros ? ? p.
  destruct p as [p q].
  split.
  - rewrite p.
    reflexivity.
  - rewrite q.
    reflexivity.
Qed.

#[program]
Definition Heyt: Category := {|
  Obj := Heyting ;
  Mor A B := { f: A → B | Homomorphism f } /~ {| equiv f g := ∀ x, f x == g x |} ;

  id _ x := x ;
  compose _ _ _ f g x := f (g  x) ;
|}.

Next Obligation.
Proof.
  exists.
  all: admit.
Admitted.

Next Obligation.
Proof.
  exists.
  all: try reflexivity.
  intros ? ? p.
  assumption.
Qed.

Next Obligation.
Proof.
  exists.
  - repeat rewrite map_top.
    reflexivity.
  - repeat rewrite map_bot.
    reflexivity.
  - intros p q.
    repeat rewrite map_meet.
    reflexivity.
  - intros p q.
    repeat rewrite map_join.
    reflexivity.
  - intros p q.
    repeat rewrite map_impl.
    reflexivity.
  - intros x y p.
    rewrite p.
    reflexivity.
Qed.

Next Obligation.
Proof.
  intros f g p f' g' q t.
  cbn.
  destruct f, f', g, g'.
  cbn in *.
  split.
  - destruct (q t) as [q0 q1].
    rewrite q0.
    destruct (p (x2 t)) as [p0 p1].
    rewrite p0.
    reflexivity.
  - destruct (q t) as [q0 q1].
    rewrite q1.
    destruct (p (x0 t)) as [p0 p1].
    rewrite p1.
    reflexivity.
Qed.
