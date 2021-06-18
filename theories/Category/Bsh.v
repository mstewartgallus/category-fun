Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Some.
Require Import Blech.Functor.
Require Blech.Reflect.

Import CategoryNotations.
Import BishopNotations.
Import SomeNotations.

Open Scope category_scope.
Open Scope bishop_scope.


Obligation Tactic := Reflect.category_simpl.


Definition bishop_mor [A B:Bishop] (op: A → B) := ∀ x y, x == y → op x == op y.
Existing Class bishop_mor.

#[local]
#[program]
Definition Bishop_Mor (A B: Bishop) := { op: A → B | bishop_mor op }.

Module Export BshNotations.
  #[local]
   Definition proj1_Bishop_Mor [A B]: Bishop_Mor A B → A → B := @proj1_sig _ _.
  #[local]
   Definition proj2_Bishop_Mor [A B] (f:Bishop_Mor A B): bishop_mor (proj1_Bishop_Mor f) := proj2_sig f.

  Coercion proj1_Bishop_Mor: Bishop_Mor >-> Funclass.
  Coercion proj2_Bishop_Mor: Bishop_Mor >-> bishop_mor.
  Existing Instance proj2_Bishop_Mor.
End BshNotations.


#[program]
Definition Bsh: Category := {|
  Obj := Bishop ;
  Mor A B := Bishop_Mor A B  /~ {| equiv x y := ∀ t, (x:>) t == (y:>) t |} ;

  id _ x := x ;
  compose _ _ _ f g x := f (g  x) ;
|}.

Next Obligation.
Proof.
  exists.
  all: unfold Reflexive, Symmetric, Transitive.
  - intros.
    reflexivity.
  - intros.
    symmetry.
    auto.
  - intros ? ? ? p q t.
    rewrite (p t), (q t).
    reflexivity.
Qed.

Next Obligation.
Proof.
  intros ? ? ?.
  assumption.
Qed.

Next Obligation.
Proof.
  intros ? ? ?.
  apply (proj2_sig f).
  apply (proj2_sig g).
  assumption.
Qed.

Next Obligation.
Proof.
  rewrite (H _).
  apply (proj2_sig f').
  rewrite (H0 _).
  reflexivity.
Qed.

Add Parametric Morphism {A B} (f: Bsh A B) : (proj1_sig f)
    with signature equiv ==> equiv as fn_mor.
Proof.
  intros.
  destruct f.
  cbn.
  auto.
Qed.

Definition simple (t:Type): Bsh := t /~ {| equiv := eq |}.
