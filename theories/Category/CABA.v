Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Proset.
Require Import Blech.Proset.Complete.
Require Import Blech.Category.
Require Import Blech.Category.PreOrd.
Require Blech.Reflect.

Import BishopNotations.
Import CategoryNotations.
Import ProsetNotations.

Open Scope category_scope.
Open Scope bishop_scope.


#[local]
Obligation Tactic := Reflect.category_simpl.

#[local]
Instance id_Homomorphism [A: Proset]: Homomorphism (λ x: A, x).
Proof.
  intros ? ? p.
  assumption.
Qed.

#[local]
Instance compose_Homomorphism [A B C: Proset]
         (f: B → C) (g: A → B)
         `(Homomorphism _ _ f) `(Homomorphism _ _ g)
  : Homomorphism (λ x, f (g x)).
Proof.
  intros ? ? p.
  apply H.
  apply H0.
  assumption.
Qed.

Class Continuous [C D: Complete] (F: C → D) := {
  map: Homomorphism F ;
  map_supremum [E: Proset] (p: E → C) `{Homomorphism _ _ p}:
    F (supremum p) == supremum (λ x, F (p x)) ;
  map_infirmum [E: Proset] (p: E → C) `{Homomorphism _ _ p}:
    F (infirmum p) == infirmum (λ x, F (p x)) ;
}.

(* Not really CABA but a constructive variation.
   supposedly CABA^op ~ Set
 *)
#[program]
Definition CABA: Category := {|
  Obj := Complete ;
  Mor A B := { F: A → B | Continuous F } /~ {| equiv f g := ∀ x, f x == g x |} ;

  id _ x := x ;
  compose _ _ _ f g x := f (g x) ;
|}.

Next Obligation.
Proof.
  exists.
  all: admit.
Admitted.

Next Obligation.
Proof.
  admit.
Admitted.

Next Obligation.
Proof.
  eexists.
  Unshelve.
  3: {
    intros ? ? p.
    apply map.
    apply map.
    assumption.
  }
  - admit.
  - admit.
Admitted.

Next Obligation.
Proof.
  intros ? ? p ? ? q ?.
  cbn in *.
  admit.
Admitted.
