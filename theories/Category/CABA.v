Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Proset.
Require Import Blech.Proset.Complete.
Require Import Blech.Proset.Op.
Require Import Blech.Category.
Require Import Blech.Category.PreOrd.
Require Blech.Reflect.

Import BishopNotations.
Import CategoryNotations.
Import ProsetNotations.
Import OpNotations.

Open Scope category_scope.
Open Scope bishop_scope.


#[local]
Obligation Tactic := Reflect.category_simpl.

Class Continuous [C D: Complete] (F: PreOrd C D) := {
  map_sup [E: Proset] (p: PreOrd (E ᵒᵖ) C):
    proj1_sig F (sup p) == sup (F ∘ p) ;
  map_inf [E: Proset] (p: PreOrd (E ᵒᵖ) C):
    proj1_sig F (inf p) == inf (F ∘ p) ;
}.

(* Not really CABA but a constructive variation.
   supposedly CABA^op ~ Set
 *)
#[program]
Definition CABA: Category := {|
  Obj := Complete ;
  Mor A B := { F: PreOrd A B | Continuous F } /~ {| equiv f g := ∀ x, f x == g x |} ;

  id _ := exist _ (id _) _ ;
  compose _ _ _ f g := exist _ (proj1_sig f ∘ proj1_sig g) _ ;
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
  admit.
Admitted.

Next Obligation.
Proof.
  admit.
Admitted.
