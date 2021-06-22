Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Proset.
Require Import Blech.Category.
Require Import Blech.Category.PreOrd.

Import ProsetNotations.
Import CategoryNotations.

Class Complete := {
  P: Proset ;

  (* FIXME make D opposite proset *)
  supremum {D: Proset} (d: D → P) `{Homomorphism _ _ d}: P ;
  infirmum {D: Proset} (d: D → P) `{Homomorphism _ _ d}: P ;
}.

Coercion P: Complete >-> Proset.
Existing Instance P.
