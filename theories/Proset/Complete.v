Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Proset.
Require Import Blech.Proset.Op.
Require Import Blech.Category.
Require Import Blech.Category.PreOrd.

Import ProsetNotations.
Import CategoryNotations.
Import OpNotations.

(* Print PreOrder. *)
Class Complete := {
  P: Proset ;

  sup {D}: PreOrd (D ᵒᵖ) P → P ;
  inf {D}: PreOrd (D ᵒᵖ) P → P ;
}.

Coercion P: Complete >-> Proset.
Existing Instance P.
