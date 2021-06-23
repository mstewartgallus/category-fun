Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Proset.
Require Import Blech.Category.
Require Import Blech.Category.Over.
Require Import Blech.Category.Monic.
Require Import Blech.Type.Truncate.

Import CategoryNotations.
Import BishopNotations.
Import ProsetNotations.
Import TruncateNotations.
Import MonicNotations.
Import OverNotations.

(* The partially ordered set of subobjects *)
#[program]
Definition Sub (C: Category) c: Proset := {|
  T := C ₊ / c ;
  preorder A B := | A ~> B | ;
|}.

Next Obligation.
Proof.
  admit.
Admitted.
