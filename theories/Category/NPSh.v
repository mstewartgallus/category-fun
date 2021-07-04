Require Import Blech.Defaults.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Category.Funct.
Require Import Blech.Category.Bsh.
Require Import Blech.Category.Prod.
Require Import Blech.Category.Op.
Require Import Blech.Groupoid.
Require Import Blech.Groupoid.Fin.

Import ProdNotations.
Import OpNotations.

(* Cylindrical ? *)
Definition NPSh (C: Category) (M N: nat): Category :=
  Funct
    (Funct (Fin M) (C ᵒᵖ) * Funct (Fin N) C)
    Bsh.
