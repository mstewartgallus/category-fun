Require Import Blech.Defaults.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Category.Bsh.
Require Import Blech.Category.Op.
Require Import Blech.Category.Funct.

Import OpNotations.

Definition PSh (C: Category): Category := Funct (C ᵒᵖ) Bsh.
