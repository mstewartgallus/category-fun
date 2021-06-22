Require Import Blech.Defaults.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Category.Funct.
Require Import Blech.Category.Bsh.

Definition CoPSh (C: Category): Category := Funct C Bsh.
