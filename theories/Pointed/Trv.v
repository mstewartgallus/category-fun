Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Bishop.Trv.
Require Import Blech.Bishop.Exp.
Import ExpNotations.
Require Import Blech.Pointed.
Require Import Blech.Pointed.Exp.
Import ExpNotations.

Import BishopNotations.
Import PointedNotations.

#[program]
Definition trv: Pointed := point trv I.

Module TrvNotations.
  Notation "·" := trv : pointed_scope.
End TrvNotations.
