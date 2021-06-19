Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Category.Prod.
Require Import Blech.Groupoid.
Require Import Blech.Groupoid.Core.
Require Import Blech.Functor.

Import BishopNotations.
Import CategoryNotations.

Open Scope category_scope.
Open Scope bishop_scope.

Class Bicategory := {
  Obj: Type ;
  Mor: Obj → Obj → Category ;

  id A: Mor A A ;
  compose {A B C}: Functor (Prod (Mor B C) (Mor A B)) (Mor A C) ;

  compose_id_left [A B] (F: Mor A B): Core _ (compose (id _, F)) F ;
  compose_id_right [A B] (F: Mor A B): Core _ (compose (F, id _)) F ;

  compose_assoc [A B C D] (f: Mor C D) (g: Mor B C) (h: Mor A B):
    Core _ (compose (f, compose (g, h))) (compose (compose (f, g), h)) ;
}.

Coercion Obj: Bicategory >-> Sortclass.
Coercion Mor: Bicategory >-> Funclass.
