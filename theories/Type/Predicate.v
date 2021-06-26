Require Import Blech.Defaults.

Definition Predicate A := A → Prop.

Definition subsetof {A} (P: Predicate A) := { x | P x }.

Coercion subsetof: Predicate >-> Sortclass.
