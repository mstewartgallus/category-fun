Require Import Blech.Defaults.

Reserved Notation "| A |" (at level 40).

(* FIXME get propositional truncation from elsewhere *)
#[universes(cumulative)]
Variant truncate A: Prop :=
| truncate_intro (_: A): truncate A.

Arguments truncate_intro [A] _.

Module TruncateNotations.
  Notation "| A |" := (truncate A): type_scope.
End TruncateNotations.
