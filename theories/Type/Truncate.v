Require Import Blech.Defaults.

Reserved Notation "| A |" (at level 40).

#[universes(cumulative)]
Variant truncate A: Prop :=
| truncate_intro (_: A): truncate A.

Arguments truncate_intro [A] _.

Module TruncateNotations.
  Add Printing Let truncate.

  Notation "| A |" := (truncate A): type_scope.
End TruncateNotations.
