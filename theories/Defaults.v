#[global]
Set Primitive Projections.
#[global]
Unset Printing Primitive Projection Parameters.

#[global]
Set Universe Polymorphism.

#[global]
Set Default Goal Selector "!".

Require Export Coq.Unicode.Utf8.

(* The builtin product type has bad behavior with respect to heavily
depending programming *)
Record prod A B := pair { fst: A ; snd: B }.
Arguments pair {A B}.
Arguments fst {A B}.
Arguments snd {A B}.

Infix "*" := prod : type_scope.

Add Printing Let prod.

Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.
#[global]
Hint Resolve pair inl inr: core.
