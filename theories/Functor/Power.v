Require Import Blech.Defaults.

Require Import Coq.Program.Tactics.

Record prod S := prod_intro {
  prod_s: Type ;
  prod_π: prod_s → S ;
}.

Arguments prod_intro {S prod_s}.
Arguments prod_s {S}.
Arguments prod_π {S}.

Record sum S := sum_intro {
  sum_s: Type ;
  sum_π: sum_s → S ;
}.

Arguments sum_intro {S sum_s}.
Arguments sum_s {S}.
Arguments sum_π {S}.

Coercion sum_s: sum >-> Sortclass.
Coercion sum_π: sum >-> Funclass.

Coercion prod_s: prod >-> Sortclass.
Coercion prod_π: prod >-> Funclass.

Module Import PowerNotations.
  Notation "'Π' x , P" := (prod_intro (λ x, P)) (at level 200, x ident).
  Notation "'Π' x : A , P" := (prod_intro (λ x: A, P)) (at level 200, x ident).
  Notation "'Π' ( x : A ) , P" := (prod_intro (λ x: A, P)) (at level 200, x ident).

  Notation "'Σ' x , P" := (sum_intro (λ x, P)) (at level 200, x ident).
  Notation "'Σ' x : A , P" := (sum_intro (λ x: A, P)) (at level 200, x ident).
  Notation "'Σ' ( x : A ) , P" := (sum_intro (λ (x: A), P)) (at level 200, x ident).
End PowerNotations.

(* I think ? *)
#[program]
Definition sum_map {A B} (f: B → A) (p: sum A): sum B :=
  Σ (x: {y: B | ∃ x, f y = p x }), x.

#[program]
Definition prod_map {A B} (f: B → A) (p: prod A): prod B :=
  Π (x: {y: B | ∃ x, f y = p x }), x.

Definition poly S := sum (prod S).

(* Vaguely makes sense I think ? *)
Definition pure {A} (x: A): poly A := Σ (i: {y: prod A | y = Π (j: {y| y = x}), proj1_sig j}), proj1_sig i.

Definition map {A B} (f: A → B): poly A → poly B := sum_map (prod_map f).

(* Not at all sure here *)
Definition counit {A} (x: A): prod (sum A) :=
Π (i: {y: sum A | y = Σ (j: {y| y = x}), proj1_sig j}), proj1_sig i.

(* Probably wrong *)
Definition join {A} (p: poly (poly A)): poly A := sum_map counit p.
