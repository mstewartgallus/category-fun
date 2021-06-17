Require Import Blech.Defaults.


Reserved Notation "X & Y" (at level 80, right associativity).
Reserved Notation "'some' x .. y , P"
         (at level 200, x binder, y binder, right associativity,
          format "'[ ' '[ ' 'some'  x .. y ']' ,  '/' P ']'").
Reserved Notation "'Σ' x .. y , P"
         (at level 200, x binder, y binder, right associativity,
          format "'[ ' '[ ' 'Σ'  x .. y ']' ,  '/' P ']'").


#[universes(cumulative)]
Record someT [A] (P: A → Type) := some_intro { head: A ; tail: P head ; }.

Arguments some_intro [A P].
Arguments head [A P].
Arguments tail [A P].

Module Export SomeNotations.
  Notation "'some' x .. y , P" := (someT (λ x, .. (someT (λ y,  P)) .. )) : type_scope.
  Notation "'Σ' x .. y , P" := (someT (λ x, .. (someT (λ y,  P)) .. )) : type_scope.
  Infix "&" := some_intro.
End SomeNotations.
