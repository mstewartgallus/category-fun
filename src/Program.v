Global
Set Primitive Projections.
Global
Unset Printing Primitive Projection Parameters.

Global
Set Universe Polymorphism.

Global
Set Default Goal Selector "!".

From Ltac2 Require Import Ltac2.

Set Default Proof Mode "Classic".

Require Import Coq.Unicode.Utf8.
Require Import Coq.Lists.List.

Set Implicit Arguments.
Module Import Some.
  Record some [A] (P: A → Type) := {
    val: A ;
    pred: P val ;
  }.

  #[local]
   Definition curry [A B C] (f: ∀ x: A, B x → C) (xy: some B): C := f (val xy) (pred xy).
  #[local]
   Definition const [A] (x: A) (_: True): A := x.

  Module Export SomeNotations.
    Notation "'some' x .. y , P" := (some (fun x => .. (some (fun y => P)) ..))
                                      (at level 200, x binder, y binder, right associativity,
                                       format "'[ ' '[ ' 'some' x .. y ']' , '/' P ']'") : type_scope.
  End SomeNotations.
End Some.

Module Import Logic.
  Inductive prop C :=
  | just (_: C)
  | success
  | failure
  .

  Variant horn C := entails (_: prop C) (_: list (prop C)).
  Inductive formula C :=
  | const (_: horn C)
  | free [A] (_: A → formula C).
  Definition theory C := list (formula C).

  Module Export LogicNotations.
    Declare Scope logic_scope.
    Delimit Scope logic_scope with logic.

    Bind Scope logic_scope with prop.
    Bind Scope logic_scope with horn.
    Bind Scope logic_scope with formula.
    Bind Scope list_scope with theory.

    Notation "∀ x .. y , P" := (free (fun x => .. (free (fun y => const P)) ..))
                                 (at level 200, x binder, y binder, right associativity,
                                  format "'[ ' '[ ' '∀' x .. y ']' , '/' P ']'") : logic_scope.
    Infix "⊢" := entails (at level 90) : logic_scope .
  End LogicNotations.

  Fixpoint head [C] (F: formula C): Type :=
    match F with
    | const _ => True
    | free P => some x, head (P x)
    end.

  Fixpoint curry [C] (F: formula C): head F → horn C :=
    match F with
    | const H => λ _, H
    | free P => λ xy, curry (P (val xy)) (pred xy)
    end.

  Definition heads [C] : theory C → list Type := List.map (λ F, head F).

  Fixpoint anyof (l: list Type): Type :=
    match l with
    | nil => False
    | cons H T => H + anyof T
    end.

  Definition any_head [C] (th: theory C) := anyof (heads th).

  Fixpoint pick [C] (th: theory C): any_head th → horn C :=
    match th with
    | nil => λ x, match x with end
    | cons H T =>
      let H' := curry H in
      let T' := pick T in
      λ xy, match xy with
            | inl x => H' x
            | inr x => T' x
            end
    end.
End Logic.

Module Import Heyting.
  Class Heyting := {
    S: Type ;

    top: S ;
    bot: S ;

    meet: S → S → S ;
    join: S → S → S ;
    impl: S → S → S ;
                  }.

  Definition meet_all `{Heyting}: list S → S := List.fold_right meet top.
  Definition join_all `{Heyting}: list S → S := List.fold_right join bot.

  Module Export HeytingNotations.
    Declare Scope heyting_scope.
    Delimit Scope heyting_scope with heyting.
    Bind Scope heyting_scope with S.

    Notation "⊤" := top.
    Notation "⊥" := bot.

    Infix "∧" := meet : heyting.
    Infix "∨" := join : heyting.
    Infix "→" := impl : heyting.

    Notation "⋁" := join_all : heyting.
    Notation "⋀" := meet_all : heyting.

    Coercion S: Heyting >-> Sortclass.
  End HeytingNotations.
End Heyting.

Module Import Interpreter.
  Close Scope nat.

  Section interpreter.
    Context [C: Type].
    Context (cset: Heyting).
    Context (one: C → cset).

    Open Scope heyting.

    #[local]
     Definition chk_prop (P: prop C): cset :=
      match P with
      | just y => one y
      | success _ => ⊤
      | _ => ⊥
      end.

    #[local]
     Definition chk_horn (H: horn C): cset :=
      match H with
      | entails P Q =>
        let P' := chk_prop P in
        let Q' := ⋀ (List.map chk_prop Q) in
        Q' → P'
      end.

    Definition chk (th: theory C) (x: any_head th): cset := chk_horn (pick th x).
  End interpreter.
End Interpreter.

(* FIXME implement a Heyting algebra using bundles and interpret
everything categorically *)
Module Import Pred.
  #[program]
   Definition predicate_logic A: Heyting := {|
    S := A → Prop ;

    top _ := True ;
    bot _ := False ;

    meet P Q x := P x ∧ Q x ;
    join P Q x := P x ∨ Q x ;
    impl P Q x := P x → Q x ;
  |}.
End Pred.

(* FIXME do the same thing but with bundles ? *)
Module Import Hoas.
  Class Lam := {
    tm: Type ;

    T: tm ;
    P: tm ;

    all: tm → (tm → tm) → tm ;
    lam: tm → (tm → tm) → tm ;
    app: tm → tm → tm ;
              }.
End Hoas.

Module Import Spec.
  Import List.ListNotations.

  Variant type_query `{Lam} := ofty (_ _ : tm).

  Module Export SpecNotations.
    Infix "∈" := ofty (at level 40).
  End SpecNotations.

  Open Scope logic_scope.

  Definition rules `{Lam}: theory type_query :=
    [
      const (just (P ∈ T) ⊢ []) ;

    ∀ A B f x,
      just (app f x ∈ B x) ⊢ [
             just (f ∈ all A B) ;
           just (x ∈ A) ] ;

    (*
       Not sure how I'm going to handle variables, not correct at all here,
       Also not sure how I'm going to handle evaluating expressions
     *)
    ∀ K L A B x,
      just (all A B ∈ K) ⊢ [
             just (A ∈ K) ;
           just (x ∈ A) ;
           just (B x ∈ L)
           ] ;
    ∀ K A B f x,
      just (lam A f ∈ all A B) ⊢ [
             just (A ∈ K) ;
           just (x ∈ A) ;
           just (f x ∈ B x)
           ]
    ].
End Spec.

Definition oftype `{Lam} x A := ∃ y, chk (predicate_logic _) eq rules y (x ∈ A).

Definition foo `{Lam}: oftype P T.
  cbn.
  eexists.
  Unshelve.
  2: {
    cbn.
    left.
    exists.
  }
  cbn.
  reflexivity.
Qed.
