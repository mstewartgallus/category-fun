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
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Module Import Bundle.
  #[universes(cumulative)]
  Record bundle A := suprema {
    s: Type ;
    π: s → A ;
  }.

  Arguments suprema [A s].
  Arguments s [A].
  Arguments π [A].

  Coercion s: bundle >-> Sortclass.
  Coercion π: bundle >-> Funclass.

  Notation "'sup' x .. y , P" := {| π x := .. {| π y := P |} .. |}
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' 'sup'  x .. y ']' , '/' P ']'").
End Bundle.

Module Import Span.

  #[universes(cumulative)]
  Record span A B := {
    s: Type ;
    π1: s → A ;
    π2: s → B ;
  }.

  Arguments s [A B].
  Arguments π1 [A B].
  Arguments π2 [A B].

  Coercion s: span >-> Sortclass.

  Module Export SpanNotations.
    Reserved Notation "'SPAN' x , P ———— Q" (x ident, at level 90, format "'SPAN' x , '//' P '//' ———— '//' Q").
    Reserved Notation "'SPAN' x : A , P ———— Q" (x ident, at level 90, format "'SPAN' x : A , '//' P '//' ———— '//' Q").
    Reserved Notation "'SPAN' ( x : A ) , P ———— Q" (x ident, at level 90, format "'SPAN' ( x : A ) , '//' P '//' ———— '//' Q").

    Notation "'SPAN' x , P ———— Q" := {| π1 x := P ; π2 x := Q |} .
    Notation "'SPAN' x : A , P ———— Q" := {| π1 (x : A) := P ; π2 (x : A) := Q |} .
    Notation "'SPAN' ( x : A ) , P ———— Q" := {| π1 (x : A) := P ; π2 (x : A) := Q |} .
  End SpanNotations.
End Span.

Module Import Logic.
  Import List.ListNotations.

  (* FIXME have an or for results as well ? *)
  Definition axiom C := span C C.

  Definition axiom_scheme C := bundle (axiom C).
  Definition theory C := bundle (axiom_scheme C).

  (* FIXME make category *)
  Inductive syn {K} {th: theory K}: K → K → Type :=
  | syn_id {A}: syn A A
  | syn_compose {A B C}: syn B C → syn A B → syn A C

  | syn_axiom rule args C D:
      (∀ ix, syn C (π1 (th rule args) ix)) →
      (∀ ix, syn (π2 (th rule args) ix) D) →
      syn C D
  .
End Logic.

Module Import Sanity.
  #[universes(cumulative)]
  Class Propositional := {
    P: Type ;

    true: P ;
    and: P → P → P ;

    false: P ;
    or: P → P → P ;
  }.

  Infix "∧" := and.
  Infix "∨" := or.

  Variant idx :=
  | bang
  | absurd
  | inl | inr | fanin
  | fst | snd | fanout.

  Definition propositional `{Propositional}: theory P := sup ix,
    match ix with
    | bang => sup A,
              SPAN (_: True),
               A
               ————
               true

    | absurd => sup A,
                SPAN (_: True),
                  false
                  ————
                  A

    | fanin => sup '(A, B),
                SPAN b:bool,
                      A ∨ B
                      ————
                      if b then A else B

    | inl => sup '(A, B),
             SPAN _:True,
                   A
                   ————
                   A ∨ B
    | inr => sup '(A, B),
             SPAN _:True,
                   B
                   ————
                   A ∨ B

    | fanout => sup '(A, B),
                SPAN b:bool,
                      (if b then A else B)
                      ————
                      A ∧ B

    | fst => sup '(A, B),
             SPAN _:True,
                   A ∧ B
                   ————
                   A

    | snd => sup '(A, B),
             SPAN _:True,
                   A ∧ B
                   ————
                   B
    end
    .


  Section sanity.
    Context `{Propositional}.

    Definition free := @syn _ propositional.

    Definition bang' C: free C true := @syn_axiom _ propositional
                                                  bang C
                                                  C true
                                                  (λ _, syn_id)
                                                  (λ _, syn_id).

    Definition inl' A B: free A (A ∨ B) := @syn_axiom _ propositional
                                                      inl (A, B)
                                                      A (A ∨ B)
                                                      (λ _, syn_id) (λ _, syn_id).
    Definition inr' A B: free B (A ∨ B) := @syn_axiom _ propositional
                                                      inr (A, B)
                                                      B (A ∨ B)
                                                      (λ _, syn_id)
                                                      (λ _, syn_id).

    #[program]
    Definition fanin' C A B (f: free A C) (g: free B C) :=
      @syn_axiom _ propositional
                 fanin (A, B)
                 (A ∨ B) C
                 (λ _, syn_id) _.

    Next Obligation.
      destruct ix.
      - apply f.
      - apply g.
    Defined.

    #[program]
     Definition fanout' C A B (f: free C A) (g: free C B): free C (A ∧ B) :=
      @syn_axiom _ propositional
                 fanout (A, B)
                 C (A ∧ B)
                 _ (λ _, syn_id).
    Next Obligation.
      destruct ix.
      - apply f.
      - apply g.
    Defined.

    Definition fst' A B: free (A ∧ B) A := @syn_axiom _ propositional
                                                      fst (A, B)
                                                      (A ∧ B) A
                                                      (λ _, syn_id) (λ _, syn_id).
    Definition snd' A B: free (A ∧ B) B := @syn_axiom _ propositional
                                                      snd (A, B)
                                                      (A ∧ B) B
                                                      (λ _, syn_id) (λ _, syn_id).
  End sanity.

  Instance as_Prop: Propositional := {
    P := Prop ;

    true := True ;
    and := Logic.and ;

    false := False ;
    or := Logic.or ;
  }.

  Definition eval_Prop [A B: @P as_Prop]: free A B → A → B.
    intros f.
    induction f.
    - intro x.
      apply x.
    - intro x.
      apply (IHf1 (IHf2 x)).
    - destruct rule.
      all: cbn in *.
      + intro x.
        apply H0.
        all: auto.
      + intro x.
        set (H' := H I x).
        contradiction.
      + intro x.
        destruct args as [P Q].
        cbn in *.
        apply (H0 I).
        left.
        apply (H I x).
      + intro x.
        destruct args as [P Q].
        cbn in *.
        apply (H0 I).
        right.
        apply (H I x).
      + destruct args as [P Q].
        cbn in *.
        intro x.
        refine (_ (H Datatypes.false x)).
        * intro x'.
          destruct x'.
          -- apply (H0 Datatypes.true H1).
          -- apply (H0 Datatypes.false H1).
      + destruct args as [P Q].
        cbn in *.
        intro x.
        apply (H0 I).
        apply (H I x).
      + destruct args as [P Q].
        cbn in *.
        intro x.
        apply (H0 I).
        apply (H I x).
      + destruct args as [P Q].
        cbn in *.
        intro x.
        apply (H0 Datatypes.false).
        split.
        * apply (H Datatypes.true x).
        * apply (H Datatypes.false x).
  Defined.

  Instance as_Set: Propositional := {
    P := Set ;

    true := unit ;
    and := prod ;

    false := Empty_set ;
    or := sum ;
  }.

  Definition eval_Set [A B: @P as_Set]: free A B → A → B.
    intros f.
    induction f.
    - intro x.
      apply x.
    - intro x.
      apply (IHf1 (IHf2 x)).
    - destruct rule.
      all: cbn in *.
      + intro x.
        apply (H0 I tt).
      + intro x.
        set (H' := H I x).
        contradiction.
      + intro x.
        destruct args as [P Q].
        cbn in *.
        apply (H0 I).
        left.
        apply (H I x).
      + intro x.
        destruct args as [P Q].
        cbn in *.
        apply (H0 I).
        right.
        apply (H I x).
      + destruct args as [P Q].
        cbn in *.
        intro x.
        refine (_ (H Datatypes.false x)).
        * intro x'.
          destruct x' as [p|q].
          -- apply (H0 Datatypes.true p).
          -- apply (H0 Datatypes.false q).
      + destruct args as [P Q].
        cbn in *.
        intro x.
        apply (H0 I).
        apply (H I x).
      + destruct args as [P Q].
        cbn in *.
        intro x.
        apply (H0 I).
        apply (H I x).
      + destruct args as [P Q].
        cbn in *.
        intro x.
        apply (H0 Datatypes.false).
        split.
        * apply (H Datatypes.true x).
        * apply (H Datatypes.false x).
  Defined.

  Example foo `{Propositional}: free true (true ∧ true) := fanout' _ _ _ (bang' _) (bang' _).

  Definition foo' := eval_Set foo.
End Sanity.


(* FIXME do the same thing but with bundles ? *)
Module Import Hoas.
  #[universes(cumulative)]
  Class Lam := {
    tm: Type ;
    ty: Type ;

    pt: ty ;
    exp: ty → ty → ty ;

    lam: ty → (tm → tm) → tm ;
    app: tm → tm → tm ;
  }.
End Hoas.

Module Import Spec.
  Import List.ListNotations.

  Variant type_query `{Lam} := ofty (_:tm) (_: ty).

  Module Export SpecNotations.
    Infix "∈" := ofty (at level 40).
  End SpecNotations.

  Open Scope logic_scope.

  Variant index := app_rule | lam_rule.
  Definition stlc `{Lam}: theory type_query := {|
    dom := index ;
    proj x :=
      match x with
      | app_rule => FREE (A, B, f, x) ,
                      app f x ∈ B ⊢ [
                           f ∈ exp A B ;
                           x ∈ A ]
        (*
       Not sure how I'm going to handle variables, not correct at all here,
       Also not sure how I'm going to handle evaluating expressions
         *)
      | lam_rule => FREE (A, B, f, x) ,
                      lam A f ∈ exp A B ⊢ [
                           x ∈ A ;
                           f x ∈ B]
      end
   |}.
End Spec.

Module Import Sanity.
  Import List.ListNotations.

  Section sanity.
    Context `{Lam}.

    Definition free := @syn _ stlc.

    Definition foo x A: free [ x ∈ A ; x ∈ A ] [].
      apply (syn_weaken nil).
    Defined.
  End sanity.
End Sanity.

Module Import Lattice.
  #[universes(cumulative)]
  Class Lattice := {
    S: Type ;

    top: S ;
    bot: S ;

    meet: S → S → S ;
    join: S → S → S ;
  }.

  Definition meet_all `{Lattice}: list S → S := List.fold_right meet top.
  Definition join_all `{Lattice}: list S → S := List.fold_right join bot.

  Module Export LatticeNotations.
    Declare Scope lattice_scope.
    Delimit Scope lattice_scope with lattice.
    Bind Scope lattice_scope with S.

    Notation "⊤" := top : lattice_scope.
    Notation "⊥" := bot : lattice_scope.

    Infix "∧" := meet : lattice_scope.

    Notation "⋀" := meet_all : lattice_scope.
    Notation "⋁" := join_all : lattice_scope.

    Coercion S: Lattice >-> Sortclass.
  End LatticeNotations.
End Lattice.

(* FIXME implement a Lattice algebra using bundles and interpret
everything categorically *)
Module Import Pred.
  #[program]
   Definition predicate_logic A: Lattice := {|
    S := A → Prop ;

    top _ := True ;
    bot _ := False ;

    meet P Q x := P x ∧ Q x ;
    join P Q x := P x ∨ Q x ;
  |}.
End Pred.


Module Import Sanity.
  Local Set Implicit Arguments.


  Definition ofty `{Lam} A B f x := check stlc app_rule (A, B, f, x).
  Check ofty.
  Definition ofty `{Lam} i v x A :=
    let (H, T) := chk (predicate_logic _) (simplify pred_stlc) {| ix := i ; val := v |}  in
    H (x ∈ A) → T (x ∈ A).
  Definition foo `{Lam} A: ofty (lam A (λ x, x)) (exp A A).
    exists lam_rule.
    intro.
    cbn in *.
    destruct .
    
  Definition bar `{Lam} := foo 0 I.
  #[program]
   Definition bar `{Lam} := foo 1 _.
  Next Obligation.
    cbn.
  (* Definition foo `{Lam}: oftype (λ x, x = P ∈ T) (λ x, x = P ∈ T) *)
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
End Sanity.

Module Import Foo.
  Definition type_Lattice := {|
    S := Set ;

    top := True ;
    bot := False ;

    meet P Q := P * Q ;
    join P Q := P + Q ;
  |}.
  Definition oftype `{Lam} (p: any_head rules) :=
      let (H, T) := chk type_Lattice (λ q, {x: type_query | q = x}) rules p in
      T → H.

  Definition bar `{Lam} : any_head rules.
    cbn.
    left.
    exists.
  Defined.

  Definition foo `{Lam}: oftype bar.
    cbn.
    intros.
    exists (P ∈ T).
    reflexivity.
  Defined.
End Foo.
