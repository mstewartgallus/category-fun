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
Require Import Psatz.

Module Import Bundle.
  #[universes(cumulative)]
  Record bundle A := {
    dom: Type ;
    proj: dom → A ;
  }.

  Arguments dom [A].
  Arguments proj [A].

  Coercion dom: bundle >-> Sortclass.
  Coercion proj: bundle >-> Funclass.
End Bundle.

Module Import Logic.
  Import List.ListNotations.

  (* FIXME have an or for results as well ? *)
  Record axiom C := entails {
                       head: bundle C ;
                       tail: bundle C ;
                       }.
  Arguments entails [C].
  Arguments head [C].
  Arguments tail [C].

  Definition axiom_scheme C := bundle (axiom C).
  Definition theory C := bundle (axiom_scheme C).

  (* FIXME make category *)
  Inductive syn {K} {th: theory K}: K → K → Type :=
  | syn_id {A}: syn A A
  | syn_compose {A B C}: syn B C → syn A B → syn A C

  | syn_axiom rule args C D:
      (∀ ix, syn C (tail (th rule args) ix)) →
      (∀ ix, syn (head (th rule args) ix) D) →
      syn C D
  .

  Module Export LogicNotations.
    Declare Scope logic_scope.
    Delimit Scope logic_scope with logic.

    Bind Scope logic_scope with axiom.
    Bind Scope logic_scope with axiom_scheme.
    Bind Scope list_scope with theory.

    Notation "[ P ]" := {| proj := P |} : logic_scope .

    Notation "'FREE' x , P" := (λ x, P) (x pattern, at level 200) : logic_scope .
    Infix "⊢" := entails (at level 90) : logic_scope .
  End LogicNotations.
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
  Open Scope logic_scope.

  Infix "∧" := and.
  Infix "∨" := or.

  Variant idx :=
  | taut
  | bang
  | inl | inr | fanin
  | fst | snd | fanout.

  Definition propositional `{Propositional}: theory P := {|
    dom := idx ;
    proj x :=
      match x with
      | taut => [FREE I,
                [FREE I, true] ⊢ [ λ (ix: False), match ix with end ]]
      | bang => [FREE A,
                [FREE I, A] ⊢ [FREE I, false]]

      | fanout => [FREE (A, B),
                  [FREE I, A ∧ B] ⊢ [ λ (ix: bool), if ix then A else B ]]
      | fst => [FREE (A, B),
               [FREE I, A] ⊢ [FREE I, A ∧ B]]
      | snd => [FREE (A, B),
               [FREE I, B] ⊢ [FREE I, A ∧ B]]

      | fanin => [FREE (A, B),
                 [λ (ix: bool), if ix then A else B] ⊢ [FREE I, A ∨ B]]
      | inl => [FREE (A, B),
               [FREE I, A ∨ B] ⊢ [FREE I, A]]
      | inr => [FREE (A, B),
               [FREE I, A ∨ B] ⊢ [FREE I, B]]
      end
   |}.

  Section sanity.
    Context `{Propositional}.

    Definition free := @syn _ propositional.

    Definition taut' C: free C true := @syn_axiom _ propositional
                                                  taut I
                                                  C true
                                     (λ ix, match ix with end)
                                     (FREE I, syn_id).

    Definition bang' C: free false C := @syn_axiom _ propositional
                                                   bang C
                                                   false C
                                                   (FREE I, syn_id)
                                                   (FREE I, syn_id).

    Definition inl' A B: free A (A ∨ B) := @syn_axiom _ propositional
                                                      inl (A, B)
                                                      A (A ∨ B)
                                                      (FREE I, syn_id) (FREE I, syn_id).
    Definition inr' A B: free B (A ∨ B) := @syn_axiom _ propositional
                                                      inr (A, B)
                                                      B (A ∨ B)
                                                      (FREE I, syn_id)
                                                      (FREE I, syn_id).

    #[program]
    Definition fanin' C A B (f: free A C) (g: free B C) :=
      @syn_axiom _ propositional
                 fanin (A, B)
                 (A ∨ B) C
                 (FREE I, syn_id) _.

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
                 _ (FREE I, syn_id).
    Next Obligation.
      destruct ix.
      - apply f.
      - apply g.
    Defined.

    Definition fst' A B: free (A ∧ B) A := @syn_axiom _ propositional
                                                      fst (A, B)
                                                      (A ∧ B) A
                                                      (FREE I, syn_id) (FREE I, syn_id).
    Definition snd' A B: free (A ∧ B) B := @syn_axiom _ propositional
                                                      snd (A, B)
                                                      (A ∧ B) B
                                                      (FREE I, syn_id) (FREE I, syn_id).

  End sanity.
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
