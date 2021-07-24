Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Strings.String.
Require Coq.Vectors.Fin.

Require Import Blech.Bishop.
Require Blech.Bishop.Prod.
Require Import Blech.Bishop.Sum.
Require Import Blech.Bishop.Trv.
Require Import Blech.Bishop.Mt.
Require Import Blech.Category.
Require Import Blech.Groupoid.
Require Import Blech.Functor.
Require Import Blech.Category.Bsh.
Require Import Blech.Groupoid.Core.
Require Import Blech.Category.Prod.
Require Import Blech.Category.Funct.
Require Import Blech.Category.Op.
Require Import Blech.Groupoid.Fin.
Require Import Blech.Type.Some.
Require Import Blech.Type.Truncate.
Require Blech.Reflect.

Import CategoryNotations.
Import GroupoidNotations.
Import FunctorNotations.
Import BishopNotations.
Import ProdNotations.
Import SumNotations.
Import OpNotations.
Import SomeNotations.
Import TruncateNotations.

Open Scope category_scope.
Open Scope bishop_scope.

#[local]
Obligation Tactic := Reflect.category_simpl.

Module Analogy.

  (* We define analogous interpretations using propositions instead of Set *)
  Definition rel V := (nat -> V) -> Prop.

  Definition and {V} (A B: rel V): rel V :=
    λ Γ, A Γ ∧ B Γ.
  Definition or {V} (A B: rel V): rel V :=
    λ Γ, A Γ ∨ B Γ.
  Definition impl {V} (A B: rel V): rel V :=
    λ Γ, A Γ -> B Γ.

  Definition true {V}: rel V :=
    λ Γ, True.
  Definition false {V}: rel V :=
    λ Γ, False.

  Definition unify {V} (i j: nat): rel V :=
    λ Γ, Γ i = Γ j.

  Definition put {V} (Γ: nat → V) (i: nat) (v: V) (j: nat): V :=
    if Nat.eqb i j then v else Γ j.
  Definition Forall {V} (i: nat) (A: rel V) : rel V :=
    λ Γ, ∀ v, A (put Γ i v).
  Definition Forsome {V} (i: nat) (A: rel V) : rel V :=
    λ Γ, ∃ v, A (put Γ i v).

  Definition close {V} (P: rel V): Prop :=
    ∀ Γ, P Γ.

  Notation "⊤" := true.
  Notation "⊥" := false.
  Infix "∧" := and.
  Infix "∨" := or.
  Infix "~" := unify (at level 30, no associativity).
  Infix "→" := impl.

  Open Scope string_scope.
  Open Scope nat_scope.

  Example trivial {V}: @close V true.
  Proof.
    intro.
    unfold true.
    exists.
  Qed.

  Definition A := 0.
  Definition B := 1.

  Example silly: @close nat (
    Forsome B (Forall A (A ~ B)) → ⊥).
  Proof.
    unfold A, B, close, impl, false, Forall, Forsome, unify.
    intros Γ p.
    destruct p as [x p].
    destruct x.
    + set (q := p 1).
      cbn in *.
      discriminate.
    + set (q := p 0).
      cbn in *.
      discriminate.
  Qed.
End Analogy.

Definition Cylinder M N (V: Category) := Funct (Funct M V * (Funct N V ᵒᵖ)) Bsh.

#[program]
Definition prod {M N V} (A B: Cylinder M N V): Cylinder M N V := {|
  op (Γ: (Funct M V) * (Funct N V ᵒᵖ)) := Prod.prod (A Γ) (B Γ) ;
  map '(_, _) '(_, _) '(f, g) '(x, y) := (map A (f, g) x, map B (f, g) y) ;
|}.

Next Obligation.
Proof.
  intros ? ? p.
  destruct p as [p q].
  cbn.
  rewrite p, q.
  split.
  all: reflexivity.
Qed.

Next Obligation.
Proof.
Admitted.

Next Obligation.
Proof.
Admitted.

Next Obligation.
Proof.
Admitted.

#[program]
Definition sum {M N V} (A B: Cylinder M N V): Cylinder M N V := {|
  op (Γ: (Funct M V) * (Funct N V ᵒᵖ)) := A Γ + B Γ ;
  map _ _ f x :=
    match x with
    | Datatypes.inl x => Datatypes.inl (map A f x)
    | Datatypes.inr x => Datatypes.inr (map B f x)
    end
|}.

Next Obligation.
Proof.
  intros ? ? p.
  cbn.
  unfold sum_eqv.
  cbn in *.
  destruct x, y.
  all: cbn in *.
  all: try contradiction.
  all: rewrite p.
  all: reflexivity.
Qed.

Next Obligation.
Proof.
Admitted.

Next Obligation.
Proof.
Admitted.

Next Obligation.
Proof.
Admitted.

#[program]
Definition pure {M N V} (o: Bsh): Cylinder M N V := {|
  op _ := o ;
  map _ _ _ := id _ ;
|}.

Next Obligation.
Proof.
  intros ? ? p ?.
  cbn.
  reflexivity.
Qed.

Definition true {M N V}: Cylinder M N V := pure trv.
Definition false {M N V}: Cylinder M N V := pure mt.

#[program]
Definition unify {M N V: Category} (i: M) (j: N): Cylinder M N V := {|
  op '(Γ, Δ) := V (Δ j) (Γ i) ;
  map '(A, B) '(A', B') '(f, g) x := proj1_sig f _ ∘ x ∘ proj1_sig g _ ;
|}.

Next Obligation.
Proof.
  intros ? ? p.
  rewrite p.
  reflexivity.
Qed.

Next Obligation.
Proof.
  rewrite compose_id_left.
  rewrite compose_id_right.
  reflexivity.
Qed.

Next Obligation.
Proof.
  intros ? ? p x.
  destruct p as [p q].
  cbn in *.
  rewrite (p _).
  rewrite (q _).
  reflexivity.
Qed.

#[program]
Definition put {M} {V: Category} (i: Fin M) (Γ: Functor (Fin M) V): Functor V (Funct (Fin M) V) :=
 {|
  op v :=
    {|
      op j := if Fin.eq_dec i j then v else Γ j ;
      map _ _ f := _ ;
    |} ;
  map _ _ f g := _ ;
 |}.

(* FIXME doesn't seem right at all *)
Next Obligation.
Proof.
  destruct (Fin.eq_dec i H0) eqn:q.
  - subst.
    apply id.
  - apply (map Γ (id _)).
Defined.

Next Obligation.
Proof.
Admitted.

Next Obligation.
Proof.
Admitted.

Next Obligation.
Proof.
Admitted.

Next Obligation.
Proof.
  destruct (Fin.eq_dec i g) eqn:q.
  - subst.
    apply f.
  - apply id.
Defined.

Next Obligation.
Proof.
Admitted.

Next Obligation.
Proof.
Admitted.

Next Obligation.
Proof.
Admitted.

Next Obligation.
Proof.
Admitted.

#[program]
Definition Forall {M N V} (i: Fin M) (A: Cylinder (Fin M) N V) : Cylinder (Fin M) N V := {|
  op '(Γ, Δ) := (∀ v, A (put i Γ v, Δ)) /~ {| equiv x y := ∀ t, x t == y t |} ;
  map _ _ '(f, g) x := _ ;
|}.

Next Obligation.
Proof.
Admitted.

Next Obligation.
Proof.
Admitted.

Next Obligation.
Proof.
Admitted.

Next Obligation.
Proof.
Admitted.

Next Obligation.
Proof.
Admitted.

Next Obligation.
Proof.
Admitted.


#[program]
Definition Forsome {M N V} (i: Fin M) (A: Cylinder (Fin M) N V) : Cylinder (Fin M) N V := {|
  op '(Γ, Δ) := (Σ v, A (put i Γ v, Δ))
                  /~ {| equiv '⟨H, T⟩ '⟨H', T'⟩ :=
                          ∃ (f: H' ~> H), T == proj1_sig (map A (_, _)) T' |} ;
  map _ _ '(f, g) x := _ ;
|}.

Next Obligation.
Proof.
  refine (map (put i Γ) f).
Defined.

Next Obligation.
Proof.
  apply (id (Δ: Funct _ _)).
Defined.

Next Obligation.
Proof.
Admitted.

Next Obligation.
Proof.
Admitted.

Next Obligation.
Proof.
Admitted.

Next Obligation.
Proof.
Admitted.

Next Obligation.
Proof.
Admitted.

#[program]
Definition close {M N V} (P: Cylinder M N V): Bsh :=
    (∀ Γ Δ, P (Γ, Δ)) /~ {| equiv x y := ∀ Γ Δ, x Γ Δ == y Γ Δ |}.

Next Obligation.
Proof.
Admitted.
