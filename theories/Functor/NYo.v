Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Functor.
Require Import Blech.Category.Bsh.
Require Import Blech.Category.Funct.
Require Import Blech.Category.Prod.
Require Import Blech.Category.NPSh.
Require Import Blech.Category.Op.
Require Import Blech.Groupoid.
Require Import Blech.Groupoid.Fin.
Require Import Blech.Functor.Curry.
Require Blech.Reflect.

Import CategoryNotations.
Import FunctorNotations.
Import BishopNotations.
Import ProdNotations.
Import OpNotations.

Open Scope category_scope.
Open Scope bishop_scope.

#[local]
Obligation Tactic := Reflect.category_simpl.

#[program]
 Definition NYo C M N (m: Fin.t M): Functor C (NPSh C M N) :=
  curry {|
  op (ab: C * (Prod (Funct (Fin M) (C ᵒᵖ)) (Funct (Fin N) C))) := C (fst (snd ab) m) (fst ab) : Bsh ;
  map _ _ '(a, (x, y)) (f: C _ _) := (a: C _ _) ∘ f ∘ (x m: C _ _) ;
|}.

Next Obligation.
Proof.
  cbn in *.
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
  intros ? ? p ?.
  destruct p as [p q].
  cbn in *.
  destruct x, y.
  cbn in *.
  destruct snd, snd0.
  cbn in *.
  rewrite p.
  destruct q.
  rewrite H.
  reflexivity.
Qed.

#[program]
 Definition NCoYo C M N (n: Fin.t N): Functor (C ᵒᵖ) (NPSh C M N) :=
  curry {|
    op (ab: (C ᵒᵖ) * (Prod (Funct (Fin M) (C ᵒᵖ)) (Funct (Fin N) C))) := C (fst ab) (snd (snd ab) n) : Bsh ;
    map _ _ '(a, (x, y)) (f: C _ _) := (y n: C _ _) ∘ f ∘ (a: C _ _) ;
|}.

Next Obligation.
Proof.
  cbn in *.
  intros ? ? p.
  rewrite p.
  reflexivity.
Qed.

Next Obligation.
Proof.
  intros ? ? p ?.
  destruct p as [p q].
  cbn in *.
  destruct x, y.
  cbn in *.
  destruct snd, snd0.
  cbn in *.
  rewrite p.
  destruct q.
  rewrite H0.
  reflexivity.
Qed.
