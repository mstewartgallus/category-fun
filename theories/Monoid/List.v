Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Lists.List.

Require Import Blech.Bishop.
Require Import Blech.Monoid.
Require Blech.Monoid.Free.

Import BishopNotations.
Import MonoidNotations.

Open Scope bishop_scope.
Open Scope monoid_scope.

#[local]
 #[program]
 Instance list_Setoid (S: Bishop): Setoid (list S) := {
  equiv := Forall2 equiv ;
 }.
Next Obligation.
Proof.
  exists.
  - intro x.
    induction x.
    + constructor.
    + constructor.
      * reflexivity.
      * assumption.
  - intros x y p.
    induction p.
    + constructor.
    + constructor.
      * symmetry.
        assumption.
      * assumption.
  - intros x y z p q.
    admit.
Admitted.

#[program]
 Definition List (S: Bishop): Monoid := {|
  S := list S /~ list_Setoid S ;

  e := nil ;
  app := @List.app _ ;
|}.

Next Obligation.
Proof.
  rewrite List.app_assoc.
  replace (Forall2 equiv) with equiv.
  all: reflexivity.
Qed.

Next Obligation.
Proof.
  replace (Forall2 equiv) with equiv.
  all: reflexivity.
Qed.

Next Obligation.
Proof.
  rewrite app_nil_r.
  replace (Forall2 equiv) with equiv.
  all: reflexivity.
Qed.

Next Obligation.
Proof.
  intros ? ? p ? ? q.
  apply Forall2_app.
  all: assumption.
Qed.

Fixpoint ε {M: Monoid} (p: List M): M :=
  match p with
  | nil => e
  | cons H T => H · ε T
  end.

Theorem counit_app {M: Monoid} (x y: List M): ε (x ++ y) == ε x · ε y.
Proof.
  induction x.
  - rewrite app_e_left.
    reflexivity.
  - cbn.
    rewrite IHx.
    rewrite app_assoc.
    reflexivity.
Qed.

Import Free.

Fixpoint from_free {S: Bishop} (m: Free S): List S :=
  match m with
  | e => nil
  | η x => cons x nil
  | app x y => from_free x ++ from_free y
  end.
