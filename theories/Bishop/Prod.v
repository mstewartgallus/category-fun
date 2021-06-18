Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Bishop.Exp.

Import BishopNotations.
Import ExpNotations.

Open Scope bishop_scope.

Close Scope nat.

#[program]
Definition prod (A B: Bishop): Bishop := A * B /~ {| equiv x y := fst x == fst y ∧ snd x == snd y |}.

Next Obligation.
Proof.
  exists.
  all: unfold Reflexive, Symmetric, Transitive.
  - split.
    all: reflexivity.
  - split.
    all: symmetry.
    all: apply H.
  - intros ? ? ? p q.
    destruct p as [p p'], q as [q q'].
    rewrite p, q, p', q'.
    split.
    all: reflexivity.
Qed.

#[program]
Definition fanout {C A B: Bishop} (f: exp C A) (g: exp C B): exp C (prod A B) := λ x, (f x, g x).

Next Obligation.
Proof.
  admit.
Admitted.


#[program]
Definition fst {A B: Bishop}: exp (prod A B) A := fst.

Next Obligation.
Proof.
  intros ? ? p.
  destruct p as [p q].
  apply p.
Qed.

#[program]
 Definition snd {A B: Bishop}: exp (prod A B) B := snd.

Next Obligation.
Proof.
  intros ? ? p.
  destruct p as [p q].
  apply q.
Qed.

Module ProdNotations.
  Infix "*" := prod : bishop_scope.
End ProdNotations.
