Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Import Blech.Proset.
Require Import Blech.Proset.Heyting.

Import ProsetNotations.
Import HeytingNotations.

(* Ostensibly, a first order system of logic is a free heyting algebra over the
set of free variables *)
Inductive free (T: Type) :=
| var (_: T)
| top
| bot
| meet (_ _: free T)
| join (_ _: free T)
| impl (_ _: free T)
.

Arguments var [T].
Arguments top {T}.
Arguments bot {T}.
Arguments meet {T}.
Arguments join {T}.
Arguments impl {T}.

Inductive entails {T}: relation (free T) :=
| reflexive: reflexive (free T) entails
| transitive: transitive (free T) entails

| bang {A}: entails A top
| fanout {C A B}: entails C A → entails C B → entails C (meet A B)
| fst {A B}: entails (meet A B) A
| snd {A B}: entails (meet A B) B

| absurd {A}: entails top A
| fanin {C A B}: entails A C → entails B C → entails (join A B) C
| inl {A B}: entails A (join A B)
| inr {A B}: entails B (join A B)

| curry {A B C}: entails (meet A B) C → entails A (impl B C)
| eval {A B}: entails (meet (impl A B) A) B
.

#[program]
Definition Free (S: Type) : Heyting := {|
  P := {|
        T := free S ;
        preorder := entails ;
  |} ;

  Heyting.top := top ;
  Heyting.bot := bot ;

  Heyting.meet := meet ;
  Heyting.join := join ;
  Heyting.impl := impl ;
|}.

Next Obligation.
Proof.
  admit.
Admitted.
