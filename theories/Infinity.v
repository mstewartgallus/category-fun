Require Import Blech.Defaults.

Require Import Coq.Logic.JMeq.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Bool.Bool.
Require Coq.Program.Basics.
Require Coq.Program.Tactics.

Require Import Blech.Truncate.
Require Import Blech.Some.
Require Import Blech.Bishop.
Require Import Blech.Category.
Require Import Blech.Categories.
Require Import Blech.Groupoid.
Require Import Blech.Reflect.
Require Import Blech.Core.
Require Import Blech.Functor.
Require Import Blech.Categories.Op.
Require Import Blech.Categories.Bsh.
Require Import Blech.Categories.El.
Require Import Blech.Categories.Over.
Require Blech.Categories.Prod.
Require Blech.PointedGroupoid.
Require Blech.Group.
Require Blech.Pointed.
Require Blech.Groupoids.
Require Blech.Functors.
Require Blech.Bishops.
Require Blech.Monoids.
Require Psatz.

Import CategoryNotations.
Import CategoriesNotations.
Import OpNotations.
Import BishopNotations.
Import Bishops.BishopsNotations.
Import Group.GroupNotations.
Import GroupoidNotations.
Import FunctorNotations.
Import Prod.ProdNotations.
Import Pointed.PointedNotations.
Import PointedGroupoid.PointedNotations.
Import OverNotations.

Reserved Notation "'lim' A , P" (right associativity, at level 200).
Reserved Notation "'glb' A , P" (right associativity, at level 200).

Reserved Notation "A <: B" (at level 80).

Reserved Notation "F 'ᵀ'" (at level 1).

Reserved Notation "C // c" (at level 40, left associativity).


Reserved Notation "X \ Y" (at level 30).

Obligation Tactic := Reflect.category_simpl.

Open Scope bishop_scope.

Definition slice_cat [C D: Category] A B := Pointed.Funct (Pointed.Point (I₊ * C) (true, A)) (Pointed.Point D B).

Module Import Profunctor.
  Definition Prof C D := Funct (C * D ᵒᵖ) Bsh.
End Profunctor.

(* IDK a better name for this comma like gadget *)
Module Import Heteromorphisms.
  Definition Hetero [C D: Category]: Prof C D → Category := @El _ .
End Heteromorphisms.

Module Terminal.
  Class Category := Term {
    C: Category.Category ;
    pt: C ;
    bang A: A ~> pt ;
    compose_bang_right [A B] (f: A ~> B): bang _ ∘ f == bang _ ;
  }.

  Module TerminalNotations.
    Coercion C: Category >-> Category.Category.
    Existing Instance C.

    Notation "!" := bang.
  End TerminalNotations.
End Terminal.

Import Terminal.TerminalNotations.

Module Presheaf.
  Definition Space C := Funct (C ᵒᵖ) Bsh.
  Definition Quantity C := Funct C Bsh.

  #[program]
   Definition Yo C: Funct C (Space C) := Functors.curry {|
    op (ab: C * (C ᵒᵖ)) := C (snd ab) (fst ab) : Bsh ;
    map _ _ '(a, b) (f: C _ _) :=
      (a: C _ _) ∘ f ∘ (b: C _ _) ;
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
    cbn in *.
    rewrite H, H0.
    reflexivity.
  Qed.

  #[program]
   Definition CoYo C: Funct (C ᵒᵖ) (Quantity C) := Functors.curry {|
    op (ab: (C ᵒᵖ) * C) := C (fst ab) (snd ab): Bsh ;
    map _ _ ab (f: C _ _) :=
      let a := fst ab : C _ _ in
      let b := snd ab : C _ _ in
      b ∘ f ∘ a ;
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
    rewrite H, H0.
    reflexivity.
  Qed.

  #[program]
   Definition Spec [C: Category] (A: Quantity C): Space C := {|
    op (u: C ᵒᵖ) := A ~> (CoYo C) u : Bishop ;
    map _ _ x y _ z := y _ z ∘ x ;
   |}.

  Next Obligation.
  Proof.
    intros ? ? p.
    rewrite p.
    reflexivity.
  Qed.

  Next Obligation.
  Proof.
    intros ? ? p ? ?.
    cbn in *.
    apply compose_compat.
    2: reflexivity.
    rewrite (p _ _).
    reflexivity.
  Qed.

  Next Obligation.
  Proof.
    rewrite H.
    reflexivity.
  Qed.

    #[program]
   Definition CoSpec [C: Category] (A: Space C): Quantity C := {|
      op (u: C) := A ~> (Yo C) u : Bishop ;
      map _ _ x y _ z := x ∘ y _ z ;
    |}.

  Next Obligation.
  Proof.
    intros ? ? p.
    rewrite p.
    reflexivity.
  Qed.

  Next Obligation.
  Proof.
    intros ? ? p ? ?.
    cbn in *.
    apply compose_compat.
    1: reflexivity.
    rewrite (p _ _).
    reflexivity.
  Qed.

  Next Obligation.
  Proof.
    rewrite H.
    reflexivity.
  Qed.

  #[program]
  Definition pop_obj [C: Category] (P: Funct (C ᵒᵖ) Bsh) (F: Funct ((El P) ᵒᵖ) Bsh):=
  lub ({|
      op (A: C ᵒᵖ) := (Σ (p: P A), F ⟨ A , p ⟩) /~ {| equiv := eq |} : Bishop;
      map _ _ (f: C ᵒᵖ _ _) '⟨ c , x ⟩ := ⟨ map P f c , map F _ x ⟩ ;
    |}: Funct (C ᵒᵖ) Bsh),
  λ _ '⟨ c , _ ⟩, c.

  Next Obligation.
  Proof.
    intros.
    exists f.
    intros.
    reflexivity.
  Defined.

  Next Obligation.
  Proof.
    intros ? ? p.
    rewrite p.
    reflexivity.
  Qed.

  Next Obligation.
  Proof.
    split.
    rewrite p.
    reflexivity.
  Qed.

  #[program]
  Definition pop [C: Category] (P: Space C): Funct (Space (El P)) (Space C/P) := {|
    op := pop_obj ;
    map _ _ f g := _ ;
  |}.
  Close Scope nat.
  #[program]
   Definition push [C: Category] (P: Space C): Funct ((Space C/P) * ((El P)ᵒᵖ)) Bishop := {|
    op fAp :=
      { x | tail (snd fAp) == π (fst fAp) (head (snd fAp)) x  } /~ {| equiv x y := proj1_sig x == proj1_sig y |} ;
    map '(a, c & x) '(a', c' & x') '(f, g) x := _ ;
   |}.

  Next Obligation.
  Proof.
    exists.
    - intros ?.
      reflexivity.
    - intros ? ? ?.
      symmetry.
      auto.
    - intros ? ? ? s t.
      rewrite s, t.
      reflexivity.
  Qed.



  #[program]
  Definition dep_sum [C: Category] [c: C] (F: C/c): Funct (C/s F) (C/c) := {|
    op (G:C/s F) := lub _, π F ∘ π G ;
    map _ _ x := x ;
  |}.

  Next Obligation.
  Proof.
    rewrite <- compose_assoc.
    rewrite H.
    reflexivity.
  Qed.

  #[program]
   Definition pullback_op [C: Category] [c: C] (F: C/c) (G: C/c) (y:C ᵒᵖ): Bishop :=
     { xy : C y (s F) * C y (s G) | π F ∘ fst xy == π G ∘ snd xy }
    /~ {| equiv x y := fst x == fst y ∧ snd x == snd y |}.

  Next Obligation.
  Proof.
    exists.
    - intros ?.
      split.
      all: intros.
      all: reflexivity.
    - intros ? ? p.
      destruct p as [p q].
      cbn in *.
      split.
      all: intros.
      all: symmetry.
      all: auto.
    - intros ? ? ? p q.
      destruct p as [p p'], q as [q q'].
      split.
      all: intros.
      1: rewrite p, q.
      2: rewrite p', q'.
      all: reflexivity.
  Qed.

  Import Prod.

  Definition pullback_op'
             [C: Category] [c: C]
             (A: Prod (Prod (C/c) (C/c)) (C ᵒᵖ)): Bishop :=
    pullback_op (fst (fst A)) (snd (fst A)) (snd A).

  #[program]
   Definition pullback_map [C: Category] [c: C]
   (A B: Prod (Prod (C/c) (C/c)) (C ᵒᵖ))
   (fs: A ~> B): pullback_op' A ~> pullback_op' B :=
    let '(f, g, x) := fs in
    λ '(a, b),
    ((f: C _ _) ∘ (a : C _ _) ∘ (x: C _ _),
     (g: C _ _) ∘ (b : C _ _) ∘ (x: C _ _)).

  Next Obligation.
  Proof.
    cbn in *.
    repeat rewrite compose_assoc.
    rewrite H3.
    rewrite H0.
    rewrite H.
    reflexivity.
  Qed.

  Next Obligation.
  Proof.
    cbn in *.
    intros L R p.
    cbn in *.
    destruct L as [L Lp], R as [R Rp], p.
    cbn in *.
    destruct L, R.
    cbn in *.
    split.
    - rewrite H3.
      reflexivity.
    - rewrite H4.
      reflexivity.
  Qed.

  #[program]
   Definition pullback' {C: Category} {c:Space C}: Funct ((Space C/c) * (Space C/c) * (C ᵒᵖ)) Bishop
    :=
    {|
    op x := pullback_op' (fst (fst x), snd (fst x), Yo C (snd x)) ;
    map '(a0, b0, c0) '(a1, b1, c1) '(F, G, x) :=
      pullback_map (a0, b0, _) (a1, b1, _) (F, G, map (Yo C) x) ;
    |}.

  Next Obligation.
  Proof.
    cbn in *.
    split.
    - category.
      reflexivity.
    - category.
      reflexivity.
  Qed.
  Next Obligation.
  Proof.
    cbn in *.
    split.
    - category.
      reflexivity.
    - category.
      reflexivity.
  Qed.

  Next Obligation.
  Proof.
    cbn in *.
    split.
    - rewrite H0.
      rewrite H.
      reflexivity.
    - rewrite H0.
      rewrite H1.
      reflexivity.
  Qed.


  (* Funct (Space C/c) (C/c) *)
  #[program]
   Definition pullback {C: Category} {c: C}: Funct (Prod (C/c) (C/c)) (Space C)
    := Functors.curry (@pullback' C c).
  
  #[program]
   Definition exp [C:Category] (F G: Space C): Space C := {|
    op (x: C ᵒᵖ) :=
            ((∀ y, (C y x * F y) ~> G y)
               /~
               {| equiv x y := ∀ t, x t == y t |}
                  ): Bishop ;
    map _ _ (x: C _ _) k _ tp := k _ (x ∘ fst tp, snd tp) ;
  |}.

  Next Obligation.
  Proof.
    admit.
  Admitted.

  Next Obligation.
  Proof.
    intros tp0 tp1 p.
    apply (proj2_sig (k o1)).
    destruct tp0, tp1.
    cbn in *.
    destruct p as [p q].
    split.
    - rewrite p.
      reflexivity.
    - rewrite q.
      reflexivity.
  Qed.

  Next Obligation.
  Proof.
    intros ? ? p ? t.
    destruct t.
    cbn in *.
    apply p.
  Qed.

  Next Obligation.
  Proof.
    apply (proj2_sig (t0 t1)).
    split.
    all: cbn in *.
    2: reflexivity.
    rewrite compose_assoc.
    reflexivity.
  Qed.

  Next Obligation.
  Proof.
    apply (proj2_sig (t0 t1)).
    all: cbn in *.
    rewrite compose_id_left.
    split.
    all: reflexivity.
  Qed.

  Next Obligation.
  Proof.
    apply (proj2_sig (t0 t1)).
    cbn in *.
    split.
    2: reflexivity.
    rewrite H.
    reflexivity.
  Qed.


  (* (Space C)/P ~ Space (El P)/P *)
  #[program]
   Definition dep_prod [C:Category] (P: Space C) (F G: Space C/P): Space (El P) :=
    @exp (El P)
         (lub ({|
              op (elm: (El P) ᵒᵖ) :=
                  let '(some_intro a p) := elm in
                  s F a: Bishop ;
              map A B (f: El P B A):= map (s F) _ ;
            |}: Space (El P)),
          _)
         (lub ({|
              op (elm: (El P) ᵒᵖ) :=
                  let '(some_intro a p) := elm in
                  s G a: Bishop ;
              map A B (f: (El P) B A) := map (s G) _
            |}: Space (El P)),
          _).

  Next Obligation.
  Proof.
    eexists.
    Unshelve.
    2: {
      eexists.
      Unshelve.
      2: {
        intro x.
        apply (proj1_sig P (val x)).
  Admitted.

  Next Obligation.
  Proof.
    admit.
  Admitted.

  Next Obligation.
  Proof.
    
  Admitted.
    de
    Check El _ (limit (λ x: C ᵒᵖ, ) ).
    Check (F (lub c, id _) ~> G (lub c, id _)).
  (* exp F G. *)

  Import Bishops.


#[program]
   Definition prod [C: Category] (A B: Space C): Space C :=
    limit (λ (x: C ᵒᵖ), proj1_sig A x * proj1_sig B x: Bishop) (λ _ _ x y, (map A x (fst y), map B x (snd y))).

  Next Obligation.
  Proof.
    intros ? ? p.
    cbn.
    destruct x0, y, p.
    cbn in *.
    rewrite H, H0.
    split.
    all: reflexivity.
  Qed.

  Next Obligation.
  Proof.
    exists.
    all: cbn in *.
    - intros ? ? ? ? ? t.
      destruct t.
      split.
      + cbn.
        apply (proj2_sig A).
      + cbn.
        apply (proj2_sig B).
    - intros ? t.
      destruct t.
      split.
      + apply (proj2_sig A).
      + apply (proj2_sig B).
    - intros.
      split.
      + apply (proj2_sig A).
        assumption.
      + apply (proj2_sig B).
        assumption.
  Qed.

  #[program]
   Definition uncurry [K:Category] [A B C: Space K]
   (f: prod A B ~> C): A ~> exp B C :=
    λ _ x _ y, f _ (map A (fst y) x, snd y).

  Next Obligation.
  Proof.
    intros L R p.
    destruct L, R, p.
    apply (proj2_sig (f o0)).
    cbn in *.
    split.
    2: auto.
    admit.
  Admitted.

  Next Obligation.
  Proof.
    intros ? ? p ? y.
    all: cbn in *.
    apply (proj2_sig (f t)).
    cbn.
    split.
    2: reflexivity.
    apply (proj2_sig (map (proj1_sig A) (Datatypes.fst y))).
    assumption.
  Qed.

  (* #[program] *)
  (* Definition fst [C] [A B: Space C]: prod A B ~> A := λ _, fst. *)

  (* #[program] *)
  (* Definition snd [C] [A B: Space C]: prod A B ~> B := λ _, snd. *)

  #[program]
   Definition eval [C:Category] [A B: Space C]: prod (exp A B) A ~> B :=
    λ _ '(f, x), f _ (id, x).

  Next Obligation.
  Proof.
    intros x y p.
    destruct x, y, p as [p q].
    cbn in *.
    rewrite (p _).
    apply (proj2_sig (t1 o)).
    cbn.
    split.
    1: reflexivity.
    assumption.
  Qed.

  Next Obligation.
  Proof.
    intros x y p.
    destruct x, y, p as [p q].
    cbn in *.
    apply (proj2_sig (g o1)).
    cbn.
    split.
    2: assumption.
    rewrite p.
    reflexivity.
  Qed.

  Next Obligation.
  Proof.
    intros x y p ? xs.
    destruct xs.
    cbn in *.
    apply p.
  Qed.

  Next Obligation.
  Proof.
    exists.
    all: cbn in *.
    - intros.
      apply (proj2_sig (t x0)).
      split.
      2: reflexivity.
      1: cbn.
      1: apply compose_assoc.
    - intros.
      apply (proj2_sig (t x)).
      split.
      2: reflexivity.
      cbn.
      rewrite compose_id_left.
      reflexivity.
    - intros ? ? ? ? ? ? ? xs.
      destruct xs.
      cbn in *.
      apply (proj2_sig (t x)).
      cbn.
      split.
      2: reflexivity.
      rewrite H.
      reflexivity.
  Qed.

  #[program]
   Definition local_exp [C: Category] [c: Space C] (F G: Space C/c): Space C/c :=
    lub (local_exp' F G), λ _ f, _.

  Next Obligation.
    apply G.
    apply f.
    refine (id, _).
  Check local_exp.
  limit
      (λ x: C ᵒᵖ, local_exp )
      (λ A B (f: C _ _) g _ xs, _).
  Next Obligation.

  Next Obligation.
  Proof.
    intros x y p.
    destruct x, y, p.
    cbn in *.
    apply (proj2_sig (g o)).
    cbn.
    split.
    2: assumption.
    rewrite H.
    reflexivity.
  Qed.

  Next Obligation.
  Proof.
    intros ? ? p ? xs.
    cbn in *.
    destruct xs.
    cbn in *.
    apply p.
  Qed.

  Next Obligation.
  Proof.
    exists.
    all: cbn in *.
    - intros ? ? ? ? ? ? ? xs.
      destruct xs.
      cbn in *.
      apply (proj2_sig (t x0)).
      cbn.
      split.
      2: reflexivity.
      apply compose_assoc.
    - intros ? ? ? xs.
      destruct xs.
      cbn in *.
      apply (proj2_sig (t x)).
      cbn.
      split.
      2: reflexivity.
      apply compose_id_left.
    - intros ? ? ? ? p ? ? xs.
      destruct xs.
      cbn in *.
      apply (proj2_sig (t x)).
      cbn.
      split.
      2: reflexivity.
      rewrite p.
      reflexivity.
  Qed.

  #[program]
   Definition local_exp [C: Category] [c: Space C] (F G: Space C/c): Space C/c :=
    lub (local_exp' F G), λ _ x, _.

  Next Obligation.
  Proof.
    apply G.
    apply x.
    refine (id, _).
    
    
  #[program]
   Definition DepProd [C: Category] [X Y: Space C] (f: X ~> Y): Funct (Space C/X) (Space C/Y) :=
    limit
      (λ (S:Space C/X),
       (lub (limit
               (λ pt: C ᵒᵖ,
                      (∀ x: Y ~> X, (id == f ∘ x) → proj1_sig (Yo C) pt ~> s S)
                        /~ {| equiv x y := ∀ t u, x t u == y t u |}
                : Bishop)
               (λ _ _ x _,_)),
       _):Space C/Y)
      (λ _ _ x _ y, _).

  Next Obligation.
  Proof.
    admit.
  Admitted.

  Next Obligation.
  Proof.
    cbn in *.
  Next Obligation.
  Proof.
    intros x y p.
    destruct p as [p q].
    destruct x as [x ex], y as [y ey].
    cbn in *.
    rewrite <- (ey _ _).
    rewrite <- (ex _ _).
    apply (proj2_sig (f o)).
    rewrite (p _ _).
    reflexivity.
  Qed.

  Next Obligation.
  Proof.
    eexists
  Variant dep_prod [C: Category] [X Y: Space C] (f: X ~> Y) (S: Space C) (t: C ᵒᵖ) :=
    dp
      (y: ∀ Z, Z ~> Y)
      (F: prod (proj1_sig (Yo C) t) (fiber f y) ~> S).

  Arguments dp [C X Y f S t].

  #[program]
  Definition dep_prod' [C: Category] [X Y: Space C] (f: X ~> Y) (S: Space C) (t: C ᵒᵖ): Bishop :=
    dep_prod f S t
             /~ {| equiv '(dp x xf) '(dp y yf) :=
                     (∀ t, x t == y t)
                     ∧ (∀ t u p q, xf t (u, p) == yf t (u, q)) |}.

  Next Obligation.
  Proof.
    admit.
  Admitted.

  #[program]
  Definition dep_prod'' [C: Category] [X Y: Space C] (f: X ~> Y) (S: Space C): Space C :=
    limit
      (dep_prod' f S)
      (λ A B (x: C B A) '(dp y yf),
       dp (λ _ _ p, _)
          (λ _ fib, _)).

  Next Obligation.
  Proof.
    intros ? ? p.
    rewrite p.
    reflexivity.
  Qed.

  Next Obligation.
  Proof.
    apply (H _).
    refine (_ ∘ p).
    
    (* (* refine (fib ∘ _). *) *)
    (* cbn in *. *)
    refine (yf _ _ _ (x ∘ fib)).
    Unshelve.
    2: {
      intros.
      refine (H _ ∘ _).
    2: {
      refine (x ∘ fib).
    admit.
  Admitted.

  Next Obligation.
  Proof.
    apply (x ∘ fib).
  Defined.

  Next Obligation.
  Proof.
    admit.
  Admitted.

  Next Obligation.
  Proof.
    admit.
  Admitted.

  Next Obligation.
  Proof.
    admit.
  Admitted.

  #[program]
   Definition DepProd [C: Category] [X Y: Space C] (f: X ~> Y): Funct (Space C/X) (Space C/Y) :=
    limit
      (λ (S:Space C/X), (lub (dep_prod'' f (s S)), λ _ '(dp y _), y _ id):Space C/Y)
      (λ _ _ x _ '(dp y yf), dp y (λ p x _, _)).

  Next Obligation.
  Proof.
    intros x y.
    destruct x, y.
    intro p.
    cbn in *.
    destruct p as [p q].
    apply p.
  Qed.

  Next Obligation.
  Proof.
    apply (yf _ _ H2).
    intros ? ? p.
    apply (proj2_sig (x t)).
    apply (proj2_sig (yf t)).
    apply p.
  Qed.

  Next Obligation.
  Proof.
    intros A B p.
    destruct A, B.
    cbn in *.
    split.
    - intros.
      apply p.
    - intros.
      apply (proj2_sig (x t)).
      apply p.
  Qed.

  Next Obligation.
  Proof.
    destruct t.
    reflexivity.
  Qed.

  Next Obligation.
  Proof.
    admit.
  Admitted.



  Section w.
    Context [K: Category].
    Variable A: Space K.
    Variable C: Space K.
    Variable B: C ~> A.

    Definition fiber [D] (y: D ~> A) :=
      ∃ x, y == B ∘ x.

   Inductive w (c: Space K): Type := {
      s: c ~> A ;
      π: fiber s → w c ;
    }.

    Arguments s [c].
    Arguments π [c].

    Fixpoint weq [c] (l r: w c): Prop :=
      ∃ (p: s l == s r),
      ∀ x y, weq (π l x) (π r y).


    #[program]
    Fixpoint wmap [A B] (x : K B A) (y: w (proj1_sig (Yo K) A)): w (proj1_sig (Yo K) B) :=
      {|
      s _ f := _ ;
      (* π _ := π y _ *)
      |}.

    Next Obligation.
    Proof.
      Check (map (proj1_sig (s y))).
            (* (x ∘ f). *)
    (*   destruct B as [sB πB], πB as [B' e]. *)
    (*   cbn in *. *)
    (*   Check (e _ _ _ H0). *)
    (*   eexists (H ∘ _). *)
      
    (*   Unshelve. *)
    (*   1: symmetry. *)
    (*   1: rewrite compose_assoc. *)
    (*   1: rewrite <- H0. *)
    (*   apply compose_compat. *)
    (*   2: reflexivity. *)
      
    (*   Check (proj2_sig f _ (s y)). *)

  #[program]
   Definition W: Space K :=
    limit (λ (x: K ᵒᵖ), w (proj1_sig (Yo K) x) /~ {| equiv := @weq _ |}: Bishop) (λ _ _ x y, _).

  Next Obligation.
  Proof.
    admit.
  Admitted.

  Next Obligation.
    cbn in *.
    eexists.
    Unshelve.
    2: {
      cbn in *.
      intr
  End w.

  Next Obligation.
  Proof.

    
  Module PresheafNotations.
    (* Notation "!" := Bang. *)
    (* Notation "·" := Terminal. *)

    (* Notation "∅" := Initial. *)

    (* Infix "+" := Sum. *)
    (* (* Notation "[ A ; B ]" := (Fanin A B). *) *)
    (* Notation "'i₁'" := Inl. *)
    (* Notation "'i₂'" := Inr. *)

    Infix "*" := prod.
    (* Notation "⟨ A , B ⟩" := (Fanout A B). *)
    (* Notation "'π₁'" := fst. *)
    (* Notation "'π₂'" := snd. *)
  End PresheafNotations.
End Presheaf.

End Arrow.

Module Import Discrete.
  Import Groupoid.

  Class Discrete := {
    G: Groupoid ;
    thin [x y] (f g: G x y): f == g ;
  }.

  Coercion G: Discrete >-> Groupoid.
  Existing Instance G.
End Discrete.


Module Profunctor.
  #[universes(cumulative)]
  Record prefunctor (C D: Category) := limit {
    P: D → C → Set ;
    lmap [A B: D] [X: C]: D A B → P B X → P A X ;
    rmap [A B: C] [X: D]: C A B → P X A → P X B ;
  }.

  Arguments limit [C D].
  Arguments P [C D].
  Arguments lmap [C D] p [A B] [X].
  Arguments rmap [C D] p [A B] [X].

  #[universes(cumulative)]
  Class profunctor [C D: Category] (F: prefunctor C D): Prop := {
    lmap_composes [X Y Z W] (x: D Y Z) (y: D X Y)
                  (t: P F _ W): lmap F y (lmap F x t) = lmap F (x ∘ y) t ;
    lmap_id [X Y] (t: P F X Y): lmap F id t = t ;

    rmap_composes [X Y Z W] (x: C Y Z) (y: C X Y)
                  (t: P F W _): rmap F x (rmap F y t) = rmap F (x ∘ y) t ;
    rmap_id [X Y] (t: P F X Y): rmap F id t = t ;
  }.

  #[local]
  Definition prof K L := {p: prefunctor K L | profunctor p }.

  #[program]
  Definition Prof (K L: Category): Category := {|
    Obj := prof K L ;
    Mor A B := (∀ x y, P A x y → P B x y) /~ {| equiv f g := ∀ x y t, f x y t = g x y t |} ;

    id _ _ _ x := x ;
    compose _ _ _ f g x y t := f x y (g x y t) ;
  |}.

  Next Obligation.
  Proof.
    exists.
    all: unfold Reflexive, Symmetric, Transitive; cbn.
    - intros.
      reflexivity.
    - intros ? ? p x y t.
      symmetry.
      apply (p x y t).
    - intros ? ? ? p q x y t.
      rewrite (p x y t), (q x y t).
      reflexivity.
  Qed.

  Next Obligation.
  Proof.
    rewrite (H _ _ _).
    rewrite (H0 _ _ _).
    reflexivity.
  Qed.

  Module Export ProfNotations.
    Coercion P: prefunctor >-> Funclass.

    #[local]
     Definition proj1_prof [K L]: prof K L → prefunctor K L := @proj1_sig _ _.
    Coercion proj1_prof:prof >-> prefunctor.

    #[local]
    Definition proj2_prof [K L] (f: prof K L): profunctor f := proj2_sig f.
    Coercion proj2_prof:prof >-> profunctor.
    Existing Instance proj2_prof.
  End ProfNotations.
End Profunctor.


Module MonCircle.
  Import Mon.
  Import Presheaf.

  Definition Circle_Spec: Space Mon := proj1_sig (Yo Mon) S¹₊.
  Definition Circle: Quantity Mon := proj1_sig (CoYo Mon) S¹₊.

   #[program]
   Definition twist: Circle ~> Circle := λ _ k n, k (n · n).

   Next Obligation.
   Proof.
     cbn in *.
     intros ? ? p.
     rewrite p.
     reflexivity.
   Qed.

   Next Obligation.
   Proof.
     exists.
     - rewrite (@map_unit _ _ _ H).
       rewrite <- Monoid.app_unit_right.
       reflexivity.
     - intros.
       repeat rewrite <- (@map_app _ _ _ H).
       cbn in *.
       destruct k.
       cbn in *.
       apply b.
       cbn.
       lia.
   Qed.

   Next Obligation.
   Proof.
     intros ? ? p ?.
     cbn in *.
     rewrite (p _).
     reflexivity.
   Qed.
End MonCircle.

Module GrpCircle.
  Import Grp.

  Open Scope Z.

  Definition Circle_Spec: Space Grp := proj1_sig (Yo Grp) S¹.

  Definition Circle: Quantity Grp := proj1_sig (CoYo Grp) S¹.

    #[program]
   Definition twist: Circle ~> Circle := λ _ k n, k (n · n).

   Next Obligation.
   Proof.
     cbn in *.
     intros ? ? p.
     rewrite p.
     reflexivity.
   Qed.

   Next Obligation.
   Proof.
     exists.
     - rewrite (@map_unit _ _ _ H).
       reflexivity.
     - intros.
       repeat rewrite <- (@map_app _ _ _ H).
       cbn in *.
       destruct k.
       cbn in *.
       apply b.
       cbn.
       lia.
     - intros.
       reflexivity.
   Qed.

   Next Obligation.
   Proof.
     intros ? ? p ?.
     cbn in *.
     rewrite (p _).
     reflexivity.
   Qed.

   #[program]
    Definition negate: Circle ~> Circle := λ _ k n, k (Group.invert n).

   Next Obligation.
   Proof.
     intros ? ? p.
     rewrite p.
     reflexivity.
   Qed.

   Next Obligation.
   Proof.
     exists.
     - rewrite (@map_unit _ _ _ H).
       reflexivity.
     - intros.
       repeat rewrite <- (@map_app _ _ _ H).
       cbn in *.
       destruct k.
       cbn in *.
       apply b.
       cbn.
       lia.
     - intros.
       reflexivity.
   Qed.

   Next Obligation.
   Proof.
     intros ? ? p ?.
     cbn in *.
     rewrite (p _).
     reflexivity.
   Qed.
End GrpCircle.

Definition Arr := Funct I₊.
Definition Endos := Funct (𝑩₊ S¹₊).
Definition Cylinder := Product.Prod I₊.

Definition Iso := Funct Interval.
Definition Autos := Funct (𝑩 S¹).
Definition Cylinder' := Product.Prod Interval.



Module Import Under.
  #[universes(cumulative)]
   Record cobundle [C: Category] (s: C) := infima { t: C ; i: C s t ; }.

  Arguments t [C] [s] _.
  Arguments i [C] [s] _.

  Section under.
    Variables (C: Category) (s: C).

    #[program]
    Definition Under: Category := {|
      Obj := cobundle s ;
      Mor A B := {f: t A ~> t B | i B == f ∘ i A } /~ {| equiv f g := (f :>) == (g :>) |} ;

      id A := @id _ (t A) ;
      compose A B C := @compose _ (t A) (t B) (t C) ;
    |}.

    Next Obligation.
    Proof.
      exists.
      all: unfold Reflexive, Symmetric, Transitive.
      - reflexivity.
      - symmetry.
        assumption.
      - intros ? ? ? p q.
        rewrite p, q.
        reflexivity.
    Qed.

    Next Obligation.
    Proof.
      rewrite <- compose_assoc.
      rewrite H0, H.
      reflexivity.
    Qed.

    Next Obligation.
    Proof.
      rewrite H, H0.
      reflexivity.
    Qed.
  End under.

  Module Export UnderNotations.
    Notation "'glb' A , P" := {| t := A ; i := P |}.
    Infix "\" := Under.
  End UnderNotations.
End Under.

Definition PointedSet := Bishop\Bishops.True.


Module Bicategory.
  Import Product.

  Class Bicategory := {
    Obj: Type ;
    Mor: Obj → Obj → Category ;

    id {A}: Mor A A ;
    compose {A B C}: Funct (Prod (Mor B C) (Mor A B)) (Mor A C) where
    "A ∘ B" := (proj1_sig compose (A, B)) ;

    compose_id_left [A B] (F: Mor A B): (id ∘ F) <~> F ;
    compose_id_right [A B] (F: Mor A B): F ∘ id <~> F ;

    compose_assoc [A B C D] (f: Mor C D) (g: Mor B C) (h: Mor A B):
      f ∘ (g ∘ h) <~> (f ∘ g) ∘ h;
  }.

  Module Export BicategoryNotations.
    Coercion Obj: Bicategory >-> Sortclass.
    Coercion Mor: Bicategory >-> Funclass.
  End BicategoryNotations.
End Bicategory.

Import Bicategory.BicategoryNotations.



(* (* Like a generalized bundle *) *)
(* Record hFiber [A B: Category] (f: Funct A B) (c: B) := { *)
(*   s: A ; *)
(*   π: c ~> proj1_sig f s; *)
(* }. *)

(* Definition Boolean := Decidable (simple bool) bool_dec. *)
(* #[program] *)
(* Definition cospan (A B: Preset) := hFiber (limit (λ (x: Boolean), if x then A else B) (λ _ _ x, _)). *)

(* Next Obligation. *)
(*   destruct H, H0. *)
(*   all: cbn in *. *)
(*   all: try contradiction. *)
(*   - apply X. *)
(*   - apply X. *)
(* Defined. *)

(* Next Obligation. *)
(*   exists. *)
(*   all: cbn in *. *)
(*   all: unfold cospan_obligation_1 in *. *)
(*   all: cbn in *. *)
(*   - intros. *)
(*     destruct X, Y, Z. *)
(*     all: try contradiction. *)
(*     all: reflexivity. *)
(*   - intros. *)
(*     destruct A0. *)
(*     all: reflexivity. *)
(*   - intros. *)
(*     destruct A0, B0. *)
(*     all: try contradiction. *)
(*     all: reflexivity. *)
(* Qed. *)

(* Check cospan. *)
(* Definition bar: cospan nat bool nat. *)
(*   exists true. *)
(*   cbn. *)

Module Bundle.
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
  Import Bundle.

  Definition axiom C := span C C.
  Definition axiom_scheme C := bundle (axiom C).
  Definition theory C := bundle (axiom_scheme C).

  Section syntactic.
    Context {K: Bishop} {th: theory K}.

    (* Some kind of pushout (basically cograph) out of the discrete category and a bunch of operations *)
    Inductive syn {K} {th: theory K}: K → K → Type :=
    | syn_id {A}: syn A A
    | syn_compose {A B C}: syn B C → syn A B → syn A C

    | syn_axiom rule args C D:
        (∀ ix, syn C (π1 (th rule args) ix)) →
        (∀ ix, syn (π2 (th rule args) ix) D) →
        syn C D
    .
  End syntactic.

  #[program]
   Definition Syn [K] (th: theory K): Category := {|
    Obj := K ;

    (* FIXME figure out equality *)
    Mor A B := @syn K th A B /~ {| equiv _ _ := True |} ;

    id := @syn_id _ _ ;
    compose := @syn_compose _ _ ;
   |}.

  Next Obligation.
  Proof.
    exists.
    all: exists.
  Qed.
End Logic.

Module SanityCheck.
  Import Bundle.

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
  | taut
  | absurd
  | inl | inr | fanin
  | fst | snd | fanout.

  Definition propositional `(Propositional): theory P := sup ix,
    match ix with
    | taut => sup A,
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
    Context `{H:Propositional}.

    Definition Free := Syn (propositional H).

    Definition prop_axiom := @syn_axiom _ (propositional H).
    Definition taut' C: Free C true := prop_axiom taut C C true (λ _, syn_id) (λ _, syn_id).
    Definition absurd' C: Free false C := prop_axiom absurd C false C (λ _, syn_id) (λ _, syn_id).

    Definition fst' A B: Free (A ∧ B) A := prop_axiom fst (A, B) (A ∧ B) A (λ _, syn_id) (λ _, syn_id).
    Definition snd' A B: Free (A ∧ B) B := prop_axiom snd (A, B) (A ∧ B) B (λ _, syn_id) (λ _, syn_id).

    Definition fanout' C A B (f: Free C A) (g: Free C B)
      := prop_axiom fanout (A, B) C (A ∧ B)
                    (λ ix, if ix as IX return (syn C (if IX then A else B)) then f else g)
                    (λ _, syn_id).
  End sanity.
End SanityCheck.


Module CatArrow.
  Close Scope nat.

  Record arrow := arr {
    source: Category ;
    target: Category ;
    proj: Funct source target ;
  }.

  Arguments arr [source target].

  Record arrow1 (A B: arrow) := arr1 {
    source1: Funct (source A) (source B) ;
    target1: Funct (target A) (target B) ;
    proj1 x: proj B (source1 x) ~> target1 (proj A x) ;
  }.

  Arguments arr1 [A B].
  Arguments source1 [A B].
  Arguments target1 [A B].
  Arguments proj1 [A B].

  Record arrow2 [F G: arrow] (A B: arrow1 F G) := arr2 {
    source2: source1 A ~> source1 B ;
    target2: target1 A ~> target1 B ;
  }.

  Arguments arr2 [F G A B].
  Arguments source2 [F G A B].
  Arguments target2 [F G A B].
  (* Arguments proj2 [F G A B]. *)

  #[program]
  Definition Arrow (F G: arrow): Category := {|
    object := arrow1 F G ;
    mor A B := arrow2 A B /~ {| equiv x y := source2 x == source2 y ∧ target2 x == target2 y |} ;
    id _ := arr2 id id ;
    compose _ _ _ f g := arr2 (source2 f ∘ source2 g) (target2 f ∘ target2 g) ;
  |}.

  Next Obligation.
  Proof.
    exists.
    - split.
      all: reflexivity.
    - intros ? ? p.
      destruct p.
      split.
      all: symmetry.
      all: auto.
    - intros ? ? ? p q.
      destruct p as [p p'], q as [q q'].
      split.
      + intro.
        rewrite (p _), (q _).
        reflexivity.
      + intro.
        rewrite (p' _), (q' _).
        reflexivity.
  Qed.

  Next Obligation.
  Proof.
    split.
    all: cbn in *.
    all: intro; apply compose_assoc.
  Qed.

  Next Obligation.
  Proof.
    split.
    all: cbn in *.
    all: intro; apply compose_id_left.
  Qed.

  Next Obligation.
  Proof.
    split.
    all: cbn in *.
    all: intro; apply compose_id_right.
  Qed.

  Next Obligation.
  Proof.
    split.
    all: cbn in *.
    - intro.
      rewrite (H _), (H0 _).
      reflexivity.
    - intro.
      rewrite (H1 _), (H2 _).
      reflexivity.
  Qed.

  Definition Pullback [A B C] (F: Functor A C) (G: Functor B C) := Arrow (arr F) (arr G).
  Definition Pushout [A B C] (F: Functor C A) (G: Functor C B) := Arrow (arr F) (arr G).
End CatArrow.


Module Import Pullback.
  #[universes(cumulative)]
  Record pullback [A B C: Category] (F: Functor A C) (G: Functor B C) := {
    source: A ;
    target: B ;
    assoc: F source ~> G target ;
  }.

  Arguments assoc [A B C F G] _.
  Arguments source {A B C F G} _.
  Arguments target {A B C F G} _.

  (* Basically a comma category *)
  #[universes(cumulative)]
  Record comma [A B C] (F: Functor A C) (G: Functor B C) (X Y: pullback F G) := {
    source_mor: source X ~> source Y ;
    target_mor: target X ~> target Y ;
    commutes: map G target_mor ∘ assoc X == assoc Y ∘ map F source_mor ;
  }.

  Arguments source_mor [A B C F G X Y] _.
  Arguments target_mor [A B C F G X Y] _.
  Arguments commutes [A B C F G X Y] _.

  #[program]
    Definition Pullback [A B C] (F: Functor A C) (G: Functor B C): Category := {|
    object := pullback F G ;
    mor A B := comma F G A B /~
                     {|
                       equiv x y :=
                         source_mor x == source_mor y ∧ target_mor x == target_mor y |} ;

    id _ := {| source_mor := id ; target_mor := id |} ;
    compose _ _ _ f g :=
      {|
        source_mor := source_mor f ∘ source_mor g ;
        target_mor := target_mor f ∘ target_mor g ;
      |} ;
  |}.

  Next Obligation.
  Proof.
    exists.
    all:split.
    all:try reflexivity.
    1,2: symmetry; destruct H; auto.
    1,2: destruct H, H0.
    1: rewrite H, H0.
    2: rewrite H1, H2.
    all: reflexivity.
  Qed.

  Next Obligation.
  Proof.
    repeat rewrite map_id.
    category.
    reflexivity.
  Qed.

  Next Obligation.
  Proof.
    cbn in *.
    repeat rewrite <- map_composes.
    rewrite <- compose_assoc.
    rewrite commutes.
    rewrite compose_assoc.
    rewrite commutes.
    rewrite <- compose_assoc.
    reflexivity.
  Qed.

  Next Obligation.
  Proof.
    split.
    all: apply compose_compat.
    all: auto.
  Qed.

  #[program]
  Definition p1 {A B C} (F: Functor A C) (G: Functor B C): Functor (Pullback F G) A := {|
    fobj := source ;
    map _ _ := @source_mor _ _ _ _ _ _ _ ;
  |}.

  #[program]
  Definition p2 {A B C} (F: Functor A C) (G: Functor B C): Functor (Pullback F G) B := {|
    fobj := target ;
    map _ _ := @target_mor _ _ _ _ _ _ _ ;
  |}.
End Pullback.



Module DiscreteCartesian.
  Import Cartesian.
  Import CartesianNotations.
  Import Monoid.
  Class Discrete := {
    Discrete_Category: Cartesian ;
    thin: IsThin Discrete_Category ;
    invert A B: Discrete_Category A B → Discrete_Category B A ;
  }.

  Coercion Discrete_Category: Discrete >-> Cartesian.
End DiscreteCartesian.

Module MonoidalPresheaf.
  Import Cartesian.
  Import CartesianNotations.
  Import DiscreteCartesian.

  Record diagram C := {
    dom: Discrete ;
    proj: Monoidal dom C ;
  }.

  Arguments dom [C].
  Arguments proj [C].

  (* By grothendieck style of thing you should obtain a functor sort of like
     DiscreteFibration C ~ [C^op, Mon]
 *)
  Module Export OverNotations.
    Notation "'lim' A , P" := {| dom := A ; proj := P |}.
  End OverNotations.

  Record fib [C:Cartesian] (A B: diagram C) := {
    slice: dom A → dom B ;
    commutes x: C (proj A x) (proj B (slice x)) ;
  }.

  Arguments slice [C A B].
  Arguments commutes [C A B].

  #[program]
  Definition Presheaf (C: Cartesian): Category := {|
    object := diagram C ;
    mor A B := fib A B /~ {| equiv f g := ∀ t, slice f t = slice g t |} ;

    id _ := {| slice x := x ; commutes _ := id |} ;
    compose _ _ _ f g := {| slice x := slice f (slice g x) ; commutes x := commutes f (slice g x) ∘ commutes g x |} ;
  |}.

  Next Obligation.
  Proof.
    exists.
    - intro.
      reflexivity.
    - intros ? ? ? ?.
      symmetry.
      auto.
    - intros ? ? ? p q t.
      rewrite (p t), (q t).
      reflexivity.
  Qed.

  Next Obligation.
  Proof.
    rewrite (H _).
    rewrite (H0 _).
    reflexivity.
  Qed.

End MonoidalPresheaf.


Module Import Presheaf.
  Import TruncateNotations.
  Import Discrete.

  (* Use discrete fibrations to represent presheaves *)

  Record diagram (C:Category) := {
    dom: Discrete ;
    proj: Functor dom C ;
  }.

  Arguments dom [C].
  Arguments proj [C].

  Module Export OverNotations.
    Notation "'lim' A , P" := {| dom := A ; proj := P |}.
  End OverNotations.

  Record fib [C:Category] (A B: diagram C) := {
    slice: dom A → dom B ;
    commutes x: C (proj A x) (proj B (slice x)) ;
  }.

  Arguments slice [C A B].
  Arguments commutes [C A B].

  #[program]
  Definition Presheaf (C: Category): Category := {|
    object := diagram C ;
    mor A B := fib A B /~ {| equiv f g := ∀ t, slice f t = slice g t |} ;

    id _ := {| slice x := x ; commutes _ := id |} ;
    compose _ _ _ f g := {| slice x := slice f (slice g x) ; commutes x := commutes f (slice g x) ∘ commutes g x |} ;
  |}.

  Next Obligation.
  Proof.
    exists.
    - intro.
      reflexivity.
    - intros ? ? ? ?.
      symmetry.
      auto.
    - intros ? ? ? p q t.
      rewrite (p t), (q t).
      reflexivity.
  Qed.

  Next Obligation.
  Proof.
    rewrite (H _).
    rewrite (H0 _).
    reflexivity.
  Qed.

  Record pullback [K] (C D: Presheaf K) := {
    source: dom C ;
    target: dom D ;
    assoc: proj C source ~> proj D target ;
  }.

  Arguments source [K C D].
  Arguments target [K C D].
  Arguments assoc [K C D].

  #[program]
   Definition Yo {C}: Functor C (Presheaf C) := {|
    fobj A := lim {| Discrete_Category := Trivial |}, {| fobj _ := A ; map _ _ _ := id |} ;
    map A B f := {| slice _ := I ; commutes _ := f |} ;
  |}.

  Next Obligation.
  Proof.
    destruct t.
    reflexivity.
  Qed.

  (* Definition Terminal {C}: Presheaf C := lim C, {| fobj x := x  |}. *)
  (* Next Obligation. *)
  (* Definition Bang {C} {A: Presheaf C}: Presheaf C A Terminal := {| slice := proj A ; commutes _ := id |}. *)

  #[local]
  Set Program Mode.

  Definition Initial {C}: Presheaf C := lim {| Discrete_Category := Empty |}, {| fobj x := match x with end |}.

  Next Obligation.
  Proof.
    intros x.
    destruct x.
  Qed.
  Solve All Obligations with cbn; contradiction.

  Definition Absurd {C} {A: Presheaf C}: Presheaf C Initial A := {| slice t := match t with end ; commutes t := match t with end  |}.


  Definition Sum {K} (A B: Presheaf K): Presheaf K :=
    lim (dom A + dom B)%type,
    λ x, match x with
         | inl a => proj A a
         | inr b => proj B b
         end .

  Definition Fanin {K} {A: Presheaf K}: Sum A A ~> A :=
    {| slice x := match x with
                  | inl x' => x'
                  | inr x' => x'
                  end |}.

  Next Obligation.
    destruct x.
    all: apply id.
  Defined.

  Definition Inl {K} {A B: Presheaf K}: A ~> Sum A B := {| slice := inl ; commutes _ := id |}.
  Definition Inr {K} {A B: Presheaf K}: B ~> Sum A B := {| slice := inr ; commutes _ := id |}.

  Definition Prod [K] (A B: Presheaf K): Presheaf K :=
    lim (pullback A B), λ x, proj A (source x).

  Definition Dup {K} {A: Presheaf K}: A ~> Prod A A :=
    {| slice x := {| source := x ; target := x ; assoc := id |} ; commutes _ := id |}.
  Definition Fst {C} {A B: Presheaf C}: Prod A B ~> A :=
    {| slice xy := source (xy :>) ; commutes _ := id  |}.
  Definition Snd {C} {A B: Presheaf C}: Prod A B ~> B :=
    {| slice xy := target (xy :>) ; commutes x := assoc x |}.

  Module ToposNotations.
    Notation "!" := Bang.
    Notation "·" := Terminal.

    Notation "∅" := Initial.

    Infix "+" := Sum.
    (* Notation "[ A ; B ]" := (Fanin A B). *)
    Notation "'i₁'" := Inl.
    Notation "'i₂'" := Inr.

    Infix "×" := Prod.
    (* Notation "⟨ A , B ⟩" := (Fanout A B). *)
    Notation "'π₁'" := Fst.
    Notation "'π₂'" := Snd.
  End ToposNotations.
End Presheaf.


Module Sum.
  Unset Program Mode.
  #[local]
   Definition sum [C D: Category] (A B: C + D): Bishop :=
    match (A, B) with
    | (inl A', inl B') => A' ~> B'
    | (inr A', inr B') => A' ~> B'
    | _ => Bishops.False
    end.
  Set Program Mode.

  #[local]
   Definition comp [K L: Category] [A B C: K + L]: sum B C → sum A B → sum A C.
  Proof.
    destruct B as [B|B].
    - destruct C as [C|C].
      2: contradiction.
      destruct A as [A|A].
      2: contradiction.
      apply compose.
    - destruct C as [C|C].
      1: contradiction.
      destruct A as [A|A].
      1: contradiction.
      apply compose.
  Defined.

  Definition Sum (K L: Category): Category := {|
    object := K + L ;
    mor := @sum K L ;

    id A :=
      match A with
      | inl _ => id
      | inr _ => id
      end ;
    compose := @comp K L ;
  |}.

  Next Obligation.
  Proof.
    destruct A, B, C, D.
    all: try contradiction.
    all: cbn.
    all: category.
    all: reflexivity.
  Qed.

  Next Obligation.
  Proof.
    destruct A, B.
    all: try contradiction.
    all: cbn.
    all: category.
    all: reflexivity.
  Qed.

  Next Obligation.
  Proof.
    destruct A, B.
    all: try contradiction.
    all: cbn.
    all: category.
    all: reflexivity.
  Qed.

  Next Obligation.
  Proof.
    destruct A, B, C.
    all: try contradiction.
    all: cbn.
    all: rewrite H, H0.
    all: reflexivity.
  Qed.

  Definition fanin {C A B} (f: Functor A C) (g: Functor B C): Functor (Sum A B) C :=
    {|
    fobj x :=
      match x with
      | inl a => f a
      | inr b => g b
      end ;
    |}.

  Obligation 1.
  destruct A0, B0.
  all: try contradiction.
  - apply (map f X).
  - apply (map g X).
  Defined.

  Next Obligation.
  Proof.
    destruct X, Y, Z.
    all: try contradiction.
    all: cbn in *.
    all: apply map_composes.
  Qed.

  Next Obligation.
  Proof.
    destruct A0.
    all: apply map_id.
  Qed.

  Next Obligation.
  Proof.
    destruct A0, B0.
    all: try contradiction.
    all: cbn.
    all: rewrite H.
    all: reflexivity.
  Qed.
End Sum.


(* Sanity check, the free cocompletion of the point should be like Set *)
(* Module Set'. *)
(*   Import ToposNotations. *)

(*   Definition Set' := Presheaf Trivial. *)

(*   Definition Pure (D: Category): Set' := lim D, Const (I:Trivial). *)
(* End Set'. *)


Module Group.
  Import Circle.Undirected.
  Import ToposNotations.

  Definition Group := Presheaf Circle.
  Definition Terminal: Group := ·.
  Definition bang A: Group A Terminal := !.

  Definition S1: Group := Yo (I: Circle).
  Definition Loop (n: Z): S1 ~> S1 := map Yo (n: Circle I I).
End Group.

Module Monoid.
  Import Circle.Directed.
  Import ToposNotations.

  Definition Monoid := Presheaf Circle.

  Definition S1: Monoid := Yo (I: Circle).
  Definition Loop (n: nat): S1 ~> S1 := map Yo (n: Circle I I).

  Definition Torus := S1 × S1.

  Definition Initial: Monoid := ∅.
  Definition Terminal: Monoid := ·.

  Definition Product (A B: Monoid): Monoid := A × B.
  Definition Fanout {C A B: Monoid} (f: C ~> A) (g: C ~> B): C ~> A × B := ⟨ f , g ⟩.
  Definition Fst {A B}: Product A B ~> A := π₁.
  Definition Snd {A B}: Product A B ~> B := π₂.

  Compute Loop 5.
End Monoid.


Module Import Hom.
   Definition Hom S: Functor S (Functor (op S) Bishop) := {|
    fobj A := {|
               fobj B := S B A ;
               map _ _ f g := g ∘ f ;
             |} ;
    map _ _ f _ g := f ∘ g ;
  |}.

  Next Obligation.
  Proof.
    rewrite H.
    reflexivity.
  Qed.

  Next Obligation.
  Proof.
    rewrite H.
    reflexivity.
  Qed.

  Next Obligation.
  Proof.
    rewrite H.
    reflexivity.
  Qed.

  Next Obligation.
  Proof.
    rewrite H.
    reflexivity.
  Qed.
End Hom.



Module Proset.
  #[universes(cumulative)]
  Class proset := {
    type: Type ;
    preorder: relation type ;
    Proset_PreOrder: PreOrder preorder ;
  }.

  Arguments type: clear implicits.
  Existing Instance Proset_PreOrder.

  Instance Proset_Setoid (C: proset): Setoid (type C) := {
    equiv x y := preorder x y ∧ preorder y x ;
  }.

  Obligation 1.
  Proof.
    admit.
  Admitted.

  Definition to_bishop (p: proset): Bishop := type p /~ Proset_Setoid _.

  Module Import ProsetNotations.
    Coercion type: proset >-> Sortclass.
    Infix "<:" := preorder.
  End ProsetNotations.

  Definition Proset: Category := {|
    object := proset ;
    mor A B :=
      {op: Preset A B | ∀ x y, x <: y → op x <: op y}
       /~ {| equiv x y := ∀ t, x t == y t |} ;
    id A := @id Preset _ ;
    compose A B C := @compose Preset _ _ _ ;
  |}.

  Obligation 1.
  Proof.
    admit.
  Admitted.


  Obligation 4.
  Proof.
    split.
    all: reflexivity.
  Qed.

  Obligation 5.
  Proof.
    split.
    all: reflexivity.
  Qed.

  Obligation 6.
  Proof.
    split.
    all: reflexivity.
  Qed.

  Obligation 7.
  Proof.
    admit.
  Admitted.
End Proset.


Module Import Option.
  #[local]
   Close Scope nat.

  Section option.
    Variable K: Category.

    #[local]
     Definition True_set := True /~ {| equiv _ _ := True |}.

    Obligation 1.
    Proof.
      exists.
      all: exists.
    Qed.

    #[local]
     Definition False_set := False /~ {| equiv x := match x with end |}.

    Obligation 1.
    Proof.
      exists.
      all: intro; contradiction.
    Qed.

    Unset Program Mode.
    #[local]
     Definition mor (A B: option K) :=
      match (A, B) with
      | (Some A', Some B') => A' ~> B'
      | (None, None) => True_set
      | _ => False_set
      end.
    Set Program Mode.

    #[local]
    Definition id {A: option K}: mor A A :=
      match A with
      | Some A' => @id K A'
      | None => I
      end.

    #[local]
     Definition compose [A B C: option K]: mor B C → mor A B → mor A C.
    destruct B.
    - destruct A.
      all: cbn in *.
      all: try contradiction.
      destruct C.
      all: try contradiction.
      apply compose.
    - destruct A.
      all: cbn in *.
      all: try contradiction.
      destruct C.
      all: try contradiction.
      exists.
    Defined.

    Instance Option: Category := {
      object := option K ;
      mor := mor ;
      id := @id ;
      compose := @compose ;
    }.

    Obligation 1.
    Proof.
      destruct A, B, C, D.
      all: try contradiction.
      all: cbn in *.
      - apply compose_assoc.
      - exists.
    Qed.

    Obligation 2.
    Proof.
      destruct A, B.
      all: try contradiction.
      all: cbn in *.
      - apply compose_id_left.
      - exists.
    Qed.

    Obligation 3.
    Proof.
      destruct A, B.
      all: try contradiction.
      all: cbn in *.
      - apply compose_id_right.
      - exists.
    Qed.

    Obligation 4.
    Proof.
      destruct A, B, C.
      all: try contradiction.
      all: cbn in *.
      - rewrite H, H0.
        reflexivity.
      - exists.
    Qed.
  End option.
End Option.


Module FreeForgetAdjoint.
  Import Proset.
  Import ProsetNotations.

  Import Free.

  Definition counit (A: Category): Cat A (Free (Forget A)) := {|
    fobj x := x ;
    map _ _ f := truncate_intro f ;
  |}.

  Definition unit (A: Proset): Forget (Free A) ~> A := λ x, x.

  Obligation 1.
  Proof.
    destruct H as [H'].
    apply H'.
  Qed.

  Definition push [A: Proset] {B: Category} (a: A): Functor B (Product.Product (Free A) B) := {|
    fobj x := (a, x) ;
    map _ _ f := (reflexivity a, f) ;
  |}.

  Obligation 1.
  Proof.
    split.
    - exists.
    - reflexivity.
  Qed.

  Obligation 2.
  Proof.
    split.
    - exists.
    - reflexivity.
  Qed.

  Definition pop [A: Proset] {B C: Category}
    (f: A ~> Forget (Functor B C)):
    Functor (Free A) (Functor B C) := {|
    fobj xy := f xy ;
  |}.

  Obligation 1.
  admit.
  Admitted.

  Obligation 2.
  admit.
  Admitted.

  Obligation 3.
  admit.
  Admitted.

  Obligation 4.
  admit.
  Admitted.
End FreeForgetAdjoint.

Module Import Span.
  Import TruncateNotations.

   #[local]
   Definition mor A B := (Cat/Product.Product A B) /~ {| equiv x y := |Isomorphism (Cat/_) x y| |}.

  Obligation 1.
  Proof.
    exists.
    - intro.
      exists.
      apply (Category.id: Isomorphism _ _ _).
    - intros ? ? ?.
      destruct H.
      exists.
      apply (X ⁻¹).
    - intros ? ? ? p q.
      destruct p as [p], q as [q].
      exists.
      apply ((q: Isomorphism _ _ _) ∘ p).
  Qed.

  #[local]
   Definition id {A}: mor A A := lim A, Product.dup.

  #[local]
   Definition compose [A B C] (f: mor B C) (g: mor A B): mor A C :=
    lim (Pullback (Product.snd ∘ proj g) (Product.fst ∘ proj f)),
      Product.fanout
        (Product.fst ∘ proj g ∘ Product.fst)
        (Product.snd ∘ proj f ∘ Product.snd) ∘
        Pullback.forget (Product.snd ∘ proj g) (Product.fst ∘ proj f).

  Instance Span: Category := {
    object := Cat ;
    mor := mor ;
    id := @id ;
    compose := @compose ;
  }.

  Obligation 1.
  Proof.
    admit.
  Admitted.

  Obligation 2.
  Proof.
    admit.
  Admitted.

  Obligation 3.
  Proof.
    admit.
  Admitted.

  Obligation 4.
  Proof.
    admit.
  Admitted.

  Definition transpose [X Y: Span] (f: X ~> Y): Y ~> X := lim (dom f), Product.swap ∘ proj f.

  Definition trace [X] (f: Span X X): Category := Pullback (Product.snd ∘ proj f) (Product.fst ∘ proj f).

  Definition trace_forget [X] (f: Span X X): Functor (trace f) (Product.Product (dom f) (dom f)) := forget (Product.snd ∘ proj f) (Product.fst ∘ proj f).
End Span.


(* Define the simplex category *)
Module Import Simplex.
  Import FiniteNotations.

  Instance Δ: Category := {
    object := nat ;
    mor A B := Cat [A] [B] ;
    id _ := id ;
    compose _ _ _ := @compose _ _ _ _ ;
  }.

  Obligation 1.
  Proof.
    exists.
    apply (id (Category := Isomorphism _)).
  Qed.

  Obligation 2.
  Proof.
    exists.
    apply (id (Category := Isomorphism _)).
  Qed.

  Obligation 3.
  Proof.
    exists.
    apply (id (Category := Isomorphism _)).
  Qed.

  Obligation 4.
  Proof.
    destruct (H0 x) as [p].
    destruct (H (g x)) as [q].
    exists.
    eapply (compose (Category := Isomorphism _) _ q).
    Unshelve.
    admit.
  Admitted.

  Definition forget A B: Δ A B := const ((lim B, id): [B]).

  Instance Δ_Directed: Category := Monomorphism Δ.

  Module Import SimplexNotations.
    Notation "'Δ₊'" := Δ_Directed.
  End SimplexNotations.
End Simplex.
Import SimplexNotations.


Module Import Chain.
  Section chain.
    Variable X: Category.

    (* Every abelian group can be thought of as an action on the circle *)

    Definition complex := Functor (op Δ) X.
    Definition d (n: nat) (V: complex): V (1 + n) ~> V n :=
      @map _ _ V (1 + n) n {|
             fobj x := lim (dom x), le_S _ _ (proj x) ;
             map _ _ f := f ;
           |}.

    Definition zero n (V: complex) := d n V ∘ d (1 + n) V.

  End chain.
End Chain.

Definition InftyCat := Fiber.Fiber Δ.

Definition pure (c: Category): InftyCat := lim c, {| fobj _ := 0 ; map _ _ _ := id |}.

Obligation 1.
Proof.
  exists.
  apply (id: Isomorphism _ _ _).
Qed.

Obligation 2.
Proof.
  exists.
  apply (id: Isomorphism _ _ _).
Qed.

Obligation 3.
Proof.
  exists.
  apply (id: Isomorphism _ _ _).
Qed.

Definition InftyYo: Functor Δ InftyCat := Fiber.Yo Δ.


Definition True_set := True /~ {| equiv _ _ := True |}.

Obligation 1.
Proof.
  exists.
  all: exists.
Qed.


Definition Simplicial C := Fiber.Fiber (Product.Product Δ₊ C).

Definition mappo [C:Category] (F: Functor Δ₊ C): Simplicial C := lim Δ₊, {|
                                       fobj n := (n, F n) ;
                                       map _ _ f := (f, map F f) ;
                                       |}.

Obligation 1.
Proof.
  cbn in *.
  split.
  - intros.
    exists.
    apply (id: Isomorphism _ _ _).
  - rewrite map_composes.
    reflexivity.
Qed.

Obligation 2.
Proof.
  split.
  - intros.
    exists.
    apply (id: Isomorphism _ _ _).
  - rewrite map_id.
    reflexivity.
Qed.

Obligation 3.
Proof.
  cbn in *.
  split.
  - intro x.
    destruct (H x) as [H'].
    exists.
    apply H'.
  - apply map_compat.
    cbn.
    assumption.
Qed.



Module Import Subobject.
  Instance Subobject C c: Category := Monomorphism C/c.
End Subobject.


Definition Presheaf K: Category := Functor (op K) Bishop.

Module Import Presheaf.
  Section limits.
    Context {C D: Category}.
    Variable F: Functor (op D) C.

    Definition limit' (c: C): Bishop := (∀ t, c ~> F t) /~ {| equiv x y := ∀ t, x t == y t |}.

    Obligation 1.
    Proof.
      exists.
      all: unfold Reflexive, Symmetric, Transitive; cbn.
      - intros.
        reflexivity.
      - intros.
        symmetry.
        auto.
      - intros.
        rewrite (H _), (H0 _).
        reflexivity.
    Qed.

    Definition limit_map {X Y: op C} (f: X ~> Y): limit' X ~> limit' Y := λ x t, x t ∘ f.

    Obligation 1.
    Proof.
      unfold Basics.flip in *.
      rewrite (H _).
      reflexivity.
    Qed.

    Definition limit: Presheaf C := {| fobj := limit' ; map := @limit_map |}.

    Obligation 1.
    Proof.
      symmetry.
      apply compose_assoc.
    Qed.

    Obligation 2.
    Proof.
      apply compose_id_right.
    Qed.

    Obligation 3.
    Proof.
      unfold Basics.flip in *.
      rewrite H.
      reflexivity.
    Qed.
  End limits.
End Presheaf.

(* Module Import Interval. *)
(*   #[local] *)
(*    Definition mor (A B: Prop): Bishop := (A → B) /~ {| equiv _ _ := True |}. *)

(*   Obligation 1. *)
(*   Proof. *)
(*     exists. *)
(*     all: exists. *)
(*   Qed. *)


(*   #[local] *)
(*    Definition id {A: Prop}: mor A A := λ x, x. *)

(*   #[local] *)
(*    Definition compose [A B C: Prop] (f: mor B C) (g: mor A B): mor A C := *)
(*     λ x, f (g x). *)

(*   Instance Interval: Category := { *)
(*     object := Prop ; *)
(*     mor := mor ; *)

(*     id := @id ; *)
(*     compose := @compose ; *)
(*   }. *)
(* End Interval. *)

(* Instance Interval: Category := { *)
(*   object := bool ; *)
(*   mor _ _ := True /~ {| equiv _ _ := True |} ; *)

(*   id _ := I ; *)
(*   compose _ _ _ _ _ := I ; *)
(* }. *)

(* Obligation 1. *)
(* Proof. *)
(*   exists. *)
(*   all:exists. *)
(* Qed. *)


Definition Arr C := Functor Interval C.
Definition Endo C := Functor Circle.Directed.Circle C.

Definition Iso C := Functor Interval C.
Definition Auto C := Functor Circle C.

Definition Cylinder C := Product.Product C Interval.


Instance ArrowSet: Category := Presheaf (op Interval).

Import TruncateNotations.
Definition truncate: Functor (op Preset) (op Interval) := {|
  fobj xy := | xy | ;
|}.

Obligation 1.
Proof.
  destruct H.
  exists.
  apply X.
  apply X0.
Defined.

Definition truncate_limit: ArrowSet := limit truncate.
Definition source := truncate_limit False.
Definition target := truncate_limit True.

Definition to: Interval False True := λ x, match x with end.
Definition to': source ~> target := map truncate_limit to.

Definition x: target.
  cbn.
  intros.
  unfold Basics.flip in *.
  exists.
Defined.


Module Diagrams.
  Section diagrams.
    Context {C:Category}.

    Definition Empty: (op Empty:Cat) ~> C := {|
      fobj A := match A with end ;
      map A := match A with end
    |}.

    Solve All Obligations with contradiction.

    Definition Constant {D} (c: C): (op D:Cat) ~> C := {|
      fobj _ := c ;
      map _ _ _ := id ;
    |}.

    Obligation 1.
    Proof.
      apply compose_id_left.
    Qed.

    Solve Obligations with reflexivity.
  End diagrams.
End Diagrams.

