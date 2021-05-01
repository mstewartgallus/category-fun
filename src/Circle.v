(* Seems to make classes go faster? *)
Set Primitive Projections.
Unset Printing Primitive Projection Parameters.

Set Universe Polymorphism.
Set Program Mode.

Require Import Coq.Unicode.Utf8.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import Psatz.

Reserved Notation "A /~ B" (at level 40).

Reserved Notation "A ~> B" (at level 80).
Reserved Notation "A ∘ B" (at level 30).

Reserved Notation "A <~> B" (at level 80).
Reserved Notation "F 'ᵀ'" (at level 1).

Reserved Notation "F ! X" (at level 1).

Module Import Bishop.
  (* We need Bishop sets (AKA Setoids) not Coq's Type to make the Yoneda
     embedding on presheafs work properly.

     The technical jargon is that a Bishop Set is a 0-trivial groupoid,
     equality is the hom. *)
  #[universes(cumulative)]
  Class Bishop := {
    type: Type ;
    Bishop_Setoid:> Setoid type ;
  }.

  Module Export BishopNotations.
    Coercion type: Bishop >-> Sortclass.
    Notation "A /~ B" := {| type := A ; Bishop_Setoid := B |}.
  End BishopNotations.

  Definition fn (A B: Bishop) :=
    { op: @type A → @type B | ∀ x y, x == y → op x == op y } /~ {| equiv x y := ∀ t, x t == y t |}.

  Obligation 1.
  Proof.
    exists.
    all: unfold Reflexive, Symmetric, Transitive.
    - intros.
      reflexivity.
    - intros.
      symmetry.
      auto.
    - intros ? ? ? p q t.
      rewrite (p t), (q t).
      reflexivity.
  Qed.

  Add Parametric Morphism {A B} (f: fn A B) : (proj1_sig f)
      with signature equiv ==> equiv as fn_mor.
  Proof.
    intros.
    destruct f.
    cbn.
    auto.
  Qed.
End Bishop.

Module Import Category.
  #[universes(cumulative)]
  Class Category := {
    object: Type ;
    hom: object → object → Bishop
    where "A ~> B" := (hom A B) ;

    id {A}: hom A A ;
    compose {A B C}: hom B C -> hom A B -> hom A C
    where "f ∘ g" := (compose f g) ;

    compose_assoc {A B C D} (f: hom C D) (g: hom B C) (h: hom A B):
      (f ∘ (g ∘ h)) == ((f ∘ g) ∘ h );
    compose_id_left {A B} (f: hom A B): (id ∘ f) == f ;
    compose_id_right {A B} (f: hom A B): (f ∘ id) == f ;

    compose_compat {A B C} (f f': hom B C) (g g': hom A B):
      f == f' → g == g' → f ∘ g == f' ∘ g' ;
  }.

  Add Parametric Morphism (K: Category) (A B C: @object K) : (@compose _ A B C)
      with signature equiv ==> equiv ==> equiv as compose_mor.
  Proof.
    intros ? ? p ? ? q.
    apply compose_compat.
    apply p.
    apply q.
  Qed.

  Module Export CategoryNotations.
    Coercion object: Category >-> Sortclass.
    Coercion hom: Category >-> Funclass.

    Notation "f ∘ g" := (compose f g).
    Notation "A ~> B" := (hom A B).
  End CategoryNotations.
End Category.

Module Import Sets.
  Instance Bishop: Category := {|
    object := Bishop ;
    hom := fn ;
    id _ x := x ;
    compose _ _ _ f g x := f (g x) ;
  |}.

  Obligation 3.
  Proof.
    reflexivity.
  Qed.

  Obligation 6.
  Proof.
    rewrite (H _).
    apply (H3 _).
    rewrite (H0 _).
    reflexivity.
  Qed.

  Solve All Obligations with cbn; reflexivity.
End Sets.

Module Import Isomorphism.
  Section isos.
    Context `(K:Category).

    Section iso.
      Variable A B: K.

      #[universes(cumulative)]
      Record iso := {
        to: K A B ;
        from: K B A ;
        to_from: to ∘ from == id ;
        from_to: from ∘ to == id ;
      }.

      #[local]
      Definition hom := iso /~ {| equiv f g := to f == to g ∧ from f == from g |}.

      Obligation 1.
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
          destruct p as [p1 p2].
          destruct q as [q1 q2].
          split.
          + rewrite p1, q1.
            reflexivity.
          + rewrite p2, q2.
            reflexivity.
      Qed.
    End iso.

    Instance Isomorphism: Category := {
      object := object ;
      hom := hom ;
      id _ :=  {| to := id ; from := id |} ;
      compose _ _ _ f g :=
        {|
          to := to _ _ f ∘ to _ _ g ;
          from := from _ _ g ∘ from _ _ f
        |} ;
    }.

    Obligation 1.
    Proof.
      apply compose_id_left.
    Qed.

    Obligation 2.
    Proof.
      apply compose_id_right.
    Qed.

    Obligation 3.
    Proof.
      rewrite <- compose_assoc.
      rewrite -> (compose_assoc (to _ _ g)).
      rewrite to_from.
      rewrite compose_id_left.
      rewrite to_from.
      reflexivity.
    Qed.

    Obligation 4.
    Proof.
      rewrite <- compose_assoc.
      rewrite -> (compose_assoc (from _ _ f)).
      rewrite from_to.
      rewrite compose_id_left.
      rewrite from_to.
      reflexivity.
    Qed.

    Obligation 5.
    Proof.
      split.
      2: symmetry.
      all: apply compose_assoc.
    Qed.

    Obligation 6.
    Proof.
      split.
      + apply compose_id_left.
      + apply compose_id_right.
    Qed.

    Obligation 7.
    Proof.
      split.
      + apply compose_id_right.
      + apply compose_id_left.
    Qed.

    Obligation 8.
    Proof.
      split.
      + apply compose_compat.
        all:assumption.
      + apply compose_compat.
        all:assumption.
    Qed.
  End isos.

  Definition transpose {C:Category} {A B: C} (f: Isomorphism _ A B): Isomorphism _ B A :=
    {| to := from _ _ _ f ; from := to _ _ _ f |}.

  Obligation 1.
  Proof.
    apply from_to.
  Qed.

  Obligation 2.
  Proof.
    apply to_from.
  Qed.

  Module Export IsomorphismNotations.
    Notation "A 'ᵀ'" := (transpose A).
    Notation "A <~> B" := (Isomorphism _ A B).
  End IsomorphismNotations.
End Isomorphism.

Module Circle.
  #[local]
   Close Scope nat.

  (* Annoyingly a slightly byzantine definition is required to get some
  sort of induction *)
  Inductive circle := zero | compose (_ _ :circle) | clockwise | counterclockwise.

  Section inductive.
     Variables (S:Category) (pt:S) (loop: pt <~> pt).

     #[local]
      Fixpoint foldme (c: circle): S pt pt :=
       match c with
       | zero => id
       | compose f g => foldme f ∘ foldme g
       | clockwise => to _ _ _ loop
       | counterclockwise => from _ _ _ loop
       end.
  End inductive.

  (* Probably a simpler equality story *)
  #[local]
   Definition hom (A B: True): Bishop := circle /~
                     {| equiv x y := ∀ s base loop, foldme s base loop x == foldme s base loop y |}.

  Obligation 1.
  Proof.
    exists.
    all:intro;intros.
    - reflexivity.
    - symmetry.
      auto.
    - rewrite (H s _), (H0 s _).
      reflexivity.
  Qed.

  Instance Circle: Category := {
    object := True ;
    hom := hom ;

    id _ := zero ;
    compose _ _ _ := compose ;
  }.

  Obligation 1.
  Proof.
    apply compose_assoc.
  Qed.

  Obligation 2.
  Proof.
    apply compose_id_left.
  Qed.

  Obligation 3.
  Proof.
    apply compose_id_right.
  Qed.

  Obligation 4.
  Proof.
    rewrite (H s), (H0 s).
    reflexivity.
  Qed.

  Definition base: Circle := I.

  Definition loop: base <~> base := {|
    to := clockwise ;
    from := counterclockwise ;
  |}.

  Obligation 1.
  Proof.
    apply to_from.
  Qed.

  Obligation 2.
  Proof.
    apply from_to.
  Qed.

  Definition Circle_ind (c: Circle base base) (S : Category) (pt: S) (loop: pt <~> pt): pt ~> pt :=
    foldme S pt loop c.
End Circle.

Module Integers.
  Import Circle.

  Definition zero: base ~> base := id.
  Definition one: base ~> base := to _ _ _ loop.
  Definition neg_one: base ~> base := from _ _ _ loop.

  Instance Z: Category := {
    object := unit ;
    hom _ _ := (nat * nat) /~ {| equiv x y := fst x + snd y = fst y + snd x |} ;
    id _ := (0, 0) ;
    compose _ _ _ f g := (fst f + fst g, snd f + snd g) ;
  }.

  Obligation 1.
  Proof.
    exists.
    all:intro;intros;lia.
  Qed.

  Obligation 2.
  Proof.
    lia.
  Qed.

  Obligation 5.
  Proof.
    lia.
  Qed.

  Fixpoint neg (n: nat): base ~> base :=
    match n with
    | 0 => id
    | S n => neg_one ∘ neg n
    end.

  Fixpoint pos (n: nat): base ~> base :=
    match n with
    | 0 => id
    | S n => one ∘ pos n
    end.

  Definition to_circle (mn: (tt:Z) ~> tt): base ~> base := pos (fst mn) ∘ neg (snd mn).
  Definition from_circle (f: base ~> base): (tt:Z) ~> tt :=
    Circle_ind f Z tt {|
        Isomorphism.to := (1, 0) ;
        Isomorphism.from := (0, 1) ;
        to_from := eq_refl;
        from_to := eq_refl |}.

  Theorem from_to x: from_circle (to_circle x) == x.
  Proof.
    destruct x as [m n].
    induction m.
    - induction n.
      + reflexivity.
      + cbn in *.
        lia.
    - induction n.
      + cbn in *.
        lia.
      + cbn in *.
        lia.
  Qed.

  Theorem to_from x: to_circle (from_circle x) == x.
  Proof.
    induction x.
    - cbn.
      intros.
      apply compose_id_left.
    - intros s base loop.
      replace (Circle.foldme s base loop (compose x1 x2)) with (Circle.foldme s base loop x1 ∘ Circle.foldme s base loop x2).
      2: reflexivity.
      rewrite <- (IHx1 s base loop).
      rewrite <- (IHx2 s base loop).
      admit.
  Admitted.
End Integers.
