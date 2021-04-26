(* Seems to make classes go faster? *)
Set Primitive Projections.
Unset Printing Primitive Projection Parameters.

Require Import Coq.Unicode.Utf8.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Reserved Notation "| A |" (at level 40).

Reserved Notation "A /~ B" (at level 40).

Reserved Notation "A ~> B" (at level 80).
Reserved Notation "A ∘ B" (at level 30).

Reserved Notation "A <~> B" (at level 80).
Reserved Notation "F 'ᵀ'" (at level 1).

Reserved Notation "F ! X" (at level 1).

Reserved Notation "A ⊗ B" (at level 30).
Reserved Notation "A ~~> B" (at level 80).

Set Universe Polymorphism.
Set Program Mode.

(* FIXME get propositional truncation from elsewhere *)
Module Import Utils.
  Definition ident (A: Type) := A.

  Variant truncate A: Prop :=
  | truncate_intro (_: ident A): truncate A.

  Module TruncateNotations.
    Notation "| A |" := (truncate A).
    Coercion truncate_intro: ident >-> truncate.
  End TruncateNotations.
End Utils.

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

  Module Import BishopNotations.
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

  (* FIXME use for stuff *)
  Local Definition prod (A B: Bishop) := (A * B) /~ {| equiv x y := fst x == fst y ∧ snd x == snd y |}.

  Obligation 1.
  exists.
  all:unfold Reflexive, Symmetric, Transitive;cbn.
  all:intros; split.
  all:try reflexivity.
  - symmetry.
    destruct H.
    auto.
  - symmetry.
    destruct H.
    auto.
  - symmetry.
    destruct H, H0.
    rewrite H, H0.
    reflexivity.
  - destruct H, H0.
    rewrite H1, H2.
    reflexivity.
  Qed.
End Bishop.

Import BishopNotations.

(*
Single sorted definition of a Category.

I just used the word Path because using the word category twice is confusing.
*)
Module Path.
  #[universes(cumulative)]
  Class Path := {
    path: Type ;

    s: path -> path ;
    t: path -> path ;

    glue f g: s f = t g -> path ;

    s_s x: s (s x) = s x ;
    t_s x: t (s x) = s x ;
    s_t x: s (t x) = t x ;
    t_t x: t (t x) = t x ;

    s_glue x y p: s (glue x y p) = s y ;
    t_glue x y p: t (glue x y p) = t x ;

    glue_s x p: glue x (s x) p = x;
    glue_t x p: glue (t x) x p = x;

    glue_assoc f g h q p r s:
      glue f (glue g h q) p = glue (glue f g r) h s ;
  }.

  Module Import PathNotations.
    Coercion path: Path >-> Sortclass.

    Notation "f ∘ g" := (glue f g _).
  End PathNotations.
End Path.

Module Deloop.
  Import Path.
  Import PathNotations.

  Section deloop.
    Context `{Path}.

    Definition object := {x | s x = x }.
    Definition hom (x y: object) := {f | s f = x /\ t f = y}.

    Definition id {A}: hom A A := A.

    Obligation 1.
    Proof.
      destruct A.
      cbn.
      split.
      auto.
      rewrite <- e.
      rewrite t_s.
      auto.
    Qed.

    Definition compose {A B C} (f: hom B C) (g: hom A B): hom A C := f ∘ g.

    Obligation 1.
    Proof.
      destruct A, B, C.
      destruct f, g.
      cbn in *.
      destruct a, a0.
      rewrite H3.
      rewrite H0.
      auto.
    Qed.

    Obligation 2.
    Proof.
      rewrite s_glue.
      rewrite t_glue.
      split.
      - destruct g.
        cbn.
        destruct a.
        auto.
      - destruct f.
        cbn.
        destruct a.
        auto.
    Qed.
  End deloop.
End Deloop.

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

  Module Import CategoryNotations.
    Coercion object: Category >-> Sortclass.
    Coercion hom: Category >-> Funclass.

    Notation "f ∘ g" := (compose f g).
    Notation "A ~> B" := (hom A B).
  End CategoryNotations.
End Category.

Import CategoryNotations.

Create HintDb category discriminated.
(* Hint Rewrite compose_id_left: category. *)
(* Hint Rewrite compose_id_right: category. *)

Module Import Sets.
  Instance Bishop: Category := {
    object := Bishop ;
    hom := fn ;
    id _ x := x ;
    compose _ _ _ f g x := f (g x) ;
  }.

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

Import BishopNotations.

Module Bishops.
  Definition True: Bishop := True /~ {| equiv _ _ := True |}.
  Definition False: Bishop := False /~ {| equiv A := match A with end |}.

  Obligation 1 of True.
  Proof.
    exists.
    all:exists.
  Qed.

  Obligation 1 of False.
  Proof.
    exists.
    all:unfold Reflexive, Symmetric, Transitive; cbn.
    all:intros.
    all:contradiction.
  Qed.
End Bishops.

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

  Module Import IsomorphismNotations.
    Notation "A 'ᵀ'" := (transpose A).
    Notation "A <~> B" := (Isomorphism _ A B).
  End IsomorphismNotations.
End Isomorphism.

Import IsomorphismNotations.

Module Import Functor.
  Import TruncateNotations.

  #[universes(cumulative)]
  Class functor (C D: Category) := {
    fobj: C → D ;
    map {A B}: C A B → D (fobj A) (fobj B) ;

    map_composes {X Y Z} (f: C Y Z) (g: C X Y): map f ∘ map g == map (f ∘ g) ;

    map_id {A}: map (@id _ A) == id ;
    map_compat {A B} (f f': C A B): f == f' → map f == map f' ;
  }.

  Module Import FunctorNotations.
    Coercion fobj: functor >-> Funclass.
    Notation "F ! X" := (map (functor := F) X).
  End FunctorNotations.

  Add Parametric Morphism (C D: Category) (A B: C) (F: functor C D) : (@map _ _ F A B)
      with signature equiv ==> equiv as map_mor.
  Proof.
    intros ? ? ?.
    apply map_compat.
    assumption.
  Qed.

  Definition Functor (A B: Category): Bishop :=
    functor A B /~ {| equiv f g := ∀ x, | f x <~> g x | |}.

  Obligation 1.
  Proof.
    exists.
    all: unfold Reflexive, Symmetric, Transitive.
    - intros.
      exists.
      apply (@id (Isomorphism _)).
    - intros ? ? p t.
      destruct (p t) as [p'].
      exists.
      apply (p' ᵀ).
    - intros ? ? ? p q t.
      destruct (p t) as [p'], (q t) as [q'].
      exists.
      apply (@compose (Isomorphism _) _ _ _ q' p').
  Qed.

  #[local]
  Definition to_iso {A B: Category} (f: Functor A B): Functor (Isomorphism A) (Isomorphism B) := {|
    fobj x := f x ;
    map _ _ p :=
      {| to := f ! (to _ _ _ p) ;
         from := f ! (from _ _ _ p) |}
  |}.

  Obligation 1.
  Proof.
    rewrite map_composes.
    rewrite to_from.
    rewrite map_id.
    reflexivity.
  Qed.

  Obligation 2.
  Proof.
    rewrite map_composes.
    rewrite from_to.
    rewrite map_id.
    reflexivity.
  Qed.

  Obligation 3.
  Proof.
    exists.
    all: rewrite map_composes.
    all: reflexivity.
  Qed.

  Obligation 4.
  Proof.
    split.
    all: rewrite map_id.
    all: reflexivity.
  Qed.

  Obligation 5.
  Proof.
    split.
    all:apply map_compat.
    all:assumption.
  Qed.

  Instance Cat: Category := {
    object := Category ;
    hom := Functor ;
    id _ := {| fobj x := x ; map _ _ f := f |} ;
    compose _ _ _ F G := {| fobj x := F (G x) ; map _ _ x := F ! (G ! x) |} ;
  }.

  Solve Obligations with try reflexivity.

  Obligation 4.
  Proof.
    rewrite map_composes, map_composes.
    reflexivity.
  Qed.

  Obligation 5.
  Proof.
    rewrite map_id, map_id.
    reflexivity.
  Qed.

  Obligation 6.
  Proof.
    apply map_compat.
    + apply map_compat.
      * assumption.
  Qed.

  Obligation 7.
  Proof.
    exists.
    apply (@id (Isomorphism _)).
  Qed.

  Obligation 8.
  Proof.
    exists.
    apply (@id (Isomorphism _)).
  Qed.

  Obligation 9.
  Proof.
    exists.
    apply (@id (Isomorphism _)).
  Qed.

  Obligation 10.
  Proof.
    destruct (H0 x) as [q'].
    destruct (H (g' x)) as [p'].
    set (f_iso := to_iso f).
    set (pq := compose (Category := Isomorphism _) p' (f_iso ! q') : f (g x) <~> f' (g' x)).
    exists.
    exists (to _ _ _ pq) (from _ _ _ pq).
    - apply to_from.
    - apply from_to.
  Qed.
End Functor.

Import FunctorNotations.

Module Import NaturalTransformation.
   Section functor.
    Variables K L : Category.

    #[local]
    Definition hom (A B: Functor K L) := (∀ x, L (A x) (B x)) /~ {| equiv f g := ∀ x, f x == g x |}.

    Obligation 1.
    Proof.
    exists.
    all: unfold Reflexive, Symmetric, Transitive, compose, id, hom; cbn.
    - intros.
      reflexivity.
    - intros ? ? p t.
      symmetry.
      apply (p t).
    - intros ? ? ? p q t.
      rewrite (p t), (q t).
      reflexivity.
    Qed.

    Instance NaturalTransformation: Category := {
      object := Functor K L ;
      hom := hom ;
      id _ _ := id ;
      compose _ _ _ f g _ := f _ ∘ g _ ;
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
      apply compose_compat.
      all:auto.
    Qed.
  End functor.
End NaturalTransformation.

Instance Preset: Category := {
  object := Type ;
  hom A B := (A → B) /~ {| equiv f g := ∀ x, f x = g x |} ;
  id _ x := x ;
  compose _ _ _ f g x := f (g x) ;
}.

Obligation 1.
Proof.
  exists.
  all:unfold Reflexive, Symmetric, Transitive;cbn.
  all:auto.
  intros ? ? ? p q ?.
  rewrite (p _), (q _).
  reflexivity.
Qed.

Obligation 5.
Proof.
  rewrite (H _), (H0 _).
  reflexivity.
Qed.

Module Import Over.
  Section over.
    Context `(Category).
    Variable c: object.

    #[universes(cumulative)]
    Record bundle := {
      dom: object ;
      proj: dom ~> c ;
    }.

    Section over.
      Variable A B: bundle.

      #[local]
      Definition hom A B :=
        {f| proj B ∘ f == proj A } /~ {| equiv f g := proj1_sig f == proj1_sig g |}.

      Obligation 1.
      Proof using Type.
        exists.
        all: unfold Reflexive, Symmetric, Transitive.
        - reflexivity.
        - symmetry.
          assumption.
        - intros ? ? ? p q.
          rewrite p, q.
          reflexivity.
      Qed.
    End over.

    Instance Over: Category := {
      object := bundle ;
      hom := hom ;
      id _ := id ;
      compose _ _ _ f g := f ∘ g ;
    }.

    Obligation 1.
    Proof.
      apply compose_id_right.
    Qed.

    Obligation 2.
    Proof.
      rewrite compose_assoc.
      rewrite H1, H0.
      reflexivity.
    Qed.

    Obligation 3.
    Proof.
      apply compose_assoc.
    Qed.

    Obligation 4.
    Proof.
      apply compose_id_left.
    Qed.

    Obligation 5.
    Proof.
      apply compose_id_right.
    Qed.

    Obligation 6.
    Proof.
      rewrite H0, H1.
      reflexivity.
    Qed.
  End over.

  Definition Σ {C:Category} {c} (f: Over C c) (g: Over C (dom _ _ f)): Over C c :=
    {| proj := proj _ _ f ∘ proj _ _ g |}.

  Module OverNotations.
    Notation "C / c" := (Over.Over C c).
  End OverNotations.
End Over.

Import OverNotations.

Instance Empty: Category := {
  object := False ;
  hom A := match A with end ;
  id A := match A with end ;
  compose A := match A with end ;
}.

Solve All Obligations with contradiction.

Instance Trivial: Category := {
  object := True ;
  hom _ _ := Bishops.True ;
  id _ := I ;
  compose _ _ _ _ _ := I ;
}.

Module Import Props.
  Definition ProofIrrelevance (S: Bishop) := ∀ x y: S, x == y.

  #[universes(cumulative)]
  Class MereProp := {
    Prop_Bishop: Bishop ;
    Prop_Irrelevant: ProofIrrelevance Prop_Bishop ;
  }.
End Props.

Module Import Interval.
  Unset Program Mode.

  #[local]
  Definition hom (A B:bool) := match (A, B) with
                         | (true, true) => Bishops.True
                         | (false, false) => Bishops.True
                         | (false, true) => Bishops.True
                         | (_, _) => Bishops.False
                         end.

  #[local]
  Definition id {A}: hom A A.
  destruct A.
    all:cbn.
    all:exists.
  Defined.

  #[local]
  Definition compose {A B C}: hom B C → hom A B → hom A C.
    destruct A, B, C.
    all:cbn.
    all:try contradiction.
    all:exists.
  Defined.

  Program Instance Interval: Category := {
    object := bool ;
    hom := hom ;
    id := @id ;
    compose := @compose ;
  }.

  Obligation 1.
  Proof.
    destruct A, B, C, D.
    all:try contradiction.
    all:exists.
  Qed.

  Obligation 2.
  Proof.
    destruct A, B.
    all:try contradiction.
    all:exists.
  Qed.

  Obligation 3.
  Proof.
    destruct A, B.
    all:try contradiction.
    all:exists.
  Qed.

  Obligation 4.
  Proof.
    destruct A, B, C.
    all:try contradiction.
    all:exists.
  Qed.
End Interval.

Module Coproduct.
  Close Scope nat.

  Section coproducts.
    Variable C D: Category.

    #[local]
    Definition sum := C + D.

    #[local]
    Definition hom' (A B: sum): Type.
    destruct A as [AL|AR], B as [BL|BR].
    1: apply (AL ~> BL).
    3: apply (AR ~> BR).
    all: apply False.
    Defined.

    #[local]
    Definition eq {A B} (f g: hom' A B): Prop.
    destruct A as [AL|AR], B as [BL|BR].
    1: apply (f == g).
    3: apply (f == g).
    all: apply False.
    Defined.

    #[local]
    Definition hom (A B: sum): Bishop := hom' A B /~ {| equiv := eq |}.

    Obligation 1.
    all: destruct A as [AL|AR], B as [BL|BR].
    all: unfold eq.
    all: exists.
    all: unfold Reflexive, Symmetric, Transitive, eq; cbn.
    all: intros; auto.
    all: try reflexivity.
    - symmetry.
      apply H.
    - rewrite H, H0.
      reflexivity.
    - intros.
      symmetry.
      apply H.
    - rewrite H, H0.
      reflexivity.
    Qed.

    Definition coproduct: Category.
    eexists sum hom _ _.
    Unshelve.
    5: {
      intros.
      destruct A.
      all: apply id.
    }
    5: {
      cbn.
      intros X Y Z.
      destruct X, Y, Z.
      all: cbn.
      all: intros f g.
      all: auto.
      all: try contradiction.
      all: apply (f ∘ g).
    }
    all: cbn.
    all: unfold eq;cbn;auto.
    - intros X Y Z W.
      destruct X, Y, Z, W.
      cbn.
      all: auto.
      all: try contradiction.
      all: intros f g h.
      all: apply compose_assoc.
    - intros A B.
      destruct A, B.
      cbn.
      all: auto.
      all: intros.
      all: apply compose_id_left.
    - intros A B.
      destruct A, B.
      all: cbn.
      all: auto.
      all: intros.
      all: apply compose_id_right.
    - intros X Y Z.
      destruct X, Y, Z.
      all: cbn.
      all: auto.
      all: try contradiction.
      + intros ? ? ? ? p q.
        rewrite p, q.
        reflexivity.
      + intros ? ? ? ? p q.
        rewrite p, q.
        reflexivity.
    Defined.
  End coproducts.

  Import Functor.

  Definition fanin {A B C: Cat} (f: A ~> C) (g: B ~> C): (coproduct A B:Cat) ~> C.
  eexists (λ x, match x with | inl x' => f x' | inr x' => g x' end) _.
  Unshelve.
  4: {
    cbn.
    intros X Y.
    destruct X, Y.
    all: cbn.
    all: try contradiction.
    all: apply map.
  }
  all: cbn.
  - intros X Y Z.
    destruct X, Y, Z.
    all: cbn.
    all: try contradiction.
    all: intros; apply map_composes.
  - intros X.
    destruct X.
    all: apply map_id.
  - intros X Y.
    destruct X, Y.
    cbn.
    all: try contradiction.
    all: apply map_compat.
  Defined.

  Definition inl {A B:Cat}: A ~> coproduct A B := {| fobj := inl ; map _ _ x := x |}.
  Definition inr {A B:Cat}: B ~> coproduct A B := {| fobj := inr ; map _ _ x := x |}.

  Solve All Obligations with reflexivity.
End Coproduct.
Module Product.
  Close Scope nat.

  Section products.
    Variable C D: Category.

    Definition hom (A B: C * D): Bishop :=
      prod (fst A ~> fst B) (snd A ~> snd B) /~ {| equiv f g := fst f == fst g ∧ snd f == snd g |}.

    Obligation 1.
    exists.
    all: unfold Reflexive, Symmetric, Transitive; cbn.
    all: intros; auto.
    - split.
      all: reflexivity.
    - destruct H.
      split.
      all: symmetry.
      all: auto.
    - destruct H, H0.
      split.
      + rewrite H, H0.
        reflexivity.
      + rewrite H1, H2.
        reflexivity.
    Qed.

    Instance product: Category := {
      object := C * D ;
      hom := hom ;
      id _ := (id, id) ;
      compose _ _ _ f g := (fst f ∘ fst g, snd f ∘ snd g)
    }.

    Obligation 1.
    Proof.
      split.
      all: apply compose_assoc.
    Qed.

    Obligation 2.
    Proof.
      split.
      all: apply compose_id_left.
    Qed.

    Obligation 3.
    Proof.
      split.
      all: apply compose_id_right.
    Qed.

    Obligation 4.
    split.
    + rewrite H, H0.
      reflexivity.
    + rewrite H1, H2.
      reflexivity.
    Qed.
  End products.

  Definition fst {A B}: (product A B:Cat) ~> A := {|
    fobj := fst ;
    map _ _ := fst
  |}.

  Definition snd {A B}: (product A B:Cat) ~> B := {|
    fobj := snd ;
    map _ _ := snd
  |}.

  Solve All Obligations with reflexivity.

  Definition fanout {A B C: Cat} (f: C ~> A) (g: C ~> B): C ~> (product A B:Cat) := {|
    fobj x := (f x, g x) ;
    map _ _ x := (f ! x, g ! x)
  |}.

  Obligation 1.
  Proof.
    split.
    all: apply map_composes.
  Qed.

  Obligation 2.
  Proof.
    split.
    all: apply map_id.
  Qed.

  Obligation 3.
  Proof.
    split.
    all: rewrite H.
    all: reflexivity.
  Qed.
End Product.

Definition Cylinder K := Product.product K Interval.

 Module Arrow.
  Section arrows.
    Variables K: Category.

    Record arrow := {
      source: K ;
      target: K ;
      proj: source ~> target ;
    }.

    Record arr (A B: arrow) := {
      source_arr: source A ~> source B ;
      target_arr: target A ~> target B ;
      commutes: target_arr ∘ proj A == proj B ∘ source_arr ;
    }.

    #[local]
    Definition hom A B := arr A B /~ {| equiv f g := (target_arr _ _ f == target_arr _ _ g) ∧ (source_arr _ _ f == source_arr _ _ g) |}.

    Obligation 1 of hom.
    exists.
    all:unfold Reflexive, Symmetric, Transitive; cbn.
    - split.
      all:reflexivity.
    - split.
      all: destruct H.
      all: symmetry.
      all: assumption.
    - intros ? ? ? p q.
      destruct p as [p p'], q as [q q'].
      split.
      1: rewrite p, q.
      2: rewrite p', q'.
      all: reflexivity.
    Qed.

    Instance Arrow: Category := {
      object := arrow ;
      hom := hom ;
      id _ := {| source_arr := id ; target_arr := id |} ;
      compose _ _ _ f g := {| target_arr := target_arr _ _ f ∘ target_arr _ _ g ;
                              source_arr := source_arr _ _ f ∘ source_arr _ _ g |} ;
    }.

    Obligation 1.
    Proof.
      rewrite compose_id_left.
      rewrite compose_id_right.
      reflexivity.
    Qed.

    Obligation 2.
    Proof.
      rewrite <- compose_assoc.
      rewrite (commutes _ _ g).
      rewrite compose_assoc.
      rewrite compose_assoc.
      rewrite (commutes _ _ f).
      reflexivity.
    Qed.

    Obligation 3.
    Proof.
      split.
      all: rewrite compose_assoc.
      all: reflexivity.
    Qed.

    Obligation 4.
    Proof.
      split.
      all:rewrite compose_id_left.
      all:reflexivity.
    Qed.

    Obligation 5.
    Proof.
      split.
      all:rewrite compose_id_right.
      all:reflexivity.
    Qed.

    Obligation 6.
    Proof.
      split.
      1: rewrite H, H0.
      2: rewrite H1, H2.
      all:reflexivity.
    Qed.
  End arrows.
End Arrow.

Module Suspension.
  Close Scope nat.
  Import Product.

  Section suspension.
    Variable K: Category.

    #[local]
    Definition hom (A B: Cylinder K) :=
      match (snd A, snd B) with
      | (false, true) => fst A ~> fst B
      | (true, true) => (fst A = fst B) /~ {| equiv _ _ := True |}
      | (false, false) => (fst A = fst B) /~ {| equiv _ _ := True |}
      | _ => Bishops.False
      end.

    Obligation 1.
    Proof.
      exists.
      all:exists.
    Qed.

    Obligation 2.
    Proof.
      exists.
      all:exists.
    Qed.

    Obligation 3.
    Proof.
      destruct b, b0, H, H0.
      all: repeat split.
      all: intro.
      all: discriminate.
    Qed.

    #[local]
    Definition id {A: Cylinder K}: hom A A.
    Proof.
      destruct A as [A I], I.
      all:cbn.
      all:reflexivity.
    Defined.

    #[local]
    Definition compose {A B C}: hom B C -> hom A B -> hom A C.
    Proof.
      intros f g.
      destruct A as [A AI], B as [B BI], C as [C CI].
      destruct AI, BI, CI.
      all: cbn in *.
      all: try contradiction.
      all: try destruct f.
      all: try destruct g.
      all: auto.
    Defined.

    Instance Suspension: Category := {
      object := Cylinder K ;
      hom := hom ;
      id := @id ;
      compose := @compose ;
    }.

    Obligation 1.
    Proof.
      destruct b, b0, b1, b2.
      all: cbn in *.
      all: try apply I.
      all: try contradiction.
      all: try destruct f.
      all: try destruct g.
      all: try destruct h.
      all: reflexivity.
    Qed.

    Obligation 2.
    Proof.
      destruct b, b0.
      all: cbn in *.
      all: try contradiction.
      all: try apply I.
      all: reflexivity.
    Qed.

    Obligation 3.
    Proof.
      destruct b, b0.
      all:cbn in *.
      all: try reflexivity.
      contradiction.
    Qed.

    Obligation 4.
    Proof.
      destruct b, b0, b1.
      all: cbn in *.
      all: try apply I.
      all: try contradiction.
      - destruct f'.
        rewrite <- H0.
        admit.
      - destruct g'.
        admit.
    Admitted.
  End suspension.
End Suspension.

Module Loop.
  Close Scope nat.
  Import Arrow.

  Section loop.
    Variable K: Category.

    (* FIXME use core/isomorphism ? *)
    Record loop := {
      base: K ;
      arr: base ~> base ;
    }.

    (* Not sure is right *)
    #[local]
    Definition hom (A B: loop) := ({| proj := arr A |}:Arrow K) ~> {| proj := arr B |}.

    Instance Loop: Category := {
      object := loop ;
      hom := hom ;
      id _ := id ;
      compose _ _ _ f g := f ∘ g ;
    }.

    Obligation 1.
    Proof.
      cbn.
      split.
      1: rewrite compose_assoc.
      2: rewrite <- compose_assoc.
      all: reflexivity.
    Qed.

    Obligation 2.
    Proof.
      cbn.
      split.
      all: apply compose_id_left.
    Qed.

    Obligation 3.
    Proof.
      cbn.
      split.
      all: apply compose_id_right.
    Qed.

    Obligation 4.
    Proof.
      cbn.
      split.
      all: apply compose_compat.
      all:auto.
    Qed.
  End loop.
End Loop.

Module Import Finite.
 (* Definie finite totally ordered sets *)
  #[local]
  Definition hom (A B: nat) := (A ≤ B) /~ {| equiv _ _ := True |}.

  Obligation 1.
  exists.
  all: exists.
  Qed.

  Local Definition id {A}: hom A A.
  cbn.
  auto.
  Defined.

  #[local]
  Definition compose {A B C}: hom B C → hom A B → hom A C.
  cbn.
  intros f g.
  rewrite g, f.
  reflexivity.
  Defined.

  #[local]
  Instance le: Category := {
    object := nat ;
    hom := hom ;
    id := @id ;
    compose := @compose ;
  }.

  Definition finite (N:nat) := le/N.

  Module Import FiniteNotations.
    (* FIXME Isolate notations *)
    Notation "[ N ]" := (finite N).
  End FiniteNotations.

  #[local]
  Definition any_gt_0 C: 0 ≤ C.
  Proof.
    induction C.
    - auto.
    - auto.
  Qed.

  Definition source C: [C] := {| dom := 0 |}.
  Definition target C: [C] := {| dom := C |}.

  Obligation 1 of source.
  Proof.
    apply any_gt_0.
  Qed.

  Definition walk {C}: source C ~> target C := any_gt_0 C.
End Finite.

Module Import Opposite.
  Section opposite.
    Context `(K:Category).

    Instance op: Category := {
      object := @object K ;
      hom A B := hom B A ;
      id _ := id ;
      compose _ _ _ f g := g ∘ f ;
    }.

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
      apply compose_id_left.
    Qed.

    Obligation 4.
    Proof.
      rewrite H, H0.
      reflexivity.
    Qed.
  End opposite.
End Opposite.

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

    Definition Fn {A B: C} (f: A ~> B): (op Interval:Cat) ~> C.
    eexists.
    Unshelve.
    4: {
      intro x.
      apply (if x then A else B).
    }
    4: {
      cbn.
      intros.
      destruct A0, B0.
      1,4: apply id.
      - apply f.
      - contradiction.
    }
    - intros X Y Z.
      cbn.
      destruct X, Y, Z.
      all:cbn.
      all:intros.
      all:try contradiction.
      + apply compose_id_left.
      + apply compose_id_right.
      + apply compose_id_left.
      + apply compose_id_left.
    - intros X.
      destruct X.
      all: reflexivity.
    - intros X Y.
      destruct X, Y.
      cbn.
      all: try contradiction.
      all: intros.
      all: reflexivity.
    Defined.
  End diagrams.
End Diagrams.

Module Limit.
  Definition weighted {D:Cat} (F G: (op D:Cat) ~> Bishop):Bishop :=
    NaturalTransformation _ _ F G.

  Definition pt {D:Cat}: (op D:Cat) ~> Bishop := Diagrams.Constant Bishops.True.

  Definition limit (D:Cat) (F: (op D:Cat) ~> Bishop) := weighted pt F.
  (* Not sure if it should be point or empty *)
  Definition colimit (D:Cat) (F: (op D:Cat) ~> Bishop) := weighted F pt.

  (* Just an example *)
  Definition unit := limit _ Diagrams.Empty.
  Definition bang {A} : A ~> unit := λ _ x, match x with end.

  Obligation 1.
  Proof.
    contradiction.
  Qed.
End Limit.


Module Monoidal.
  Import Isomorphism.
  Import IsomorphismNotations.

  #[universes(cumulative)]
  Class Monoidal `(Category) := {
    I: object ;
    tensor (_ _: object): object
    where "A ⊗ B" := (tensor A B) ;

    tensor_assoc {A B C}: A ⊗ (B ⊗ C) <~> (A ⊗ B) ⊗ C ;
    tensor_I_left {A}: I ⊗ A <~> A ;
    tensor_I_right {A}: A ⊗ I <~> A ;
  }.

  (* FIXME use some other notation for monoidal tensor *)
  Module MonoidalNotations.
    Infix "⊗" := tensor.
  End MonoidalNotations.
End Monoidal.

Module Enriched.
  Import Monoidal.
  Import MonoidalNotations.
  Import Isomorphism.
  Import IsomorphismNotations.

  #[universes(cumulative)]
  Record Category `(Monoidal) := {
    object: Type ;
    hom: object → object → Category.object
    where "A ~~> B" := (hom A B) ;

    id {A}: I ~> (A ~~> A) ;
    compose {A B C}: (B ~~> C) ⊗ (A ~~> B) ~> (A ~~> C) ;

    (* Not going to do this laws yet *)
  }.

  Module EnrichedNotations.
    Infix "~~>" := hom.
  End EnrichedNotations.
End Enriched.

(* Define the simplex category *)
Module Import Simplex.
  Import FiniteNotations.

  Instance Δ: Category := {
    object := nat ;
    hom A B := ([A]: Cat) ~> [B] ;
    id _ := id ;
    compose _ _ _ f g := f ∘ g ;
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
End Simplex.

Definition presheaf K: Category := NaturalTransformation (op K) Bishop.

Module Presheaf.
  Import Monoidal.
  Import MonoidalNotations.

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
      rewrite (H _).
      reflexivity.
    Qed.

    Definition limit: presheaf C := {| fobj := limit' ; map := @limit_map |}.

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
      rewrite H.
      reflexivity.
    Qed.
  End limits.

  Definition unit {C}: presheaf C := limit Diagrams.Empty.

  Definition bang {C} (A: presheaf C): A ~> unit.
  intro t.
  cbn.
  eexists.
  Unshelve.
  2: {
    intros.
    contradiction.
  }
  cbn.
  intros.
  contradiction.
  Defined.

  Section yoneda.
    Variables C:Category.

    Definition yo (c: C) := limit (Diagrams.Constant c).

    Definition yo_map {A B: C} (f: A ~> B): yo A ~> yo B := λ X g t, f ∘ g t.

    Obligation 1.
    Proof.
      rewrite (H t).
      reflexivity.
    Qed.

    Definition Yo: (C: Cat) ~> presheaf C := {| fobj := yo ; map := @yo_map |}.

    Obligation 1.
    Proof.
      rewrite compose_assoc.
      reflexivity.
    Qed.

    Obligation 2.
    Proof.
      apply compose_id_left.
    Qed.

    Obligation 3.
    Proof.
      rewrite H.
      reflexivity.
    Qed.
  End yoneda.

  (* FIXME define product on presheafs in terms of categorical/set product *)
  Definition product_Monoid C: Monoidal (presheaf C).
  admit.
  Admitted.
End Presheaf.

Definition sSet := presheaf Δ.

Definition InfinityCategory := Enriched.Category sSet (Presheaf.product_Monoid _).
