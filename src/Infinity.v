(* Seems to make classes go faster? *)
Set Primitive Projections.
Unset Printing Primitive Projection Parameters.

Require Import Coq.Unicode.Utf8.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Arith.PeanoNat.

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

Module Import Functor.
  #[universes(cumulative)]
  Class functor (C D: Category) := {
    fobj: C → D ;
    map {A B}: C A B → D (fobj A) (fobj B) ;

    map_composes {X Y Z} (f: C Y Z) (g: C X Y): map f ∘ map g == map (f ∘ g) ;

    map_id {A}: map (@id _ A) == id ;
    map_compat {A B} (f f': C A B): f == f' → map f == map f' ;
  }.

  Module Export FunctorNotations.
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

      #[local]
    Definition hom {K L} (A B: functor K L) := (∀ x, L (A x) (B x)) /~ {| equiv f g := ∀ x, f x == g x |}.

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

    Instance Functor K L: Category := {
      object := functor K L ;
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
End Functor.

Module Import Cat.
  Import TruncateNotations.

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
    hom A B := (Functor A B) /~ {| equiv f g := ∀ x, | f x <~> g x | |};
    id _ := {| fobj x := x ; map _ _ f := f |} ;
    compose _ _ _ F G := {| fobj x := F (G x) ; map _ _ x := F ! (G ! x) |} ;
  }.

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

  Solve Obligations with try reflexivity.

  Obligation 5.
  Proof.
    rewrite map_composes, map_composes.
    reflexivity.
  Qed.

  Obligation 6.
  Proof.
    rewrite map_id, map_id.
    reflexivity.
  Qed.

  Obligation 7.
  Proof.
    apply map_compat.
    + apply map_compat.
      * assumption.
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
    exists.
    apply (@id (Isomorphism _)).
  Qed.

  Obligation 11.
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
End Cat.

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

Module Import Finite.
 (* Define finite totally ordered sets *)
  #[local]
  Definition hom (A B: nat) := (A ≤ B) /~ {| equiv _ _ := True |}.

  Obligation 1.
  Proof.
    exists.
    all: exists.
  Qed.

  #[local]
  Definition id {A}: hom A A := le_n A.

  #[local]
   Definition compose {A B C}: hom B C → hom A B → hom A C.
  Proof.
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

  Module Export FiniteNotations.
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

Module Product.
  #[local]
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

    Instance Product: Category := {
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

  Definition fst {A B}: (Product A B:Cat) ~> A := {|
    fobj := fst ;
    map _ _ := fst
  |}.

  Definition snd {A B}: (Product A B:Cat) ~> B := {|
    fobj := snd ;
    map _ _ := snd
  |}.

  Solve All Obligations with reflexivity.

  Definition fanout {A B C: Cat} (f: C ~> A) (g: C ~> B): C ~> (Product A B:Cat) := {|
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

Instance Empty: Category := {
  object := False ;
  hom A := match A with end ;
  id A := match A with end ;
  compose A := match A with end ;
}.

Solve All Obligations with contradiction.

Instance Trivial: Category := [0].

Instance Interval: Category := {
  object := bool ;
  hom _ _ := True /~ {| equiv _ _ := True |} ;

  id _ := I ;
  compose _ _ _ _ _  := I ;
}.

Obligation 1.
Proof.
  exists.
  all: exists.
Qed.

Instance Cylinder K: Category := Product.Product K Interval.

Instance Boolean: Category := {
  object := bool ;
  hom A B := (A = B) /~ {| equiv _ _ := True |} ;

  id A := eq_refl ;
  compose _ _ _ f g :=
    let eq_refl := f in
    let eq_refl := g in
    eq_refl
}.

Obligation 1.
Proof.
  exists.
  all:exists.
Qed.
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

    Definition Coproduct: Category.
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

  Definition fanin {A B C: Cat} (f: A ~> C) (g: B ~> C): (Coproduct A B:Cat) ~> C.
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

  Definition inl {A B:Cat}: A ~> Coproduct A B := {| fobj := inl ; map _ _ x := x |}.
  Definition inr {A B:Cat}: B ~> Coproduct A B := {| fobj := inr ; map _ _ x := x |}.

  Solve All Obligations with reflexivity.
End Coproduct.

Module Import Coequalizer.
  #[local]
  Close Scope nat.

  Section coeq.
    Variables K L: Category.
    Variables p q: (K:Cat) ~> L.

    #[local]
     Definition hom (A B: L): Bishop :=
      (∀ S (F: Functor L S)
         (shrink: ∀ x, F (p x) <~> F (q x)),
          S (F A) (F B)) /~
    {| equiv x y := ∀ s cyl shrink, x s cyl shrink == y s cyl shrink |}.

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

    Instance Coequalizer: Category := {
      object := L ;
      hom := hom ;

      id _ _ _ _ := id ;
      compose _ _ _ f g s cyl shrink := f s cyl shrink ∘ g s cyl shrink;
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

    Definition cyl: Functor L Coequalizer := {|
      fobj x := x ;
      map _ _ f _ _ _ := map f ;
    |}.

    Obligation 1.
    Proof.
      rewrite map_composes.
      reflexivity.
    Qed.

    Obligation 2.
    Proof.
      rewrite map_id.
      reflexivity.
    Qed.

    Obligation 3.
    Proof.
      cbn in *.
      apply map_compat.
      cbn.
      auto.
    Qed.

    Definition shrink {X: K}: Isomorphism Coequalizer (p X) (q X) := {|
      to s cyl shrink := to _ _ _ (shrink X) ;
      from s cyl shrink := from _ _ _ (shrink X) ;
   |}.

    Obligation 1.
    Proof.
      apply to_from.
    Qed.

    Obligation 2.
    Proof.
      apply from_to.
    Qed.
  End coeq.
End Coequalizer.

Module Import Suspension.
  #[local]
  Close Scope nat.

  Section suspension.
    Variable K: Category.

    #[local]
     Definition hom (A B: Cylinder K): Bishop :=
      (∀ S (cyl: Functor (Cylinder K) S) (shrink: ∀ A B X, cyl (A, X) <~> cyl (B, X)),
          S (cyl A) (cyl B)) /~
    {| equiv x y := ∀ s cyl shrink, x s cyl shrink == y s cyl shrink |}.

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

    Instance Suspension: Category := {
      object := Cylinder K ;
      hom := hom ;

      id _ _ _ _ := id ;
      compose _ _ _ f g s cyl shrink := f s cyl shrink ∘ g s cyl shrink;
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
  End suspension.

  Definition cyl {K:Category}: Functor (Cylinder K) (Suspension K) := {|
    fobj x := x ;
    map _ _ f _ _ _ := map f ;
  |}.

  Obligation 1.
  Proof.
    rewrite map_composes.
    reflexivity.
  Qed.

  Obligation 2.
  Proof.
    rewrite map_id.
    reflexivity.
  Qed.

  Obligation 3.
  Proof.
    cbn in *.
    apply map_compat.
    cbn.
    split.
    auto.
    exists.
  Qed.

  Definition shrink {K:Category} {A B: K} {X}: Isomorphism (Suspension K) (A, X) (B, X) := {|
    to s cyl shrink := to _ _ _ (shrink A B X) ;
    from s cyl shrink := from _ _ _ (shrink A B X) ;
   |}.

  Obligation 1.
  Proof.
    apply to_from.
  Qed.

  Obligation 2.
  Proof.
    apply from_to.
  Qed.
End Suspension.

Instance Circle: Category := Coequalizer Trivial Trivial (id: (_:Cat)~>_) (id: (_:Cat)~>_).

Definition base: Circle := {| dom := 0; proj := le_n 0 |}.

Definition zero: base ~> base := id.

Definition one: base ~> base.
  cbn.
  intros ? ? shrink.
  apply (to _ _ _ (shrink _)).
Defined.

Definition negone: base ~> base.
  cbn.
  intros ? ? shrink.
  apply (from _ _ _ (shrink _)).
Defined.

Instance Z: Category := {
  object := unit ;
  hom _ _ := (nat * nat) /~ {| equiv x y := fst x + snd y = snd y + fst x |} ;
  id _ := (0, 0) ;
  compose _ _ _ f g := (fst f + fst g, snd f + snd g) ;
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

Obligation 5.
Proof.
  admit.
Admitted.

Definition cyl: (Trivial:Cat) ~> Z := {|
  fobj _ := tt ;
  map _ _ _ := id ;
|}.

Fixpoint neg (n: nat): base ~> base :=
  match n with
  | 0 => zero
  | S n => negone ∘ neg n
  end.

Fixpoint pos (n: nat): base ~> base :=
  match n with
  | 0 => zero
  | S n => one ∘ pos n
  end.

Definition to (mn: (tt:Z) ~> tt): base ~> base := pos (fst mn) ∘ neg (snd mn).
Definition from (f: base ~> base): (tt:Z) ~> tt :=
  f Z cyl (λ _, {|
       Isomorphism.to := (1, 0) ;
       Isomorphism.from := (0, 1) ;
       to_from := eq_refl;
       from_to := eq_refl |}).

Compute from (to (12, 3)).

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
