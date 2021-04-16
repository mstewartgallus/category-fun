(* Seems to make classes go faster? *)
Set Primitive Projections.
Unset Printing Primitive Projection Parameters.

Require Import Coq.Setoids.Setoid.

Reserved Notation "| A |" (at level 40).

Reserved Notation "A /~ B" (at level 40).
Reserved Notation "A == B" (at level 70).

Reserved Notation "A ~> B" (at level 80).
Reserved Notation "A ∘ B" (at level 30).

Reserved Notation "A <~> B" (at level 80).
Reserved Notation "F 'ᵀ'" (at level 1).

Reserved Notation "F ! X" (at level 1).

Reserved Notation "A ⊗ B" (at level 30).
Reserved Notation "A ~~> B" (at level 80).

(* FIXME get propositional truncation from elsewhere *)
Polymorphic Variant truncate A: Prop :=
  | truncate_intro (_: A): truncate A.

Module TruncateNotations.
  Notation "| A |" := (truncate A).

  Polymorphic Definition ident (A: Type) := A.
  Coercion truncate_id {A}: ident A -> |A| := truncate_intro _.
End TruncateNotations.

Module Export Category.
  (* We need Bishop sets (AKA Setoids) not Coq's Type to make the Yoneda
     embedding on presheafs work properly.

     The technical jargon is that a Setoid is a 0-trivial groupoid,
     equality is the hom *)
  Polymorphic Cumulative Class Morphism := {
    type: Type ;
    equal: type -> type -> Prop
    where "A == B" := (equal A B) ;

    Setoid_Equivalence:> Equivalence equal
  }.

  Polymorphic Definition ThinMorphism (A: Type): Morphism.
  exists A (fun _ _ => True).
  exists.
  all:auto.
  Defined.

  Coercion type: Morphism >-> Sortclass.
  Coercion equal: Morphism >-> Funclass.

  Module Export MorphismNotations.
    Notation "A /~ B" := {| type := A ; equal := B |}.
    Notation "A == B" := (equal A B).
  End MorphismNotations.

  Polymorphic Cumulative Class Category := {
    object: Type ;
    hom: object -> object -> Morphism
    where "A ~> B" := (hom A B) ;

    id {A}: hom A A ;
    compose {A B C}: hom B C -> hom A B -> hom A C
    where "f ∘ g" := (compose f g) ;

    compose_assoc {A B C D} (f: hom C D) (g: hom B C) (h: hom A B):
      (f ∘ (g ∘ h)) == ((f ∘ g) ∘ h );
    compose_id_left {A B} (f: hom A B): (id ∘ f) == f ;
    compose_id_right {A B} (f: hom A B): (f ∘ id) == f ;

    compose_compat {A B C} (f f': hom B C) (g g': hom A B):
      f == f' -> g == g' -> f ∘ g == f' ∘ g' ;
  }.

  Module Export CategoryNotations.
    Coercion object: Category >-> Sortclass.
    Coercion hom: Category >-> Funclass.

    Notation "f ∘ g" := (compose f g).
    Notation "A ~> B" := ((_:Category) A B).
  End CategoryNotations.

  Polymorphic Add Parametric Morphism (K: Category) (A B C: K) : (@compose _ A B C)
      with signature equal ==> equal ==> equal as compose_mor.
  Proof.
    intros ? ? p ? ? q.
    apply compose_compat.
    apply p.
    apply q.
  Qed.
End Category.

Module Isomorphism.
  Section iso.
    Polymorphic Context `(K:Category).

    Polymorphic Cumulative Record hom' (A B: K) := {
      to: K A B ;
      from: K B A ;
      to_from: to ∘ from == id ;
      from_to: from ∘ to == id ;
   }.

    Polymorphic Definition eq {A B} (f g: hom' A B): Prop :=
      @to _ _ f == @to _ _ g /\ @from _ _ f == @from _ _ g.

    Polymorphic Instance eq_Equivalence A B: Equivalence (@eq A B).
    Proof using Type.
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
      + apply (Equivalence_Transitive _ _ _ p1 q1).
      + apply (Equivalence_Transitive _ _ _ p2 q2).
    Qed.

    Polymorphic Definition hom A B := hom' A B /~ eq.

    Polymorphic Definition id {A: K}: hom A A.
    exists id id.
    - apply compose_id_left.
    - apply compose_id_right.
    Defined.

    Polymorphic Definition compose {A B C} (f: hom B C) (g: hom A B): hom A C.
    exists (@to _ _ f ∘ @to _ _ g) (@from _ _ g ∘ @from _ _ f).
    - rewrite <- compose_assoc.
      rewrite -> (compose_assoc (@to _ _ g)).
      rewrite to_from.
      rewrite compose_id_left.
      rewrite to_from.
      reflexivity.
    - rewrite <- compose_assoc.
      rewrite -> (compose_assoc (@from _ _ f)).
      rewrite from_to.
      rewrite compose_id_left.
      rewrite from_to.
      reflexivity.
    Defined.

    Polymorphic Definition Isomorphism: Category.
    exists object hom @id @compose.
    all: unfold eq, compose ; cbn.
    - intros.
      split.
      + apply compose_assoc.
      + symmetry.
        apply compose_assoc.
    - intros.
      split.
      + apply compose_id_left.
      + apply compose_id_right.
    - intros.
      split.
      + apply compose_id_right.
      + apply compose_id_left.
    - intros ? ? ? ? ? ? ? p q.
      destruct p, q.
      split.
      + apply compose_compat.
        * apply H.
        * apply H1.
      + apply compose_compat.
        * apply H2.
        * apply H0.
    Defined.
  End iso.

  Polymorphic Definition transpose {C:Category} {A B: C} (f: Isomorphism _ A B): Isomorphism _ B A.
  exists (@from _ _ _ f) (@to _ _ _ f).
  - apply from_to.
  - apply to_from.
  Defined.

  Module Import IsomorphismNotations.
    Notation "A 'ᵀ'" := (transpose A).
    Notation "A <~> B" := (Isomorphism _ A B).
  End IsomorphismNotations.

  Import IsomorphismNotations.

End Isomorphism.

Definition Isomorphism: Category -> Category := Isomorphism.Isomorphism.

Module Functor.
  Polymorphic Cumulative Class functor (C D: Category) := {
    fobj: C -> D ;
    map {A B}: C A B -> D (fobj A) (fobj B) ;

    map_composes {X Y Z} (f: C Y Z) (g: C X Y): map f ∘ map g == map (f ∘ g) ;

    map_id {A}: map (@id _ A) == id ;
    map_compat {A B} (f f': C A B): f == f' -> map f == map f' ;
  }.

  Section functor.
    Polymorphic Variables K L : Category.

    Polymorphic Definition hom' (A B: functor K L) := forall x, L (@fobj _ _ A x) (@fobj _ _ B x).

    Polymorphic Definition eq {A B} (f g: hom' A B): Prop := forall x, f x == g x.

    Polymorphic Instance eq_Equivalence A B: Equivalence (@eq A B).
    Proof using Type.
    exists.
    all: unfold Reflexive, Symmetric, Transitive, compose, id, hom, eq; cbn.
    - intros.
      reflexivity.
    - intros ? ? p t.
      symmetry.
      apply (p t).
    - intros ? ? ? p q t.
      apply (Equivalence_Transitive _ _ _ (p t) (q t)).
    Qed.

    Polymorphic Definition hom A B := hom' A B /~ eq.

    Polymorphic Definition id {A}: hom A A := fun _ => id.
    Polymorphic Definition compose {A B C} (f: hom B C) (g: hom A B): hom A C := fun _ => f _ ∘ g _.

    Polymorphic Definition Functor: Category.
    exists (functor _ _) hom @id @compose.
    all: unfold compose, id, hom, eq ; cbn.
    - intros.
      apply compose_assoc.
    - intros.
      apply compose_id_left.
    - intros.
      apply compose_id_right.
    - intros ? ? ? ? ? ? ? p q t.
      apply compose_compat.
      + apply p.
      + apply q.
    Defined.
  End functor.

  Polymorphic Add Parametric Morphism (C D: Category) (A B: C) (F: Functor C D) : (@Functor.map _ _ F A B)
      with signature (@equal _) ==> equal as map_mor.
  Proof.
    intros ? ? p.
    apply Functor.map_compat.
    apply p.
  Qed.

  Module FunctorNotations.
    Coercion fobj: functor >-> Funclass.
    Notation "F ! X" := (map (functor := F) X).
  End FunctorNotations.
End Functor.

Import Functor.FunctorNotations.

Polymorphic Definition Functor: Category -> Category -> Category := Functor.Functor.

Module cat.
  Import TruncateNotations.
  Import Isomorphism.
  Import IsomorphismNotations.

  Polymorphic Definition eq {C D} (A B: Functor C D) := forall x: C, | A x <~> B x |.

  Polymorphic Instance eq_Equivalence C D: Equivalence (@eq C D).
  Proof.
  exists.
  all: unfold Reflexive, Symmetric, Transitive, compose, id, hom ; cbn.
  - intros ? f.
    exists.
    apply id.
  - intros ? ? p t.
    destruct (p t) as [p'].
    exists.
    apply (p' ᵀ).
  - intros ? ? ? p q t.
    destruct (p t) as [p'], (q t) as [q'].
    exists.
    apply (q' ∘ p').
  Qed.

  Polymorphic Definition hom (A B: Category): Morphism := Functor A B /~ eq.

  Polymorphic Definition id {A}: hom A A.
  exists (fun x => x) (fun _ _ f => f).
  - intros ? ? ? ? ?.
    reflexivity.
  - intros.
    reflexivity.
  - intros ? ? ? ? p.
    apply p.
  Defined.

  Polymorphic Definition compose {A B C} (F: hom B C) (G: hom A B): hom A C.
  exists (fun x => F (G x)) (fun _ _ x => F ! (G ! x)).
  - intros.
    rewrite Functor.map_composes, Functor.map_composes.
    reflexivity.
  - intros.
    rewrite Functor.map_id, Functor.map_id.
    reflexivity.
  - intros ? ? ? ? p.
    apply Functor.map_compat.
    + apply Functor.map_compat.
      * apply p.
  Defined.

  Polymorphic Definition to_iso {A B: Category} (f: Functor A B): Functor (Isomorphism A) (Isomorphism B).
  eexists _ _.
  Unshelve.
  4: apply (fun x => f x).
  4: {
    cbn.
    intros X Y p.
    exists (f ! (@to _ _ _ p)) (f ! (@from _ _ _ p)).
    all: rewrite Functor.map_composes.
    all: rewrite <- Functor.map_id.
    all: apply Functor.map_compat.
    1: rewrite <- to_from.
    2: rewrite <- from_to.
    all: reflexivity.
  }
  all: cbn.
  - intros.
    exists.
    + cbn.
      rewrite Functor.map_composes.
      reflexivity.
    + cbn.
      rewrite Functor.map_composes.
      reflexivity.
  - intros.
    exists.
    + cbn.
      apply Functor.map_id.
    + cbn.
      apply Functor.map_id.
  - intros.
    exists.
    + destruct H.
      cbn.
      apply Functor.map_compat.
      apply H.
    + destruct H.
      apply Functor.map_compat.
      apply H0.
  Defined.

  Polymorphic Definition compose_compat {A B C : Category} (f f' : hom B C) (g g' : hom A B):
    (f == f') ->
    (g == g') ->
    compose f g == compose f' g'.
  Proof.
    intros p q x.
    destruct (q x) as [q'].
    destruct (p (g' x)) as [p'].
    set (f_iso := to_iso f).
    set (pq := p' ∘ (f_iso ! q') : f (g x) <~> f' (g' x)).
    exists.
    exists (@to _ _ _ pq) (@from _ _ _ pq).
    - apply to_from.
    - apply from_to.
  Qed.

  Polymorphic Definition cat: Category.
  exists Category hom @id @compose.
  - intros ? ? ? ? ? ? ? ?.
    exists.
    apply Category.id.
  - intros ? ? ? ?.
    exists.
    apply Category.id.
  - intros ? ? ? ?.
    exists.
    apply Category.id.
  - apply @compose_compat.
  Defined.
End cat.

Polymorphic Definition cat: Category := cat.cat.

(* FIXME define Set as Prosets that are groupoids? *)
Module Proset.
  (* A partially ordered set is a thin category *)
  Polymorphic Definition IsThin (A: Morphism) := forall x y: A, x == y.
  Polymorphic Definition IsSet (C: Category) := forall A B, IsThin (C A B).

  Polymorphic Cumulative Class ASet := {
    ASet_Category:> Category ;
    ASet_IsSet: IsSet ASet_Category
  }.

  Module Import SetNotations.
    (* FIXME Isolate notations *)
    Coercion ASet_Category: ASet >-> Category.
  End SetNotations.

  (* Define the category of prosets as a subcategory of cat *)
  Polymorphic Definition hom (C D: ASet): Morphism := (C: cat) ~> D.

  Polymorphic Definition id {A}: hom A A := id.
  Polymorphic Definition compose {A B C}: hom B C -> hom A B -> hom A C := compose.

  Polymorphic Definition Proset: Category.
  exists ASet hom @id @compose.
  - intros.
    apply compose_assoc.
  - intros.
    apply compose_id_left.
  - intros.
    apply compose_id_right.
  - intros.
    apply compose_compat.
    + apply H.
    + apply H0.
  Defined.

  Polymorphic Definition AsASet A (preorder: relation A) `(Reflexive _ preorder) `(Transitive _ preorder): Proset.
  eexists _.
  Unshelve.
  2: {
    eexists A _ _ _.
    Unshelve.
    5: {
      intros X Y.
      apply (ThinMorphism (preorder X Y)).
    }
    5: {
      cbn.
      intros.
      reflexivity.
    }
    5: {
      cbn.
      intros ? ? ? p q.
      rewrite q, p.
      reflexivity.
    }
    all: cbn; intros; auto.
  }
  unfold IsSet.
  cbn.
  intros ? ? ? p.
  exists.
  Defined.
End Proset.

Import Proset.SetNotations.
Polymorphic Definition Proset: Category := Proset.Proset.

Module Props.
  Import Proset.
  Import Isomorphism.IsomorphismNotations.

  (* Define a mere proposition as a proof irrelevant proset *)
  Polymorphic Definition IsProp (C: Proset) := forall x y: C, x <~> y.

  Polymorphic Cumulative Class AProp := {
    AProp_Set:Proset ;
    AProp_IsProp: IsProp AProp_Set
  }.

  Module Import PropNotations.
    Coercion AProp_Set: AProp >-> object.
  End PropNotations.

  Polymorphic Definition hom (C D: AProp): Morphism := ThinMorphism True.

  Polymorphic Definition id {A}: hom A A.
  cbn.
  auto.
  Defined.

  Polymorphic Definition compose {A B C}: hom B C -> hom A B -> hom A C.
  auto.
  Defined.

  Polymorphic Definition Props: Category.
  exists AProp hom @id @compose.
  all: cbn; auto.
  Defined.

  Section props.
    Polymorphic Variable K: Type.

    Polymorphic Definition phom (A B: K) := ThinMorphism True.

    Polymorphic Definition AsAProp: Props.
    eexists _.
    Unshelve.
    2: {
      eexists _.
      Unshelve.
      2: {
        exists K @phom (fun _ => I) (fun _ _ _ _ _ => I).
        all: cbn; auto.
      }
      exists.
    }
    intros.
    exists I I.
    all: exists.
    Defined.
  End props.
End Props.

Import Props.PropNotations.

Polymorphic Definition Props: Category := Props.Props.
Polymorphic Definition Empty: Props := Props.AsAProp False.
Polymorphic Definition Trivial: Props := Props.AsAProp True.


Module Over.
  Section over.
    Polymorphic Context `(Category).
    Polymorphic Variable c : object.

    Polymorphic Cumulative Record bundle := {
      dom: object ;
      proj: dom ~> c ;
    }.

    (* I really could just use an ordinary sigma type but it makes the
    types messier down the line *)
    Polymorphic Cumulative Record hom' A B := {
      slice: dom A ~> dom B;
      commutes: proj B ∘ slice == proj A
    }.

    Polymorphic Definition eq {A B} (f g: hom' A B) := slice _ _ f == slice _ _ g.

    Polymorphic Instance eq_Equivalence A B: Equivalence (@eq A B).
    Proof using Type.
      exists.
      all: unfold Reflexive, Symmetric, Transitive, eq.
      - intro.
        reflexivity.
      - intros ? ? p.
        symmetry.
        apply p.
      - intros ? ? ? p q.
        rewrite p, q.
        reflexivity.
    Qed.

    Polymorphic Definition hom A B := hom' A B /~ eq.

    Polymorphic Definition id {A} : hom A A.
    exists id.
    apply compose_id_right.
    Defined.

    Polymorphic Definition compose {X Y Z} : hom Y Z -> hom X Y -> hom X Z.
    intros f g.
    exists (slice _ _ f ∘ slice _ _ g).
    rewrite compose_assoc.
    rewrite (commutes _ _ f).
    apply (commutes _ _ g).
    Defined.

    Polymorphic Definition compose_assoc {X Y Z W} (f: hom Z W) (g: hom Y Z) (h: hom X Y): eq (compose f (compose g h)) (compose (compose f g) h).
    Proof using Type.
      apply compose_assoc.
    Qed.

    Polymorphic Definition compose_id_left A B (f: hom A B): eq (compose id f) f.
    Proof using Type.
      apply compose_id_left.
    Qed.

    Polymorphic Definition compose_id_right {A B} (f: hom A B): eq (compose f id) f.
    Proof using Type.
      apply compose_id_right.
    Qed.

    Polymorphic Definition compose_compat {A B C} (f f': hom B C) (g g': hom A B):
      eq f f' -> eq g g' -> eq (compose f g) (compose f' g').
    Proof using Type.
      unfold eq.
      cbn.
      intros p p'.
      rewrite p.
      rewrite p'.
      reflexivity.
    Qed.

    Polymorphic Definition over : Category.
    exists bundle hom @id @compose.
    - apply @compose_assoc.
    - apply @compose_id_left.
    - apply @compose_id_right.
    - apply @compose_compat.
    Defined.
  End over.

  Polymorphic Definition Σ {C:Category} {c} (f: over C c) (g: over C (dom _ _ f)): over C c :=
    {| proj := proj _ _ f ∘ proj _ _ g |}.

  (* FIXME Isolate this notation *)
  Module Import OverNotations.
    Notation "C / c" := (Over.over C c).
  End OverNotations.
End Over.

Import Over.OverNotations.

Module Finite.
 (* Definie finite totally ordered sets *)
  Instance le_Reflexive: Reflexive le.
  auto.
  Qed.

  Instance le_Transitive: Transitive le.
  intros ? ? ? f g.
  induction g.
  - apply f.
  - auto.
  Qed.

  Definition finite (N:nat): Proset.
    exists ((Proset.AsASet _ le _ _)/N).
    exists.
  Defined.

  Module Import FiniteNotations.
    (* FIXME Isolate notations *)
    Notation "[ N ]" := (finite N).
  End FiniteNotations.

  Definition any_gt_0 C: 0 <= C.
  Proof.
    induction C.
    - auto.
    - auto.
  Qed.

  Definition source C: [C].
    exists 0.
    apply any_gt_0.
  Defined.

  Definition target C: [C].
    exists C.
    cbn.
    auto.
  Defined.

  Definition walk {C}: source C ~> target C.
    exists (any_gt_0 C).
    cbn.
    auto.
  Defined.
End Finite.

Import Finite.FiniteNotations.

Module Interval.
  Definition hom A B := ThinMorphism
                          match (A, B) with
                          | (true, true) => True
                          | (false, false) => True
                          | (false, true) => True
                          | (_, _) => False
                          end.

  Definition id {A}: hom A A.
    destruct A.
    all:cbn.
    all:auto.
  Qed.

  Definition compose {A B C}: hom B C -> hom A B -> hom A C.
    destruct A, B, C.
    all:cbn.
    all:auto.
  Qed.

  Definition Interval: Category.
    exists bool hom @id @compose.
    all:cbn.
    all:auto.
  Defined.
End Interval.

Definition Interval: Category := Interval.Interval.

Module Opposite.
  Section opposite.
    Polymorphic Context `(K:Category).

    Polymorphic Definition hom (A B: K) := hom B A.

    Polymorphic Definition id {A} : hom A A := id.
    Polymorphic Definition compose {A B C} : hom B C -> hom A B -> hom A C := fun f g => g ∘ f.

    Polymorphic Definition eq {A B} (f g: hom A B) := f == g.

    Polymorphic Instance eq_Equivalence A B: Equivalence (@eq A B).
    exists.
    all: unfold Reflexive, Symmetric, Transitive, compose, id, hom, eq ; intros; cbn.
    - reflexivity.
    - rewrite H.
      reflexivity.
    - rewrite H, H0.
      reflexivity.
    Qed.

    Polymorphic Definition op: Category.
    exists object hom @id @compose.
    all: unfold hom, eq, compose, id; intros; cbn.
    - rewrite compose_assoc.
      reflexivity.
    - rewrite compose_id_right.
      reflexivity.
    - rewrite compose_id_left.
      reflexivity.
    - rewrite H, H0.
      reflexivity.
    Defined.
  End opposite.
End Opposite.

Polymorphic Definition op: cat -> cat := Opposite.op.

Module Diagrams.
  Section diagrams.
    Polymorphic Context {C:Category}.

    Polymorphic Definition Empty: op (Empty:Proset) ~> C.
    eexists _ _.
    Unshelve.
    all: intro A; destruct A.
    Defined.

    Polymorphic Definition Constant {D} (c: C): op D ~> C.
    exists (fun _ => c) (fun _ _ _ => id).
    all: intros; cbn.
    1: apply compose_id_left.
    all: reflexivity.
    Defined.

    Polymorphic Definition Fn {A B: C} (f: A ~> B): op Interval ~> C.
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
  Polymorphic Definition weighted {D:cat} (F G: op D ~> Proset) :=
    Proset.AsASet (F ~> G) equal _ _.

  Polymorphic Definition pt {D:cat}: op D ~> Proset := Diagrams.Constant (Trivial:Proset).

  Polymorphic Definition limit (D:cat) (F: op D ~> Proset) := weighted pt F.
  (* Not sure if it should be point or empty *)
  Polymorphic Definition colimit (D:cat) (F: op D ~> Proset) := weighted F pt.

  (* Just an example *)
  Polymorphic Definition unit := limit _ Diagrams.Empty.
  Polymorphic Definition bang {A} : A ~> unit.
  eexists (fun _ x => match x:False with end) _.
  Unshelve.
  4: {
    intros.
    intro.
    reflexivity.
  }
  all: cbn.
  all: auto.
  Defined.
End Limit.

Module Product.
  Close Scope nat.

  Section products.
    Polymorphic Variable C D: Category.

    Polymorphic Definition hom' (A B: C * D) := prod (fst A ~> fst B) (snd A ~> snd B).

    Polymorphic Definition eq {A B} (f g: hom' A B) := fst f == fst g /\ snd f == snd g.

    Polymorphic Definition hom (A B: C * D): Morphism.
    exists (hom' A B) eq.
    exists.
    all: unfold Reflexive, Symmetric, Transitive, eq; cbn.
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
    Defined.

    Polymorphic Definition id {A}: hom A A := (id, id).
    Polymorphic Definition compose {A B C} (f: hom B C) (g: hom A B): hom A C :=
      (fst f ∘ fst g, snd f ∘ snd g).

    Polymorphic Definition product: cat.
    exists (C * D) hom @id @compose.
    all:cbn.
    all:unfold eq;cbn;intros;auto.
    - destruct f, g, h.
      split.
      all: apply compose_assoc.
    - destruct f.
      split.
      all: apply compose_id_left.
    - destruct f.
      split.
      all: apply compose_id_right.
    - destruct f, f', g, g'.
      cbn in H, H0.
      destruct H, H0.
      cbn.
      split.
      + rewrite H, H0.
        reflexivity.
      + rewrite H1, H2.
        reflexivity.
    Defined.
  End products.

  Polymorphic Definition fst {A B}: product A B ~> A.
  exists fst (fun _ _ => fst).
  - intros.
    destruct f, g.
    reflexivity.
  - intros.
    reflexivity.
  - intros ? ? ? ? p.
    apply p.
  Defined.

  Polymorphic Definition snd {A B}: product A B ~> B.
  exists snd (fun _ _ => snd).
  - intros.
    destruct f, g.
    reflexivity.
  - intros.
    reflexivity.
  - intros ? ? ? ? p.
    apply p.
  Defined.

  Import Functor.
  Polymorphic Definition fanout {A B C: cat} (f: C ~> A) (g: C ~> B): C ~> product A B.
  exists (fun x => (f x, g x)) (fun _ _ x => (f ! x, g ! x)).
  all:cbn;intros;unfold Product.eq;cbn;auto.
  - split.
    all: apply map_composes.
  - split.
    all: apply map_id.
  - split.
    all: rewrite H.
    all: reflexivity.
  Defined.
End Product.

Module Coproduct.
  Close Scope nat.

  Section coproducts.
    Polymorphic Variable C D: Category.

    Polymorphic Definition sum := C + D.
    Polymorphic Definition hom' (A B: sum): Type.
    destruct A as [AL|AR], B as [BL|BR].
    1: apply (AL ~> BL).
    3: apply (AR ~> BR).
    all: apply False.
    Defined.

    Polymorphic Definition eq {A B} (f g: hom' A B): Prop.
    destruct A as [AL|AR], B as [BL|BR].
    1: apply (f == g).
    3: apply (f == g).
    all: apply False.
    Defined.

    Polymorphic Definition hom (A B: sum): Morphism.
    exists (hom' A B) eq.
    all: destruct A as [AL|AR], B as [BL|BR].
    all: exists.
    all: unfold Reflexive, Symmetric, Transitive, eq; cbn.
    all: intros; auto.
    all: try reflexivity.
    - symmetry.
      apply H.
    - rewrite H, H0.
      reflexivity.
    - symmetry.
      apply H.
    - rewrite H, H0.
      reflexivity.
    Defined.

    Polymorphic Definition coproduct: cat.
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

  Polymorphic Definition fanin {A B C: cat} (f: A ~> C) (g: B ~> C): coproduct A B ~> C.
  eexists (fun x => match x with | inl x' => f x' | inr x' => g x' end) _.
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

  Polymorphic Definition inl {A B}: A ~> coproduct (A:cat) B.
  exists inl (fun _ _ x => x).
  - cbn.
    intros.
    reflexivity.
  - intros.
    reflexivity.
  - intros.
    apply H.
  Defined.

  Polymorphic Definition inr {A B}: B ~> coproduct (A:cat) (B:cat).
  exists inr (fun _ _ x => x).
  - cbn.
    intros.
    reflexivity.
  - intros.
    reflexivity.
  - intros.
    apply H.
  Defined.
End Coproduct.

Module Monoidal.
  Import Isomorphism.
  Import IsomorphismNotations.

  Polymorphic Cumulative Class Monoidal `(Category) := {
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

  Polymorphic Cumulative Record Category `(Monoidal) := {
    object: Type ;
    hom: object -> object -> Category.object
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
Module Simplex.
  Definition hom (A B: nat): Morphism := ([A]: Proset) ~> [B].

  Definition id {A}: hom A A := id.
  Definition compose {A B C} (f: hom B C) (g: hom A B): hom A C := f ∘ g.

  Definition Δ: Category.
    exists nat hom @id @compose.
    all: unfold hom, compose, id; intros.
    - rewrite compose_assoc.
      reflexivity.
    - apply compose_id_left.
    - apply compose_id_right.
    - rewrite H, H0.
      reflexivity.
  Defined.
End Simplex.

Definition Δ: Category := Simplex.Δ.

Polymorphic Definition presheaf K: Category := Functor (op K) Proset.

Module Presheaf.
  Import Monoidal.
  Import MonoidalNotations.
  Import Functor.

  Section limits.
    Polymorphic Context {C D: Category}.
    Polymorphic Variable F: Functor (op D) C.

    Polymorphic Definition limit' (c: C): Proset.
    eapply (Proset.AsASet (forall t, c ~> F t)).
    Unshelve.
    3: {
      intros x y.
      apply (forall t, x t == y t).
    }
    all: unfold Reflexive, Transitive; cbn.
    - intros.
      reflexivity.
    - intros.
      rewrite (H _), (H0 _).
      reflexivity.
    Defined.

    Polymorphic Definition limit_map {X Y: op C} (f: X ~> Y): limit' X ~> limit' Y.
    cbn in f, X, Y.
    unfold Opposite.hom in f.
    eexists _ _.
    Unshelve.
    4: {
      intros x t.
      apply (x t ∘ f).
    }
    4: {
      intros ? ? p t.
      unfold limit' in A, B, p.
      cbn in A, B, p.
      rewrite (p t).
      reflexivity.
    }
    all: cbn.
    all: intros.
    all: auto.
    Defined.

    Polymorphic Definition limit: presheaf C.
    set (limit'' := limit' : op C -> Proset).
    exists limit'' @limit_map.
    - intros.
      cbn.
      unfold Opposite.compose.
      exists.
      eexists.
      Unshelve.
      all: cbn; unfold hom', eq; cbn; intros.
      all: auto.
      all: rewrite compose_assoc.
      all: reflexivity.
    - intros.
      exists.
      eexists.
      Unshelve.
      all: cbn; unfold hom', eq; cbn; intros.
      all: auto.
      all: rewrite compose_id_right.
      all: reflexivity.
    - intros.
      exists.
      eexists.
      Unshelve.
      all: cbn; unfold hom', eq; cbn; intros.
      all: auto.
      all: rewrite H.
      all: reflexivity.
    Defined.
  End limits.

  Polymorphic Definition unit {C}: presheaf C := limit Diagrams.Empty.

  Polymorphic Definition bang {C} (A: presheaf C): A ~> unit.
  intro t.
  cbn.
  eexists.
  Unshelve.
  all: cbn.
  all: auto.
  - intros ? x.
    destruct x.
  - intros ? ? ? x.
    destruct x.
  Defined.

  Polymorphic Definition unit {C}: presheaf C := limit Diagrams.Empty.

  Section yoneda.
    Polymorphic Variables C:Category.

    Polymorphic Definition yo (c: C) := limit (Diagrams.Constant c).

    Polymorphic Definition yo_map {A B: C} (f: A ~> B): yo A ~> yo B.
    intros X.
    eexists.
    Unshelve.
    all: cbn.
    all: auto.
    - intros g ?.
      apply (f ∘ g t).
    - cbn.
      intros ? ? p ?.
      rewrite (p _).
      reflexivity.
    Defined.

    Polymorphic Definition Yo: (C: cat) ~> presheaf C.
    exists yo @yo_map.
    - intros ? ? ? f g ?.
      exists.
      eexists.
      Unshelve.
      all:cbn.
      all:unfold eq, hom';cbn.
      all:intros.
      all:auto.
      all: rewrite compose_assoc.
      all: reflexivity.
    - cbn.
      exists.
      eexists.
      Unshelve.
      all:cbn; unfold eq, hom'; cbn.
      all:intros.
      all:auto.
      all: rewrite compose_id_left.
      all: reflexivity.
    - intros ? ? ? ? p ?.
      cbn.
      exists.
      eexists.
      Unshelve.
      all: cbn; unfold eq, hom'; cbn.
      all: auto.
      all: intros.
      all: rewrite p.
      all: reflexivity.
    Defined.
  End yoneda.

  (* FIXME define product on presheafs in terms of categorical/set product *)
  Polymorphic Instance product_Monoid C: Monoidal (presheaf C).
  admit.
  Admitted.
End Presheaf.

Polymorphic Definition sSet := presheaf Δ.


Polymorphic Definition InfinityCategory := Enriched.Category sSet (Presheaf.product_Monoid _).
