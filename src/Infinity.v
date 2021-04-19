(* Seems to make classes go faster? *)
Set Primitive Projections.
Unset Printing Primitive Projection Parameters.

Require Import Coq.Setoids.Setoid.

Reserved Notation "| A |" (at level 40).

Reserved Notation "A ~ B" (at level 70).

Reserved Notation "A /~ B" (at level 40).

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

Module Setoid.
  (* We need Bishop sets (AKA Setoids) not Coq's Type to make the Yoneda
     embedding on presheafs work properly.

     The technical jargon is that a Setoid is a 0-trivial groupoid,
     equality is the hom. *)
  Polymorphic Cumulative Class Setoid := {
    type: Type ;
    equal: relation type ;
    Setoid_Equivalence:> Equivalence equal
  }.

  Module Import SetoidNotations.
    Coercion type: Setoid >-> Sortclass.
    Coercion equal: Setoid >-> relation.
  End SetoidNotations.
End Setoid.

Import Setoid.SetoidNotations.

Module Import Category.
  Import Setoid.
  Local Notation "A ~ B" := (equal A B).

  Polymorphic Cumulative Class Category := {
    object: Type ;
    hom: object -> object -> Setoid
    where "A ~> B" := (hom A B) ;

    id {A}: hom A A ;
    compose {A B C}: hom B C -> hom A B -> hom A C
    where "f ∘ g" := (compose f g) ;

    compose_assoc {A B C D} (f: hom C D) (g: hom B C) (h: hom A B):
      (f ∘ (g ∘ h)) ~ ((f ∘ g) ∘ h );
    compose_id_left {A B} (f: hom A B): (id ∘ f) ~ f ;
    compose_id_right {A B} (f: hom A B): (f ∘ id) ~ f ;

    compose_compat {A B C} (f f': hom B C) (g g': hom A B):
      f ~ f' -> g ~ g' -> f ∘ g ~ f' ∘ g' ;
  }.

  Polymorphic Add Parametric Morphism (K: Category) (A B C: @object K) : (@compose _ A B C)
      with signature equal ==> equal ==> equal as compose_mor.
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
    Notation "A ~> B" := (Category.hom A B).
  End CategoryNotations.
End Category.

Module Import Sets.
  Import Setoid.

  Module Import Fns.
    Polymorphic Class fn (A B: Setoid) := {
      op: @type A -> @type B ;
      map {A B}: equal A B -> equal (op A) (op B)
    }.
  End Fns.

  Polymorphic Local Definition eq {A B} (f g: fn A B) := forall x, equal (@op _ _ f x) (@op _ _ g x).
  Polymorphic Local Definition eq_Equivalence {A B}: Equivalence (@eq A B).
  exists.
  all:unfold Reflexive, Symmetric, Transitive, eq;cbn.
  - intros.
    reflexivity.
  - intros.
    symmetry.
    auto.
  - intros ? ? ? p q ?.
    rewrite (p _), (q _).
    reflexivity.
  Qed.

  Polymorphic Local Definition hom A B := {|
    type := fn A B;
    equal := eq;
    Setoid_Equivalence := eq_Equivalence;
  |}.

  Polymorphic Local Definition id {A}: @type (hom A A).
  exists (fun x => x).
  intros.
  apply H.
  Defined.

  Polymorphic Local Definition compose {A B C} (f: @type (hom B C)) (g: @type (hom A B)): @type (hom A C).
  exists (fun x => @op _ _ f (@op _ _ g x)).
  cbn.
  unfold compose.
  intros ? ? x.
  apply map.
  apply map.
  apply x.
  Defined.

  Polymorphic Definition Setoid: Category.
  exists Setoid hom @id @compose.
  - intros ? ? ? ? ? ? ? ?.
    reflexivity.
  - intros.
    reflexivity.
  - intros.
    reflexivity.
  - intros ? ? ? ? ? ? ? p q ?.
    cbn.
    rewrite (p _).
    apply map.
    rewrite (q _).
    reflexivity.
  Defined.

  Module Import SetoidNotations.
    Coercion op: fn >-> Funclass.

    Notation "A ~ B" := (@equal (_:Setoid) A B).
    Notation "A /~ B" := ({| type := A ; equal := (B:relation A) |}:Setoid).
  End SetoidNotations.
End Sets.

Import SetoidNotations.
Import CategoryNotations.

Module Setoids.
  Definition True: Setoid.
    exists True (fun _ _ => True).
    exists.
    all:auto.
  Defined.

  Definition False: Setoid.
    exists False (fun (A:False) _ => match A with end).
    exists.
    all:unfold Reflexive, Symmetric, Transitive; cbn.
    all:intros.
    all:contradiction.
  Defined.
End Setoids.

Module Import Preset.
  Polymorphic Local Definition eq {A B}: relation (A -> B) := fun f g => forall x, f x = g x.
  Polymorphic Local Instance eq_Equivalence A B: Equivalence (@eq A B).
  exists.
  all:unfold Reflexive, Symmetric, Transitive, eq;cbn.
  all:auto.
  intros ? ? ? p q ?.
  rewrite (p _), (q _).
  reflexivity.
  Qed.

  Polymorphic Local Definition hom A B := (A -> B) /~ (@eq A B).

  Polymorphic Local Definition id {A}: hom A A := fun x => x.

  Polymorphic Local Definition compose {A B C} (f: hom B C) (g: hom A B): hom A C :=
    fun x => f (g x).

  Polymorphic Definition Preset: Category.
  exists Type hom @id @compose.
  all:unfold hom, eq, compose;cbn.
  all:auto.
  intros ? ? ? ? ? ? ? p q ?.
  rewrite (p _), (q _).
  reflexivity.
  Defined.
End Preset.

Module Import Isomorphism.
  Section iso.
    Polymorphic Context `(K:Category).

    Polymorphic Cumulative Record iso (A B: K) := {
      to: K A B ;
      from: K B A ;
      to_from: to ∘ from ~ id ;
      from_to: from ∘ to ~ id ;
   }.

    Polymorphic Local Definition eq {A B} (f g: iso A B): Prop :=
      @to _ _ f ~ @to _ _ g /\ @from _ _ f ~ @from _ _ g.

    Polymorphic Local Instance eq_Equivalence A B: Equivalence (@eq A B).
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

    Polymorphic Local Definition hom A B := iso A B /~ eq.

    Polymorphic Local Definition id {A: K}: hom A A.
    exists id id.
    - apply compose_id_left.
    - apply compose_id_right.
    Defined.

    Polymorphic Local Definition compose {A B C} (f: hom B C) (g: hom A B): hom A C.
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
End Isomorphism.

Import IsomorphismNotations.

Module Import Functor.
  Import TruncateNotations.

  Polymorphic Cumulative Class functor (C D: Category) := {
    fobj: C -> D ;
    map {A B}: C A B -> D (fobj A) (fobj B) ;

    map_composes {X Y Z} (f: C Y Z) (g: C X Y): map f ∘ map g~ map (f ∘ g) ;

    map_id {A}: map (@id _ A) ~ id ;
    map_compat {A B} (f f': C A B): f ~ f' -> map f ~ map f' ;
  }.

  Module Import FunctorNotations.
    Coercion fobj: functor >-> Funclass.
    Notation "F ! X" := (map (functor := F) X).
  End FunctorNotations.

  Polymorphic Add Parametric Morphism (C D: Category) (A B: C) (F: functor C D) : (@map _ _ F A B)
      with signature (@Setoid.equal _) ==> Setoid.equal as map_mor.
  Proof.
    intros ? ? p.
    apply map_compat.
    apply p.
  Qed.

  Polymorphic Local Definition eq {C D} (A B: functor C D) := forall x: C, | A x <~> B x |.

  Polymorphic Local Instance eq_Equivalence C D: Equivalence (@eq C D).
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

  Polymorphic Definition Functor (A B: Category): Setoid := functor A B /~ eq.

  Polymorphic Local Definition id {A}: Functor A A.
  exists (fun x => x) (fun _ _ f => f).
  - intros ? ? ? ? ?.
    reflexivity.
  - intros.
    reflexivity.
  - intros ? ? ? ? p.
    apply p.
  Defined.

  Polymorphic Local Definition compose {A B C} (F: Functor B C) (G: Functor A B): Functor A C.
  exists (fun x => F (G x)) (fun _ _ x => F ! (G ! x)).
  - intros.
    rewrite map_composes, map_composes.
    reflexivity.
  - intros.
    rewrite map_id, map_id.
    reflexivity.
  - intros ? ? ? ? p.
    apply map_compat.
    + apply map_compat.
      * apply p.
  Defined.

  Polymorphic Local Definition to_iso {A B: Category} (f: Functor A B): Functor (Isomorphism A) (Isomorphism B).
  eexists _ _.
  Unshelve.
  4: apply (fun x => f x).
  4: {
    cbn.
    intros X Y p.
    exists (f ! (@to _ _ _ p)) (f ! (@from _ _ _ p)).
    all: rewrite map_composes.
    all: rewrite <- map_id.
    all: apply map_compat.
    1: rewrite <- to_from.
    2: rewrite <- from_to.
    all: reflexivity.
  }
  all: cbn.
  - intros.
    exists.
    + cbn.
      rewrite map_composes.
      reflexivity.
    + cbn.
      rewrite map_composes.
      reflexivity.
  - intros.
    exists.
    + cbn.
      apply map_id.
    + cbn.
      apply map_id.
  - intros.
    exists.
    + destruct H.
      cbn.
      apply map_compat.
      apply H.
    + destruct H.
      apply map_compat.
      apply H0.
  Defined.

  Polymorphic Local Definition compose_compat {A B C : Category} (f f' : Functor B C) (g g' : Functor A B):
    (f ~ f') ->
    (g ~ g') ->
    compose f g ~ compose f' g'.
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

  Polymorphic Definition Cat: Category.
  exists Category Functor @id @compose.
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
End Functor.

Import FunctorNotations.

Module Import NaturalTransformation.
  Section functor.
    Polymorphic Variables K L : Category.

    Polymorphic Local Definition nt (A B: Functor K L) := forall x, L (@fobj _ _ A x) (@fobj _ _ B x).

    Polymorphic Local Definition eq {A B} (f g: nt A B): Prop := forall x, f x ~ g x.

    Polymorphic Local Instance eq_Equivalence A B: Equivalence (@eq A B).
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

    Polymorphic Local Definition hom A B := nt A B /~ eq.

    Polymorphic Local Definition id {A}: hom A A := fun _ => id.
    Polymorphic Local Definition compose {A B C} (f: hom B C) (g: hom A B): hom A C := fun _ => f _ ∘ g _.

    Polymorphic Definition NaturalTransformation: Category.
    exists (Functor _ _) hom @id @compose.
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
End NaturalTransformation.

Module Import Over.
  Section over.
    Polymorphic Context `(Category).
    Polymorphic Variable c : object.

    Polymorphic Cumulative Record bundle := {
      dom: object ;
      proj: dom ~> c ;
    }.

    (* I really could just use an ordinary sigma type but it makes the
    types messier down the line *)
    Polymorphic Cumulative Record over A B := {
      slice: dom A ~> dom B;
      commutes: proj B ∘ slice ~ proj A
    }.

    Polymorphic Local Definition eq {A B} (f g: over A B) := slice _ _ f ~ slice _ _ g.

    Polymorphic Local Instance eq_Equivalence A B: Equivalence (@eq A B).
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

    Polymorphic Local Definition hom A B := over A B /~ eq.

    Polymorphic Local Definition id {A} : hom A A.
    exists id.
    apply compose_id_right.
    Defined.

    Polymorphic Local Definition compose {X Y Z} : hom Y Z -> hom X Y -> hom X Z.
    intros f g.
    exists (slice _ _ f ∘ slice _ _ g).
    rewrite compose_assoc.
    rewrite (commutes _ _ f).
    apply (commutes _ _ g).
    Defined.

    Polymorphic Local Definition compose_assoc {X Y Z W} (f: hom Z W) (g: hom Y Z) (h: hom X Y): eq (compose f (compose g h)) (compose (compose f g) h).
    Proof using Type.
      apply compose_assoc.
    Qed.

    Polymorphic Local Definition compose_id_left A B (f: hom A B): eq (compose id f) f.
    Proof using Type.
      apply compose_id_left.
    Qed.

    Polymorphic Local Definition compose_id_right {A B} (f: hom A B): eq (compose f id) f.
    Proof using Type.
      apply compose_id_right.
    Qed.

    Polymorphic Local Definition compose_compat {A B C} (f f': hom B C) (g g': hom A B):
      eq f f' -> eq g g' -> eq (compose f g) (compose f' g').
    Proof using Type.
      unfold eq.
      cbn.
      intros p p'.
      rewrite p.
      rewrite p'.
      reflexivity.
    Qed.

    Polymorphic Definition Over : Category.
    exists bundle hom @id @compose.
    - apply @compose_assoc.
    - apply @compose_id_left.
    - apply @compose_id_right.
    - apply @compose_compat.
    Defined.
  End over.

  Polymorphic Definition Σ {C:Category} {c} (f: Over C c) (g: Over C (dom _ _ f)): Over C c :=
    {| proj := proj _ _ f ∘ proj _ _ g |}.

  Module OverNotations.
    Notation "C / c" := (Over.Over C c).
  End OverNotations.
End Over.

Import OverNotations.

Module Import Empty.
  Local Definition hom (A: False): False -> Setoid := match A with end.

  Local Definition id {A: False}: hom A A := match A with end.
  Local Definition compose {A B C}: hom B C -> hom A B -> hom A C := match A with end.

  Definition Empty: Category.
    exists False hom @id @compose.
    all:unfold compose, id, hom.
    all:cbn.
    all:intros.
    all:contradiction.
  Defined.
End Empty.

Module Import Trivial.
  Local Definition hom (A B:True) := Setoids.True.

  Local Definition id {A}: hom A A := I.
  Local Definition compose {A B C} (_: hom B C) (_: hom A B): hom A C := I.

  Definition Trivial: Category.
    exists True hom @id @compose.
    all:unfold compose, id, hom; cbn.
    all:intros.
    all:exists.
  Defined.
End Trivial.

Module Import Props.
  Polymorphic Definition ProofIrrelevance (S: Setoid) := forall x y: S, x ~ y.

  Polymorphic Cumulative Class MereProp := {
    Prop_Setoid: Setoid ;
    Prop_Irrelevant: ProofIrrelevance Prop_Setoid ;
  }.

  Polymorphic Definition ThinSet (A: Type): Setoid.
  eapply (A /~ (fun _ _ => True)).
  Unshelve.
  exists.
  all:auto.
  Defined.

  Polymorphic Definition AProp (A: Type): MereProp.
  exists (ThinSet A).
  exists.
  Defined.
End Props.

Module Import Interval.
  Local Definition hom A B := match (A, B) with
                        | (true, true) => Setoids.True
                        | (false, false) => Setoids.True
                        | (false, true) => Setoids.True
                        | (_, _) => Setoids.False
                        end.

  Local Definition id {A}: hom A A.
    destruct A.
    all:cbn.
    all:auto.
  Defined.

  Local Definition compose {A B C}: hom B C -> hom A B -> hom A C.
    destruct A, B, C.
    all:cbn.
    all:auto.
  Defined.

  Definition Interval: Category.
    exists bool hom @id @compose.
    - intros A B C D.
      destruct A, B, C, D.
      all:cbn.
      all:auto.
      all:contradiction.
    - intros A B.
      destruct A, B.
      all:cbn.
      all:auto.
      all:contradiction.
    - intros A B.
      destruct A, B.
      all:cbn.
      all:auto.
      all:contradiction.
    - intros A B C.
      destruct A, B, C.
      all:cbn.
      all:auto.
  Defined.
End Interval.

Module Import Arrow.
  Section arrows.
    Polymorphic Variables K: Category.

    Polymorphic Record arrow := {
      dom: K ;
      cod: K ;
      proj: dom ~> cod ;
    }.

    Polymorphic Record arr (A B: arrow) := {
      to: cod A ~> cod B ;
      from: dom A ~> dom B ;
      commutes: to ∘ proj A ~ proj B ∘ from ;
    }.

    Polymorphic Local Definition eq {A B} (f g: arr A B) :=
      (to _ _ f ~ to _ _ g) /\ (from _ _ f ~ from _ _ g).
    Polymorphic Local Instance eq_Equivalence A B: Equivalence (@eq A B).
    exists.
    all: unfold Reflexive, Symmetric, Transitive, eq; cbn.
    all:split.
    all: try reflexivity.
    - destruct H.
      symmetry.
      auto.
    - destruct H.
      symmetry.
      auto.
    - destruct H, H0.
      rewrite H, H0.
      reflexivity.
    - destruct H, H0.
      rewrite H1, H2.
      reflexivity.
    Qed.

    Polymorphic Local Definition hom A B := arr A B /~ eq.

    Polymorphic Local Definition id {A}: hom A A.
    exists id id.
    rewrite compose_id_left.
    rewrite compose_id_right.
    reflexivity.
    Defined.

    Polymorphic Local Definition compose {A B C} (f: hom B C) (g: hom A B): hom A C.
    exists (to _ _ f ∘ to _ _ g) (from _ _ f ∘ from _ _ g).
    rewrite <- compose_assoc.
    rewrite (commutes _ _ g).
    rewrite compose_assoc.
    rewrite compose_assoc.
    rewrite (commutes _ _ f).
    reflexivity.
    Defined.

    Polymorphic Definition Arrow: Category.
    exists arrow hom @id @compose.
    all: cbn; unfold id, compose, eq; cbn.
    - split.
      all: rewrite compose_assoc.
      all: reflexivity.
    - split.
      all:rewrite compose_id_left.
      all:reflexivity.
    - split.
      all:rewrite compose_id_right.
      all:reflexivity.
    - intros ? ? ? ? ? ? ? p q.
      destruct p, q.
      split.
      1: rewrite H, H1.
      2: rewrite H0, H2.
      all:reflexivity.
    Defined.
  End arrows.
End Arrow.

Module Import Finite.
 (* Definie finite totally ordered sets *)
  Local Instance le_Reflexive: Reflexive le.
  auto.
  Qed.

  Local Instance le_Transitive: Transitive le.
  intros ? ? ? f g.
  induction g.
  - apply f.
  - auto.
  Qed.

  Local Definition eq {A B} (_ _:A <= B) := True.
  Local Instance eq_Equivalence A B: Equivalence (@eq A B).
  exists.
  all:exists.
  Qed.

  Local Definition hom (A B: nat) := (A <= B) /~ eq.

  Local Definition id {A}: hom A A.
  cbn.
  auto.
  Defined.

  Local Definition compose {A B C}: hom B C -> hom A B -> hom A C.
  cbn.
  intros f g.
  rewrite g, f.
  reflexivity.
  Defined.

  Local Definition le: Category.
  exists nat hom @id @compose.
  all:exists.
  Defined.

  Definition finite (N:nat) := le/N.

  Module Import FiniteNotations.
    (* FIXME Isolate notations *)
    Notation "[ N ]" := (finite N).
  End FiniteNotations.

  Local Definition any_gt_0 C: 0 <= C.
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
    exists.
  Defined.
End Finite.

Import FiniteNotations.

Module Import Opposite.
  Section opposite.
    Polymorphic Context `(K:Category).

    Polymorphic Local Definition hom (A B: K) := hom B A.

    Polymorphic Local Definition id {A} : hom A A := id.
    Polymorphic Local Definition compose {A B C} : hom B C -> hom A B -> hom A C := fun f g => g ∘ f.

    Polymorphic Local Definition eq {A B} (f g: hom A B) := f ~ g.

    Polymorphic Local Instance eq_Equivalence A B: Equivalence (@eq A B).
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

Module Diagrams.
  Section diagrams.
    Polymorphic Context {C:Category}.

    Polymorphic Definition Empty: (op Empty:Cat) ~> C.
    eexists _ _.
    Unshelve.
    all: intro A; destruct A.
    Defined.

    Polymorphic Definition Constant {D} (c: C): (op D:Cat) ~> C.
    exists (fun _ => c) (fun _ _ _ => id).
    all: intros; cbn.
    1: apply compose_id_left.
    all: reflexivity.
    Defined.

    Polymorphic Definition Fn {A B: C} (f: A ~> B): (op Interval:Cat) ~> C.
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
  Polymorphic Definition weighted {D:Cat} (F G: (op D:Cat) ~> Setoid):Setoid :=
    NaturalTransformation _ _ F G.

  Polymorphic Definition pt {D:Cat}: (op D:Cat) ~> Setoid := Diagrams.Constant Setoids.True.

  Polymorphic Definition limit (D:Cat) (F: (op D:Cat) ~> Setoid) := weighted pt F.
  (* Not sure if it should be point or empty *)
  Polymorphic Definition colimit (D:Cat) (F: (op D:Cat) ~> Setoid) := weighted F pt.

  (* Just an example *)
  Polymorphic Definition unit := limit _ Diagrams.Empty.
  Polymorphic Definition bang {A} : A ~> unit.
  exists (fun _ x => match x:False with end).
  intros.
  cbn.
  unfold NaturalTransformation.eq.
  intros.
  cbn.
  unfold Sets.eq.
  cbn.
  intro.
  cbn.
  destruct x.
  Defined.
End Limit.

Module Product.
  Close Scope nat.

  Section products.
    Polymorphic Variable C D: Category.

    Polymorphic Local Definition hom' (A B: C * D) := prod (fst A ~> fst B) (snd A ~> snd B).

    Polymorphic Local Definition eq {A B} (f g: hom' A B) := fst f ~ fst g /\ snd f ~ snd g.

    Polymorphic Local Instance eq_Equivalence A B: Equivalence (@eq A B).
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
    Qed.

    Polymorphic Definition hom (A B: C * D): Setoid := hom' A B /~ eq.

    Polymorphic Definition id {A}: hom A A := (id, id).
    Polymorphic Definition compose {A B C} (f: hom B C) (g: hom A B): hom A C :=
      (fst f ∘ fst g, snd f ∘ snd g).

    Polymorphic Definition product: Cat.
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

  Polymorphic Definition fanout {A B C: Cat} (f: C ~> A) (g: C ~> B): C ~> product A B.
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

    Polymorphic Local Definition sum := C + D.
    Polymorphic Local Definition hom' (A B: sum): Type.
    destruct A as [AL|AR], B as [BL|BR].
    1: apply (AL ~> BL).
    3: apply (AR ~> BR).
    all: apply False.
    Defined.

    Polymorphic Local Definition eq {A B} (f g: hom' A B): Prop.
    destruct A as [AL|AR], B as [BL|BR].
    1: apply (f ~ g).
    3: apply (f ~ g).
    all: apply False.
    Defined.

    Polymorphic Local Instance eq_Equivalence A B: Equivalence (@eq A B).
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

    Polymorphic Local Definition hom (A B: sum): Setoid := hom' A B /~ eq.

    Polymorphic Definition coproduct: Category.
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

  Polymorphic Definition fanin {A B C: Cat} (f: A ~> C) (g: B ~> C): (coproduct A B:Cat) ~> C.
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

  Polymorphic Definition inl {A B:Cat}: A ~> coproduct A B.
  exists inl (fun _ _ x => x).
  - cbn.
    intros.
    reflexivity.
  - intros.
    reflexivity.
  - intros.
    apply H.
  Defined.

  Polymorphic Definition inr {A B:Cat}: B ~> coproduct A B.
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
  Definition hom (A B: nat): Setoid := ([A]: Cat) ~> [B].

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

Polymorphic Definition presheaf K: Category := NaturalTransformation (op K) Setoid.

Module Presheaf.
  Import Monoidal.
  Import MonoidalNotations.

  Section limits.
    Polymorphic Context {C D: Category}.
    Polymorphic Variable F: Functor (op D) C.

    Polymorphic Definition limit' (c: C): Setoid.
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
