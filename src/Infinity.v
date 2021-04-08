Require Import Coq.Setoids.Setoid.

Reserved Notation "| A |" (at level 40).

Reserved Notation "A ~> B" (at level 80).
Reserved Notation "A ∘ B" (at level 30).
Reserved Notation "A == B" (at level 70).

Reserved Notation "A <~> B" (at level 80).
Reserved Notation "A ⊗ B" (at level 30).
Reserved Notation "A => B" (at level 80).

(* FIXME get propositional truncation from elsewhere *)
Polymorphic Variant truncate A: Prop := truncate_intro (_:A).

Module TruncateNotations.
  Notation "| A |" := (truncate A).
End TruncateNotations.
Import TruncateNotations.

Module Export Category.
  Polymorphic Cumulative Class Category := {
    object: Type ;
    hom: object -> object -> Type
    where "A ~> B" := (hom A B) ;

    id {A}: A ~> A ;
    compose {A B C}: B ~> C -> A ~> B -> A ~> C
    where "f ∘ g" := (compose f g) ;

    equal {A B} (f g: A ~> B): Prop
    where "f == g" := (equal f g) ;

    is_eqv A B: Equivalence (@equal A B) ;

    compose_assoc {A B C D} (f: C ~> D) (g: B ~> C) (h: A ~> B): f ∘ (g ∘ h) == (f ∘ g) ∘ h ;
    compose_id_left {A B} (f: A ~> B): (id ∘ f) == f ;
    compose_id_right {A B} (f: A ~> B): (f ∘ id) == f ;

    compose_compat {A B C} (f f': B ~> C) (g g': A ~> B):
      f == f' -> g == g' -> (f ∘ g) == (f' ∘ g') ;
  }.

  Module Export CategoryNotations.
    Notation "A ~> B" := (hom A B).
    Notation "f ∘ g" := (compose f g).
    Notation "f == g" := (equal f g).
  End CategoryNotations.

  Polymorphic Instance eq_cat C (A B: @object C) : @Equivalence (hom A B) equal := is_eqv _ _.

  Polymorphic Add Parametric Morphism K (A B C: @object K) : (@compose _ A B C)
      with signature equal ==> equal ==> equal as compose_mor.
  Proof.
    intros f f' p g g' p'.
    apply (compose_compat f f' g g' p p').
  Qed.
End Category.

Module Isomorphism.
  Polymorphic Record hom `{Category} (A B: object) := {
    to: A ~> B ;
    from: B ~> A ;
    to_from: to ∘ from == id ;
    from_to: from ∘ to == id ;
  }.

  Section iso.
    Context `(Category).

    Polymorphic Definition id {A: object}: hom A A.
    exists id id.
    all: rewrite compose_id_left ; reflexivity.
    Defined.

    Polymorphic Definition compose {A B C: object} (f: hom B C) (g: hom A B): hom A C.
    exists (to _ _ f ∘ to _ _ g) (from _ _ g ∘ from _ _ f).
    - rewrite <- compose_assoc.
      rewrite -> (compose_assoc (to _ _ g)).
      rewrite to_from.
      rewrite compose_id_left.
      rewrite to_from.
      reflexivity.
    - rewrite <- compose_assoc.
      rewrite -> (compose_assoc (from _ _ f)).
      rewrite from_to.
      rewrite compose_id_left.
      rewrite from_to.
      reflexivity.
    Defined.

    Polymorphic Definition eq {A B: object} (f g: hom A B) : Prop := to _ _ f == to _ _ g /\ from _ _ f == from _ _ g.

    Polymorphic Definition reflexivity {A B: object} (f: hom A B) : eq f f.
    Proof using Type.
      split.
      all: reflexivity.
    Qed.

    Polymorphic Definition symmetry {A B} (f g: hom A B) : eq f g -> eq g f.
    Proof using Type.
      intro p.
      destruct p as [H0 H1].
      split.
      all: try rewrite H0; try rewrite H1; reflexivity.
    Qed.

    Polymorphic Definition transitivity {A B} (f g h: hom A B) : eq f g -> eq g h -> eq f h.
    Proof using Type.
      intros p q.
      destruct p as [H0 H1].
      destruct q as [H2 H3].
      split.
      all: try rewrite H0, H2; try rewrite H1, H3; reflexivity.
    Qed.

    Polymorphic Instance eq_Equivalence A B: Equivalence (@eq A B) := {
      Equivalence_Reflexive := reflexivity ;
      Equivalence_Symmetric := symmetry ;
      Equivalence_Transitive := transitivity ;
    }.

    Polymorphic Definition Isomorphism: Category.
    exists object hom @id @compose @eq.
    1: apply eq_Equivalence.
    all: unfold eq, compose ; cbn.
    - intros.
      split.
      all: rewrite compose_assoc ; reflexivity.
    - intros.
      split.
      + rewrite compose_id_left.
        reflexivity.
      + rewrite compose_id_right.
        reflexivity.
    - intros.
      split.
      + rewrite compose_id_right.
        reflexivity.
      + rewrite compose_id_left.
        reflexivity.
    - intros ? ? ? ? ? ? ? p q.
      destruct p, q.
      split.
      + rewrite H0, H2.
        reflexivity.
      + rewrite H1, H3.
        reflexivity.
    Defined.
  End iso.
End Isomorphism.

Definition Isomorphism: Category -> Category := Isomorphism.Isomorphism.

Module IsomorphismNotations.
  Notation "A <~> B" := ((A: @object (Isomorphism _)) ~> (B: @object (Isomorphism _))).
End IsomorphismNotations.

Module Functor.
  (* FIXME laws ? *)
  Section functor.
    Polymorphic Variables K L : Category.

    Polymorphic Cumulative Record functor := {
      fobj: @object K -> @object L ;
      fmap {A B}: A ~> B -> fobj A ~> fobj B ;

      fmap_composes {A B C} (f: B ~> C) (g: A ~> B): fmap f ∘ fmap g == fmap (f ∘ g) ;

      fmap_id {A}: fmap (@id _ A) == id ;
      fmap_compat {A B} (f f': A ~> B): f == f' -> fmap f == fmap f' ;
    }.

    Polymorphic Definition hom (A B: functor) := forall x, fobj A x ~> fobj B x.

    Polymorphic Definition id {A}: hom A A := fun _ => id.
    Polymorphic Definition compose {A B C} (f: hom B C) (g: hom A B): hom A C := fun _ => (f _) ∘ (g _).

    Polymorphic Definition eq {A B} (f g: hom A B): Prop := forall x, f x == g x.

    Polymorphic Instance eq_Equivalence A B: Equivalence (@eq A B).
    exists.
    all: unfold Reflexive, Symmetric, Transitive, compose, id, hom, eq ; cbn.
    - intros.
      reflexivity.
    - intros ? ? p t.
      rewrite (p t).
      reflexivity.
    - intros ? ? ? p q t.
      rewrite (p t), (q t).
      reflexivity.
    Qed.

    Polymorphic Definition Functor: Category.
    exists functor hom @id @compose @eq.
    all: unfold compose, id, hom, eq ; cbn.
    1: apply eq_Equivalence.
    - intros.
      rewrite compose_assoc.
      reflexivity.
    - intros.
      rewrite compose_id_left.
      reflexivity.
    - intros.
      rewrite compose_id_right.
      reflexivity.
    - intros ? ? ? ? ? ? ? p q t.
      rewrite (p t), (q t).
      reflexivity.
    Defined.
  End functor.
End Functor.

Definition Functor: Category -> Category -> Category := Functor.Functor.

Polymorphic Add Parametric Morphism C D A B (F: @object (Functor C D)) : (Functor.fmap _ _ F)
    with signature (@equal _ A B) ==> equal as fmap_mor.
Proof.
  intros.
  apply Functor.fmap_compat.
  apply H.
Qed.

Module cat.
  Import Functor.
  Import Isomorphism.
  Import IsomorphismNotations.

  Polymorphic Definition hom (A B: Category) := @object (Functor A B).

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
  exists (fun x => fobj _ _ F (fobj _ _ G x)) (fun __ _ x => fmap _ _ F (fmap _ _ G x)).
  - intros.
    symmetry.
    rewrite -> (fmap_composes _ _ F).
    rewrite -> (fmap_composes _ _ G).
    reflexivity.
  - intros.
    rewrite fmap_id, fmap_id.
    reflexivity.
  - intros ? ? ? ? p.
    rewrite p.
    reflexivity.
  Defined.

  (* FIXME define propositional truncation elsewhere *)
  Polymorphic Definition eq {A B} (f g: hom A B) := | f <~> g |.

  Polymorphic Instance eq_Equivalence A B: Equivalence (@eq A B).
  exists.
  all: unfold Reflexive, Symmetric, Transitive, compose, id, hom ; cbn.
  - intros f.
    exists.
    exists Category.id Category.id.
    all: rewrite compose_id_left ; reflexivity.
  - intros ? ? p.
    destruct p.
    exists.
    exists (from _ _ X) (to _ _ X).
    + apply (from_to _ _ X).
    + apply (to_from _ _ X).
  - intros ? ? ? p q.
    destruct p, q.
    exists.
    apply (X0 ∘ X).
  Qed.

  Polymorphic Definition compose_compat {A B C : Category} (f f' : hom B C) (g g' : hom A B):
    eq f f' ->
    eq g g' ->
    eq (compose f g) (compose f' g').
  intros p q.
  destruct p as [p], q as [q].
  exists.
  exists
    (fun x => fmap _ _ f' (to _ _ q x) ∘ to _ _ p (fobj _ _ g x))
    (fun x => from _ _ p (fobj A B g x) ∘ fmap _ _ f' (from _ _ q x)).
  - cbn.
    intro x.
    unfold Functor.eq, Functor.id, Functor.compose, Functor.hom ; cbn.
    rewrite <- (compose_assoc _ (to _ _ p _)).
    rewrite (compose_assoc _ (from _ _ p _)).
    set (p' := to_from _ _ p (fobj _ _ g x)).
    set (q' := to_from _ _ q x).
    cbn in p', q'.
    unfold Functor.eq, Functor.id, Functor.compose, Functor.hom in p', q'; cbn in p', q'.
    rewrite p'.
    rewrite compose_id_left.
    rewrite fmap_composes.
    rewrite q'.
    rewrite fmap_id.
    reflexivity.
  - intro x.
    unfold Functor.eq, Functor.id, Functor.compose, Functor.hom ; cbn.
    unfold Functor.eq, Functor.id, Functor.compose, Functor.hom ; cbn.
    rewrite compose_assoc.
    setoid_replace
      ((from _ _ p (fobj _ _ g x) ∘ fmap _ _ f' (from _ _ q x))
         ∘ fmap _ _ f' (to _ _ q x))
      with
        (from _ _ p (fobj _ _ g x) ∘ fmap _ _ f' (from _ _ q x ∘ to _ _ q x)).
    2: {
      rewrite <- compose_assoc.
      rewrite fmap_composes.
      reflexivity.
    }
    set (p' := from_to _ _ p (fobj _ _ g x)).
    set (q' := from_to _ _ q x).
    rewrite q'.
    rewrite fmap_id.
    rewrite compose_id_right.
    rewrite p'.
    cbn.
    unfold Functor.id.
    reflexivity.
  Qed.

  Polymorphic Definition cat: Category.
  exists Category hom @id @compose @eq.
  1: apply eq_Equivalence.
  all: cbn; unfold Functor.eq, Functor.id, Functor.compose, Functor.hom, compose ; cbn.
  - intros ? ? f g h.
    exists.
    eexists.
    Unshelve.
    all: cbn; unfold Functor.eq, Functor.id, Functor.compose, Functor.hom, compose ; cbn.
    3: {
      intro t.
      cbn.
      apply Category.id.
    }
    3: {
      intro t.
      cbn.
      apply Category.id.
    }
    cbn.
    all: intro ; rewrite compose_id_left ; reflexivity.
  - intros ? ? ?.
    exists.
    eexists.
    Unshelve.
    3: {
      unfold compose, id, Functor.hom ; cbn.
      intro.
      cbn.
      apply Category.id.
    }.
    3: {
      unfold compose, id, Functor.hom ; cbn.
      intro.
      cbn.
      apply Category.id.
    }
    all: intros ?; cbn; unfold Functor.id, Functor.compose, compose ; cbn ; rewrite compose_id_left ; reflexivity.
  - intros A B f.
    exists.
    unfold compose, id, Functor.hom ; cbn.
    eexists.
    Unshelve.
    3: {
      cbn.
      unfold hom.
      intro x.
      cbn.
      apply Category.id.
    }
    3: {
      cbn.
      unfold hom.
      intro x.
      cbn.
      apply Category.id.
    }
    all: intros ?; cbn; unfold Functor.id, Functor.compose, compose ; cbn ; rewrite compose_id_left ; reflexivity.
  - apply @compose_compat.
  Defined.
End cat.

Polymorphic Definition cat: Category := cat.cat.

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
    where "A => B" := (hom A B) ;

    id {A}: I ~> (A => A) ;
    compose {A B C}: (B => C) ⊗ (A => B) ~> (A => C) ;

    (* Not going to do this laws yet *)
  }.

  Module EnrichedNotations.
    Infix "=>" := hom.
  End EnrichedNotations.
End Enriched.

(* We need Bishop sets (AKA setoids) not Coq's Type to make the Yoneda
embedding on presheafs work properly *)
Module Bishop.
  Polymorphic Cumulative Record bishop_set := {
    type: Type ;
    eqv: type -> type -> Prop ;
    is_eqv: @Equivalence type eqv
  }.

  Polymorphic Instance eq_bishop (A: bishop_set) : @Equivalence (type A) (eqv _) := is_eqv A.

  Polymorphic Cumulative Record hom A B := {
    oper: type A -> type B;
    oper_compat x y: eqv _ x y -> eqv _ (oper x) (oper y);
  }.

  Polymorphic Add Parametric Morphism A B (f: hom A B) : (oper A B f)
      with signature (eqv _) ==> (eqv _) as oper_mor.
  Proof.
    intros x y p.
    apply oper_compat.
    apply p.
  Qed.

  Polymorphic Definition id {A} : hom A A.
  exists (fun x => x).
  intros; auto.
  Defined.

  Polymorphic Definition compose {A B C} (f: hom B C) (g: hom A B): hom A C.
  exists (fun x => oper _ _ f (oper _ _ g x)).
  destruct f, g.
  intros; auto.
  Defined.

  Polymorphic Definition eq {A B} (f g: hom A B): Prop :=
    forall x,
      eqv B (oper _ _ f x) (oper _ _ g x).

  Polymorphic Definition reflexivity {A B} (f: hom A B): eq f f.
  Proof using Type.
    intros x.
    destruct B.
    destruct f.
    reflexivity.
  Qed.

  Polymorphic Definition symmetry {A B} (f g: hom A B): eq f g -> eq g f.
  Proof using Type.
    unfold eq.
    intros p s.
    destruct B.
    destruct f, g; cbn.
    symmetry.
    apply p.
  Qed.

  Polymorphic Definition transitivity {A B} (f g h: hom A B): eq f g -> eq g h -> eq f h.
  Proof using Type.
    unfold eq.
    intros p q s.
    destruct B, f, g, h.
    rewrite (p s).
    rewrite (q s).
    reflexivity.
  Qed.

  Polymorphic Instance eq_Equivalence A B: Equivalence (@eq A B) := {
    Equivalence_Reflexive := reflexivity ;
    Equivalence_Symmetric := symmetry ;
    Equivalence_Transitive := transitivity ;
  }.

  Polymorphic Definition compose_assoc {X Y Z W} (f: hom Z W) (g: hom Y Z) (h: hom X Y): eq (compose f (compose g h)) (compose (compose f g) h).
  Proof using Type.
    unfold eq, compose.
    intro x.
    destruct X, Y, Z, W, f, g, h.
    reflexivity.
  Qed.

  Polymorphic Definition compose_id_left {A B} (f: hom A B): eq (compose id f) f.
  Proof using Type.
    unfold eq, compose, id.
    intro.
    destruct B, f.
    reflexivity.
  Qed.

  Polymorphic Definition compose_id_right {A B} (f: hom A B): eq (compose f id) f.
  Proof using Type.
    unfold eq, compose, id.
    intro.
    destruct B, f.
    reflexivity.
  Qed.

  Polymorphic Definition compose_compat {A B C} (f f': hom B C) (g g': hom A B):
    eq f f' -> eq g g' -> eq (compose f g) (compose f' g').
  Proof using Type.
    unfold eq.
    intros p q x.
    cbn.
    cbn in p, q.
    rewrite p, q.
    reflexivity.
  Defined.

  Polymorphic Definition Bishop_Set: @object cat.
  exists bishop_set hom @id @compose @eq.
  1: apply eq_Equivalence.
  - apply @compose_assoc.
  - apply @compose_id_left.
  - apply @compose_id_right.
  - apply @compose_compat.
  Defined.
End Bishop.

Polymorphic Definition Bishop_Set := Bishop.Bishop_Set.

Module Opposite.
  Section opposite.
    Polymorphic Context `(Category).

    Polymorphic Definition hom (A B: object) := B ~> A.

    Polymorphic Definition id {A} : hom A A := id.
    Polymorphic Definition compose {A B C} : hom B C -> hom A B -> hom A C := fun f g => g ∘ f.

    Polymorphic Definition eq {A B} (f g: hom A B) := f == g.

    Polymorphic Instance eq_Equivalence A B: Equivalence (@eq A B).
    exists.
    all: unfold Reflexive, Symmetric, Transitive, compose, id, hom, eq ; intros; cbn.
    - reflexivity.
    - rewrite H0.
      reflexivity.
    - rewrite H0, H1.
      reflexivity.
    Qed.

    Polymorphic Definition op: Category.
    exists object hom @id @compose @eq.
    1: apply eq_Equivalence.
    all: unfold hom, eq, compose, id; intros; cbn.
    - rewrite compose_assoc.
      reflexivity.
    - rewrite compose_id_right.
      reflexivity.
    - rewrite compose_id_left.
      reflexivity.
    - rewrite H0, H1.
      reflexivity.
    Defined.
  End opposite.
End Opposite.

Polymorphic Definition op: @object cat -> @object cat := Opposite.op.

Module Over.
  Section over.
    Polymorphic Context `(Category).
    Polymorphic Variable c : object.

    Polymorphic Cumulative Record bundle := {
      dom : object ;
      proj: dom ~> c ;
    }.

    (* I really could just use an ordinary sigma type but it makes the
    types messier down the line *)
    Polymorphic Cumulative Record hom A B := {
      slice: dom A ~> dom B;
      commutes: proj B ∘ slice == proj A
    }.

    Polymorphic Definition eq {A B} (f g: hom A B) := slice _ _ f == slice _ _ g.

    Polymorphic Instance eq_Equivalence A B: Equivalence (@eq A B).
    exists.
    all: unfold Reflexive, Symmetric, Transitive, eq.
    - intro.
      reflexivity.
    - intro.
      symmetry.
      apply H0.
    - intros ? ? ? p q.
      rewrite p, q.
      reflexivity.
    Qed.

    Polymorphic Definition id {A} : hom A A.
    exists id.
    apply compose_id_right.
    Defined.

    Polymorphic Definition compose {X Y Z} : hom Y Z -> hom X Y -> hom X Z.
    intros f g.
    exists ((let (f', _) := f in f') ∘ (let (g', _) := g in g')).
    rewrite -> compose_assoc.
    destruct f, g.
    cbn.
    rewrite <- commutes1.
    rewrite <- commutes0.
    reflexivity.
    Defined.

    Polymorphic Definition compose_assoc {X Y Z W} (f: hom Z W) (g: hom Y Z) (h: hom X Y): eq (compose f (compose g h)) (compose (compose f g) h).
    Proof using Type.
      destruct f, g, h.
      unfold eq.
      cbn.
      rewrite -> compose_assoc.
      reflexivity.
    Qed.

    Polymorphic Definition compose_id_left A B (f: hom A B): eq (compose id f) f.
    Proof using Type.
      unfold eq.
      cbn.
      rewrite -> compose_id_left.
      reflexivity.
    Qed.

    Polymorphic Definition compose_id_right {A B} (f: hom A B): eq (compose f id) f.
    Proof using Type.
      unfold eq.
      cbn.
      rewrite -> compose_id_right.
      reflexivity.
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

    Polymorphic Definition over : @object cat.
    exists bundle hom @id @compose @eq.
    1: apply eq_Equivalence.
    - apply @compose_assoc.
    - apply @compose_id_left.
    - apply @compose_id_right.
    - apply @compose_compat.
    Defined.
  End over.
End Over.

(* FIXME Isolate this notation *)
Notation "C / c" := (Over.over C c).

(* FIXME not really all total orders, need a better name. *)
Module Relation.
  Section relation.
    Polymorphic Variable S: Type.
    Polymorphic Variable rel : relation S.
    Polymorphic Context `(reflexive: Reflexive _ rel) `(transitive: Transitive _ rel).

    Polymorphic Definition compose {A B C} (f: rel B C) (g: rel A B): rel A C := transitive _ _ _ g f.

    Polymorphic Definition eq {A B} (_ _: rel A B) := True.

    Polymorphic Instance eq_Equivalence A B : Equivalence (@eq A B).
    exists.
    all: intros; cbn; unfold eq; auto.
    Qed.

    Polymorphic Definition relation: @object cat.
      exists S rel reflexive @compose @eq.
      1: apply eq_Equivalence.
      all: intros; cbn; unfold eq; auto.
    Defined.
  End relation.
End Relation.

Definition relation := Relation.relation.

(* Category of finite totally ordered sets *)
Module Finite.
  Instance le_Reflexive: Reflexive le.
  auto.
  Qed.

  Instance le_Transitive: Transitive le.
  intros ? ? ? f g.
  induction g.
  - apply f.
  - auto.
  Qed.

  Definition finite N := relation _ le _ _/N.
End Finite.

Definition finite := Finite.finite.

(* FIXME Isolate notations *)
Notation "[ N ]" := (finite N).

Definition one := [0].

Definition source C: @object [C].
  exists 0.
  cbn.
  induction C.
  - auto.
  - auto.
Defined.
Definition target C: @object [C] := {| Over.proj := id |}.

Definition I := [1].
Definition walk {C}: source C ~> target C.
  cbn.
  eexists.
  Unshelve.
  2: {
    cbn.
    apply source.
  }
  cbn.
  unfold Relation.eq.
  auto.
Defined.

(* Define the simplex category *)
Module Simplex.
  Definition hom (A B: nat) := [A] ~> [B].

  Definition id {A}: hom A A := id.
  Definition compose {A B C} (f: hom B C) (g: hom A B): hom A C := f ∘ g.

  Definition eq {A B} (f g: hom A B) := f == g.

  Instance eq_Equivalence A B: Equivalence (@eq A B).
  exists.
  all: unfold Reflexive, Symmetric, Transitive, compose, id, hom, eq ; intros; cbn.
  - reflexivity.
  - rewrite H.
    reflexivity.
  - rewrite H, H0.
    reflexivity.
  Qed.

  Definition Δ: @object cat.
    exists nat hom @id @compose @eq.
    1: apply eq_Equivalence.
    all: unfold hom, eq, compose, id; intros.
    - rewrite compose_assoc.
      reflexivity.
    - apply compose_id_left.
    - apply compose_id_right.
    - rewrite H, H0.
      reflexivity.
  Defined.
End Simplex.

Definition Δ: @object cat := Simplex.Δ.

Module Empty.
  Definition hom (A B: Empty_set) := Empty_set.

  Definition id {A}: hom A A := A.
  Definition compose {A B C} (f: hom B C) (g: hom A B): hom A C := A.

  Definition eq {A B} (f f': hom A B) := True.

  Instance eq_Equivalence A B : Equivalence (@eq A B).
  exists.
  all: unfold Reflexive, Symmetric, Transitive, compose, id, hom, eq ; intros; cbn.
  all: auto.
  Qed.

  Definition Empty: @object cat.
    exists Empty_set hom @id @compose @eq.
    1: apply eq_Equivalence.
    all: intros; unfold eq; auto.
  Defined.
End Empty.

Notation Empty := Empty.Empty.

Polymorphic Definition presheaf K: @object cat := Functor (op K) Bishop_Set.

Module Diagrams.
  Import Functor.

  Section diagrams.
    Polymorphic Context {C:@object cat}.

    Polymorphic Definition Empty: op Empty ~> C.
    eexists _ _.
    Unshelve.
    3: {
      intro x.
      destruct x.
    }
    3: {
      intro A.
      destruct A.
    }
    - intro A.
      destruct A.
    - intro A.
      destruct A.
    - intro.
      destruct A.
    Defined.

    Polymorphic Definition Constant (c: @object C): op one ~> C.
    eexists _ _.
    Unshelve.
    4: {
      intro x.
      apply c.
    }
    4: {
      intros A B f.
      cbn.
      apply Category.id.
    }
    all: intros; cbn.
    1: rewrite compose_id_left.
    all: reflexivity.
    Defined.
  End diagrams.
End Diagrams.

Module Presheaf.
  Import Monoidal.
  Import MonoidalNotations.
  Import Functor.

  Polymorphic Definition limit'' {C D} (F: op D ~> C)  (c: @object C): @object Bishop_Set.
  exists (forall t, c ~> fobj _ _ F t) (fun x y => forall t, x t == y t).
  exists.
  - intros x t.
    reflexivity.
  - intros x y p t.
    rewrite (p t).
    reflexivity.
  - intros x y z p q t.
    rewrite (p t), (q t).
    reflexivity.
  Defined.

  Polymorphic Definition limit' {C D} (F: op D ~> C) (C: @object C): @object Bishop_Set := limit'' F C.

  Polymorphic Definition limit_map {C D} (F: op D ~> C) {X Y: @object (op C)} (f: X ~> Y): limit' X ~> limit' Y.
  cbn in f, X, Y.
  unfold Opposite.hom in f.
  eexists _.
  Unshelve.
  2: {
    intros x t.
    set (x' := x t).
    apply (x' ∘ f).
  }
  intros x y p.
  cbn.
  intros.
  cbn in p.
  rewrite (p t).
  reflexivity.
  Defined.

  Polymorphic Definition limit: @object (presheaf C).
  set (limit'' := limit' : @object (op C) -> @object Bishop_Set).
  exists limit'' @limit_map.
  - intros X Y Z f g s t.
    unfold limit_map.
    cbn.
    unfold Opposite.compose.
    rewrite compose_assoc.
    reflexivity.
  - intros X Y f f' p s t.
    unfold limit_map.
    cbn in p.
    unfold Opposite.eq in p.
    cbn.
    rewrite p.
    reflexivity.
  Defined.

Polymorphic Definition unit {C}: @object (presheaf C) :=
  limit Diagrams.Empty.

Polymorphic Definition bang {C} (A: @object (presheaf C)): A ~> unit.
intro t.
eexists.
Unshelve.
2: {
  intro p.
  cbn.
  intro B.
  destruct B.
}
intros x y p.
cbn.
intro X.
destruct X.
Defined.

Polymorphic Instance product_Monoid C: Monoidal (presheaf C).
admit.
Admitted.

Section yoneda.
  Polymorphic Variables C:@object cat.

  Polymorphic Definition yo (c: object C) := limit (Diagrams.Constant c).

  Polymorphic Definition yo_map {A B: object C} (f: A ~> B): yo A ~> yo B.
  intros X.
  eexists.
  Unshelve.
  2: {
    cbn.
    intros x ?.
    apply (f ∘ x (target _)).
  }
  intros x y.
  intro p.
  cbn.
  intros ?.
  cbn in p.
  rewrite (p (target _)).
  reflexivity.
  Defined.

  (* Because of universe weirdness we need a more awkward type
      signature than we should *)
  Polymorphic Definition Yo: object (Functor C (presheaf C)).
  exists yo @yo_map.
  - intros X Y Z f g ? ? ?; cbn.
    rewrite compose_assoc.
    reflexivity.
  - intros X Y f f' p ? ? ?; cbn.
    rewrite p.
    reflexivity.
  Defined.
End yoneda.

End Presheaf.

Polymorphic Definition sSet := presheaf Δ.

Polymorphic Definition InfinityCategory := Enriched.Category sSet (Presheaf.product_Monoid _).
