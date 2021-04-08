Require Import Coq.Setoids.Setoid.

(* Seems to make classes go faster? *)
Set Primitive Projections.
Unset Printing Primitive Projection Parameters.

Reserved Notation "| A |" (at level 40).

Reserved Notation "∈ C" (at level 1).
Reserved Notation "F ⊗ X" (at level 30).

Reserved Notation "A ~> B" (at level 80).
Reserved Notation "A ∘ B" (at level 30).
Reserved Notation "A == B" (at level 70).

Reserved Notation "A <~> B" (at level 80).
(* Reserved Notation "A ⊗ B" (at level 30). *)
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
    Notation "∈ C" := (@object C).
    Notation "A ~> B" := (hom A B).
    Notation "f ∘ g" := (compose f g).
    Notation "f == g" := (equal f g).
  End CategoryNotations.

  Polymorphic Instance eq_cat C (A B: ∈ C) : @Equivalence (hom A B) equal := is_eqv _ _.

  Polymorphic Add Parametric Morphism K (A B C: ∈ K) : (@compose _ A B C)
      with signature equal ==> equal ==> equal as compose_mor.
  Proof.
    intros ? ? p ? ? q.
    apply compose_compat.
    + apply p.
    + apply q.
  Qed.
End Category.

Module Isomorphism.
  Polymorphic Cumulative Class hom `{Category} (A B: object) := {
    to: A ~> B ;
    from: B ~> A ;
    to_from: to ∘ from == id ;
    from_to: from ∘ to == id ;
  }.

  Section iso.
    Polymorphic Context `(Category).

    Polymorphic Definition id {A: object}: hom A A.
    exists id id.
    - apply compose_id_left.
    - apply compose_id_right.
    Defined.

    Polymorphic Definition compose {A B C: object} (f: hom B C) (g: hom A B): hom A C.
    exists (to ∘ to) (from ∘ from).
    - rewrite <- compose_assoc.
      rewrite -> (compose_assoc (@to _ _ _ g)).
      rewrite to_from.
      rewrite compose_id_left.
      rewrite to_from.
      reflexivity.
    - rewrite <- compose_assoc.
      rewrite -> (compose_assoc (@from _ _ _ f)).
      rewrite from_to.
      rewrite compose_id_left.
      rewrite from_to.
      reflexivity.
    Defined.

    Polymorphic Definition eq {A B: object} (f g: hom A B) : Prop := @to _ _ _ f == @to _ _ _ g /\ @from _ _ _ f == @from _ _ _ g.

    Polymorphic Instance eq_Equivalence A B: Equivalence (@eq A B).
    exists.
    - split.
      all: reflexivity.
    - intros ? ? p.
      destruct p as [H0 H1].
      split.
      all: try rewrite H0; try rewrite H1; reflexivity.
    - intros ? ? ? p q.
      destruct p as [H0 H1].
      destruct q as [H2 H3].
      split.
      all: try rewrite H0, H2; try rewrite H1, H3; reflexivity.
    Qed.

    Polymorphic Definition Isomorphism: Category.
    exists object hom @id @compose @eq.
    1: apply eq_Equivalence.
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
        * apply H0.
        * apply H2.
      + apply compose_compat.
        * apply H3.
        * apply H1.
    Defined.
  End iso.

  Module IsomorphismNotations.
    Notation "A <~> B" := ((A: ∈ (Isomorphism _)) ~> (B: ∈ (Isomorphism _))).
  End IsomorphismNotations.

  Import IsomorphismNotations.

  Polymorphic Definition transpose {C} {A B: ∈ C} (f: A <~> B): B <~> A.
  exists (@from _ _ _ f) (@to _ _ _ f).
  - apply from_to.
  - apply to_from.
  Defined.
End Isomorphism.

Definition Isomorphism: Category -> Category := Isomorphism.Isomorphism.

Module Functor.
  Polymorphic Cumulative Class functor (K L: Category) := {
    fobj: ∈ K -> ∈ L ;
    map {A B}: A ~> B -> fobj A ~> fobj B ;

    map_composes {A B C} (f: B ~> C) (g: A ~> B): map f ∘ map g == map (f ∘ g) ;

    map_id {A}: map (@id _ A) == id ;
    map_compat {A B} (f f': A ~> B): f == f' -> map f == map f' ;
  }.

  Module FunctorNotations.
    Notation "F ⊗ A" := (@fobj _ _ F A).
  End FunctorNotations.

  Import FunctorNotations.

  Section functor.
    Polymorphic Variables K L : Category.

    Polymorphic Definition hom (A B: functor K L) := forall x, A ⊗ x ~> B ⊗ x.

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
    exists (functor _ _) hom @id @compose @eq.
    all: unfold compose, id, hom, eq ; cbn.
    1: apply eq_Equivalence.
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
End Functor.

Definition Functor: Category -> Category -> Category := Functor.Functor.

Polymorphic Add Parametric Morphism C D A B (F: ∈ (Functor C D)) : (@Functor.map _ _ F _ _)
    with signature (@equal _ A B) ==> equal as map_mor.
Proof.
  intros.
  apply Functor.map_compat.
  apply H.
Qed.

Module cat.
  Import Functor.
  Import FunctorNotations.
  Import Isomorphism.
  Import IsomorphismNotations.

  Polymorphic Definition hom (A B: Category) := ∈ (Functor A B).

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
  exists (fun x => F ⊗ (G ⊗ x)) (fun _ _ x => map (map x)).
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

  Polymorphic Definition eq {A B} (f g: hom A B) := | f <~> g |.

  Polymorphic Instance eq_Equivalence A B: Equivalence (@eq A B).
  exists.
  all: unfold Reflexive, Symmetric, Transitive, compose, id, hom ; cbn.
  - intros f.
    unfold eq.
    exists.
    apply Category.id.
  - intros ? ? p.
    destruct p as [p].
    exists.
    apply Isomorphism.transpose.
    apply p.
  - intros ? ? ? p q.
    destruct p as [p], q as [q].
    exists.
    apply (q ∘ p).
  Qed.

  Polymorphic Definition compose_compat {A B C : Category} (f f' : hom B C) (g g' : hom A B):
    eq f f' ->
    eq g g' ->
    eq (compose f g) (compose f' g').
  intros p q.
  destruct p as [p], q as [q].
  exists.
  exists
    (fun x => map (@to _ _ _ q x) ∘ @to _ _ _ p (g ⊗ x))
    (fun x => @from _ _ _ p (g ⊗ x) ∘ map (@from _ _ _ q x)).
  - cbn.
    intro x.
    unfold Functor.eq, Functor.id, Functor.compose, Functor.hom ; cbn.
    rewrite <- (compose_assoc _ (@to _ _ _ p _)).
    rewrite (compose_assoc _ (@from _ _ _ p _)).
    set (p' := @to_from _ _ _ p (@fobj _ _ g x)).
    set (q' := @to_from _ _ _ q x).
    cbn in p', q'.
    unfold Functor.eq, Functor.id, Functor.compose, Functor.hom in p', q'; cbn in p', q'.
    rewrite p'.
    rewrite compose_id_left.
    rewrite map_composes.
    rewrite q'.
    rewrite map_id.
    reflexivity.
  - intro x.
    unfold Functor.eq, Functor.id, Functor.compose, Functor.hom ; cbn.
    unfold Functor.eq, Functor.id, Functor.compose, Functor.hom ; cbn.
    rewrite compose_assoc.
    setoid_replace
      ((@from _ _ _ p (fobj x) ∘ map (@from _ _ _ q x))
         ∘ map (@to _ _ _ q x))
      with
        (@from _ _ _ p (fobj x) ∘ map (@from _ _ _ q x ∘ @to _ _ _ q x)).
    2: {
      rewrite <- compose_assoc.
      rewrite map_composes.
      reflexivity.
    }
    set (p' := @from_to _ _ _ p (@fobj _ _ g x)).
    set (q' := @from_to _ _ _ q x).
    rewrite q'.
    rewrite map_id.
    rewrite compose_id_right.
    rewrite p'.
    cbn.
    unfold Functor.id.
    reflexivity.
  Qed.

  Polymorphic Definition cat: Category.
  exists Category hom @id @compose @eq.
  1: apply eq_Equivalence.
  - intros ? ? ? ? ? ? ?.
    exists.
    exists (fun _ => Category.id) (fun _ => Category.id).
    all: cbn; intro; apply compose_id_left.
  - intros ? ? ?.
    exists.
    exists (fun _ => Category.id) (fun _ => Category.id).
    all: cbn; intro; apply compose_id_left.
  - intros ? ? ?.
    exists.
    exists (fun _ => Category.id) (fun _ => Category.id).
    all: cbn; intro; apply compose_id_left.
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
    where "A => B" := (hom A B) ;

    id {A}: I ~> (A => A) ;
    compose {A B C}: (B => C) ⊗ (A => B) ~> (A => C) ;

    (* Not going to do this laws yet *)
  }.

  Module EnrichedNotations.
    Infix "=>" := hom.
  End EnrichedNotations.
End Enriched.

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

    Polymorphic Definition relation: Category.
      exists S rel reflexive @compose @eq.
      1: apply eq_Equivalence.
      all: intros; cbn; unfold eq; auto.
    Defined.
  End relation.
End Relation.

Polymorphic Definition relation := Relation.relation.

(* We need Bishop sets (AKA setoids) not Coq's Type to make the Yoneda
embedding on presheafs work properly *)

Module Bishop.
  Polymorphic Cumulative Record bishop_set := {
    type: Type ;
    eqv: type -> type -> Prop ;
    is_eqv: @Equivalence type eqv
  }.

  Polymorphic Instance eq_bishop (A: bishop_set) : @Equivalence (type A) (eqv _) := is_eqv A.

  Polymorphic Definition Bishop_Eqv (A: bishop_set): Category.
  apply (@Relation.relation (type A) (eqv A)).
  - apply is_eqv.
  - apply is_eqv.
  Defined.

  Polymorphic Definition hom A B := (Bishop_Eqv A: @object cat) ~> (Bishop_Eqv B).

  Polymorphic Definition id {A}: hom A A := id.

  Polymorphic Definition compose {A B C} (f: hom B C) (g: hom A B): hom A C := f ∘ g.

  Polymorphic Definition eq {A B} (f g: hom A B): Prop := f == g.
  Polymorphic Instance eq_Equivalence A B: Equivalence (@eq A B).
  exists.
  - intros ?.
    reflexivity.
  - intros ? ? p.
    rewrite p.
    reflexivity.
  - intros ? ? ? p q.
    rewrite p, q.
    reflexivity.
  Qed.

  Polymorphic Definition Bishop_Set: Category.
  exists bishop_set hom @id @compose @eq.
  1: apply eq_Equivalence.
  all: unfold eq, hom, compose; intros.
  - apply compose_assoc.
  - apply compose_id_left.
  - apply compose_id_right.
  - apply compose_compat.
    + apply H.
    + apply H0.
  Defined.
End Bishop.

Polymorphic Definition Bishop_Eqv := Bishop.Bishop_Eqv.
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

Polymorphic Definition op: Category -> Category := Opposite.op.

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
    exists (slice _ _ f ∘ slice _ _ g).
    rewrite compose_assoc.
    rewrite (commutes _ _ f).
    apply (commutes _ _ g).
    Defined.

    Polymorphic Definition compose_assoc {X Y Z W} (f: hom Z W) (g: hom Y Z) (h: hom X Y): eq (compose f (compose g h)) (compose (compose f g) h).
    Proof using Type.
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

    Polymorphic Definition over : Category.
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

Definition source C: ∈ [C].
  exists 0.
  cbn.
  induction C.
  - auto.
  - auto.
Defined.
Definition target C: ∈ [C] := {| Over.proj := id |}.

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
  Definition hom (A B: nat) := ([A]: ∈ cat) ~> [B].

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

  Definition Δ: Category.
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

Definition Δ: Category := Simplex.Δ.

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

  Definition Empty: Category.
    exists Empty_set hom @id @compose @eq.
    1: apply eq_Equivalence.
    all: intros; unfold eq; auto.
  Defined.
End Empty.

Notation Empty := Empty.Empty.

Polymorphic Definition presheaf K: Category := Functor (op K) Bishop_Set.

Module Diagrams.
  Import Functor.

  Section diagrams.
    Polymorphic Context {C:Category}.

    Polymorphic Definition Empty: (op Empty: ∈ cat) ~> C.
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

    Polymorphic Definition Constant (c: ∈ C): (op one: ∈ cat) ~> C.
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

  Section limits.
    Polymorphic Context {C D: Category}.
    Polymorphic Context `(@functor (op D) C).

    Polymorphic Definition limit' (c: ∈ C): ∈ Bishop_Set.
    exists (forall t, c ~> fobj t) (fun x y => forall t, x t == y t).
    exists.
    - intros ? ?.
      reflexivity.
    - intros x y p t.
      symmetry.
      apply (p t).
    - intros x y z p q t.
      rewrite (p t).
      apply (q t).
    Defined.

    Polymorphic Definition limit_map {X Y: ∈ (op C)} (f: X ~> Y): limit' X ~> limit' Y.
    cbn in f, X, Y.
    unfold Opposite.hom in f.
    eexists _ _.
    Unshelve.
    4: {
      intros x t.
      apply (x t ∘ f).
    }
    4: {
      cbn.
      intros.
      rewrite (H0 t).
      reflexivity.
    }
    3: {
      cbn; unfold Relation.eq; cbn.
      intros.
      auto.
    }
    2: {
      cbn; unfold Relation.eq; cbn.
      intro.
      auto.
    }
    cbn; unfold Relation.eq; cbn.
    intros.
    auto.
    Defined.

    Polymorphic Definition limit: ∈ (presheaf C).
    set (limit'' := limit' : ∈ (op C) -> ∈ Bishop_Set).
    exists limit'' @limit_map.
    - intros.
      cbn.
      unfold Opposite.compose.
      exists.
      cbn.
      eexists.
      Unshelve.
      3: {
        intro.
        cbn.
        intro.
        rewrite compose_assoc.
        reflexivity.
      }
      3: {
        cbn.
        intro.
        cbn.
        intro.
        rewrite compose_assoc.
        reflexivity.
      }
      2: {
        cbn.
        intro.
        cbn.
        unfold Relation.eq.
        auto.
      }
      1: {
        cbn.
        intro.
        cbn.
        unfold Relation.eq.
        auto.
      }
    - intros.
      cbn.
      unfold cat.eq.
      exists.
      cbn.
      eexists.
      Unshelve.
      3: {
        cbn.
        intro.
        cbn.
        intro.
        rewrite compose_id_right.
        reflexivity.
      }
      3: {
        cbn.
        intro.
        cbn.
        intro.
        rewrite compose_id_right.
        reflexivity.
      }
      2: {
        cbn.
        intro.
        cbn.
        unfold Relation.eq.
        auto.
      }
      1: {
        cbn.
        intro.
        cbn.
        unfold Relation.eq.
        auto.
      }
    - cbn.
      intros.
      unfold cat.eq.
      exists.
      cbn.
      eexists.
      Unshelve.
      3: {
        cbn.
        intro.
        cbn.
        intro.
        rewrite H0.
        reflexivity.
      }
      3: {
        cbn.
        intro.
        cbn.
        intro.
        rewrite H0.
        reflexivity.
      }
      2: {
        cbn.
        intro.
        cbn.
        unfold Relation.eq.
        auto.
      }
      1: {
        cbn.
        intro.
        cbn.
        unfold Relation.eq.
        auto.
      }
    Defined.
  End limits.

  Polymorphic Definition unit {C}: @object (presheaf C) := limit Diagrams.Empty.

  Polymorphic Definition bang {C} (A: @object (presheaf C)): A ~> unit.
  intro t.
  cbn.
  eexists.
  Unshelve.
  4: {
    intro.
    cbn.
    intro x.
    destruct x.
  }
  4: {
    cbn.
    cbn.
    intro B.
    intro.
    intro.
    intro.
    destruct t0.
  }
  cbn.
  unfold Relation.eq.
  cbn.
  intros.
  auto.
  intros.
  cbn.
  unfold Relation.eq.
  auto.
  intros.
  cbn.
  unfold Relation.eq.
  auto.
  Defined.

  Polymorphic Instance product_Monoid C: Monoidal (presheaf C).
  admit.
  Admitted.

    Section yoneda.
      Polymorphic Variables C:Category.

      Polymorphic Definition yo (c: ∈ C) := limit (Diagrams.Constant c).

      Polymorphic Definition yo_map {A B: ∈ C} (f: A ~> B): yo A ~> yo B.
      intros X.
      eexists.
      Unshelve.
      2: {
        cbn.
        intros ?.
        unfold Relation.eq.
        auto.
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
      Polymorphic Definition Yo: ∈ (Functor C (presheaf C)).
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
