Require Import Coq.Setoids.Setoid.

(* Seems to make classes go faster? *)
Set Primitive Projections.
Unset Printing Primitive Projection Parameters.

Reserved Notation "| A |" (at level 40).

Reserved Notation "A /~ B" (at level 30).
Reserved Notation "∈ B" (at level 30).
Reserved Notation "A ~ B" (at level 70).
Reserved Notation "A == B" (at level 70).

Reserved Notation "A ~> B" (at level 80).
Reserved Notation "A ∘ B" (at level 30).

Reserved Notation "A <~> B" (at level 80).

Reserved Notation "A ⊗ B" (at level 30).
Reserved Notation "A ~~> B" (at level 80).

(* FIXME get propositional truncation from elsewhere *)
Polymorphic Definition id (A: Type) := A.
Polymorphic Variant truncate A: Prop := truncate_intro (_:id A).

Module TruncateNotations.
  Notation "| A |" := (truncate A).

  Coercion truncate_intro: id >-> truncate.
End TruncateNotations.

Import TruncateNotations.

Module Export Foundations.
  Close Scope nat.

  (* We need Bishop sets (AKA Setoids) not Coq's Type to make the Yoneda
     embedding on presheafs work properly *)
  (* The technical jargon is that a Setoid is a 0-trivial groupoid,
     equality is the hom *)

  Polymorphic Cumulative Record span A B := {
    dom: Type ;
    proj1: dom -> A ;
    proj2: dom -> B ;
  }.

  Polymorphic Definition corr A := span A A.

  Polymorphic Definition equiv {A} (c:corr A) x y := {p|proj1 _ _ c p = x /\ proj2 _ _ c p = y}.

  Polymorphic Cumulative Class Reflexive {A} (c: corr A) := {
    reflexive x: equiv c x x
  }.
  Coercion reflexive: Reflexive >-> Funclass.

  Polymorphic Cumulative Class Symmetric {A} (c: corr A) := {
    symmetry x y: equiv c x y -> equiv c y x
  }.
  Coercion symmetry: Symmetric >-> Funclass.

  Polymorphic Cumulative Class Transitive {A} (c: corr A) := {
    transitive x y z:
      equiv c x y -> equiv c y z ->
      equiv c x z
  }.
  Coercion transitive: Transitive >-> Funclass.

  Polymorphic Cumulative Class Groupoid := {
    type: Type ;
    relate: corr type ;
    set_Reflexive :> Reflexive relate ;
    set_Transitive :> Transitive relate ;
    set_Symmetric :> Symmetric relate ;
  }.

  Coercion type: Groupoid >-> Sortclass.

  Polymorphic Definition equal {A:Groupoid} (x y:A) := |equiv (relate (Groupoid:=A)) x y|.

  Module Export SetNotations.
    Notation "∈ A" := (relate (Groupoid := A)).
    Notation "A /~ Q" := {| type := A ; relate := Q |}.
    Notation "A ~ B" := (equiv relate A B).
    Notation "x == y" := (equal x y).
  End SetNotations.

  Polymorphic Definition IsSet (A:Groupoid): Prop := forall (x y: A), (x ~ y) -> x = y.
  Polymorphic Class Setoid := {
    Setoid_Groupoid:> Groupoid ;
    Setoid_IsSet: IsSet Setoid_Groupoid
  }.

  Coercion Setoid_Groupoid: Setoid >-> Groupoid.

  Instance equal_Equivalence (A:Groupoid): Equivalence (@equal A).
  exists.
  - intros x.
    destruct (reflexive x).
    exists.
    exists x0.
    apply a.
  - intros x y p.
    destruct p as [p].
    exists.
    apply (symmetry x y).
    apply p.
  - intros x y z p q.
    destruct p as [p], q as [q].
    exists.
    apply (transitive x y z).
    + apply p.
    + apply q.
  Qed.

  Polymorphic Definition ident (A: Type): Setoid.
  eexists.
  Unshelve.
  2: {
    exists A {| proj1 x := x ; proj2 x := x |}.
    - exists.
      intros.
      exists x.
      split.
      all: auto.
    - exists.
      intros ? ? ? p q.
      destruct p as [p pe], q as [q qe].
      exists p.
      cbn.
      cbn in p, q, pe, qe.
      destruct pe as [pe pe'], qe as [qe qe'].
      split.
      all: auto.
      rewrite pe'.
      rewrite <- qe.
      rewrite qe'.
      reflexivity.
    - exists.
      intros ? ? p.
      destruct p as [p pe].
      exists p.
      cbn.
      cbn in p, pe.
      destruct pe as [pe pe'].
      split.
      all: auto.
  }
  intros ? ? p.
  destruct p as [p pe].
  cbn in p, pe.
  destruct pe as [pe pe'].
  rewrite <- pe, pe'.
  reflexivity.
  Defined.
End Foundations.

Module Export Category.
  Polymorphic Cumulative Class Category := {
    object: Type ;
    hom: object -> object -> Groupoid
    where "A ~> B" := (hom A B) ;

    id {A}: hom A A ;
    compose {A B C}: hom B C -> hom A B -> hom A C
    where "f ∘ g" := (compose f g) ;

    compose_assoc {A B C D} (f: hom C D) (g: hom B C) (h: hom A B):
      (f ∘ (g ∘ h)) == ((f ∘ g) ∘ h );
    compose_id_left {A B} (f: hom A B): (id ∘ f) == f ;
    compose_id_right {A B} (f: hom A B): (f ∘ id) == f ;

    compose_compat {A B C} (f f': hom B C) (g g': hom A B):
      f ~ f' -> g ~ g' -> (f ∘ g) ~ (f' ∘ g') ;
  }.

  Coercion object: Category >-> Sortclass.
  Coercion hom: Category >-> Funclass.

  Module Export CategoryNotations.
    Notation "f ∘ g" := (compose f g).
    Notation "A ~> B" := ((_:Category) A B).
  End CategoryNotations.

  Polymorphic Add Parametric Morphism (K: Category) (A B C: K) : (@compose _ A B C)
      with signature equal ==> equal ==> equal as compose_mor.
  Proof.
    intros ? ? p ? ? q.
    destruct p as [p], q as [q].
    exists.
    apply (compose_compat _ _ _ _ p q).
  Qed.
End Category.

Module Export Functions.
  (* A function is a homeomorphism over equivalence *)
  Polymorphic Class function (C D: Setoid) := {
    app: C -> D ;
    map {A B}: A ~ B -> app A ~ app B ;
  }.

  Coercion app: function >-> Funclass.

  Polymorphic Definition fn C D := ident (function C D).

  Polymorphic Add Parametric Morphism (C D: Setoid) (F: fn C D) : (@app _ _ F)
      with signature equal ==> equal as app_mor.
  Proof.
    intros ? ? p.
    destruct p as [p].
    exists.
    apply map.
    apply p.
  Qed.
End Functions.

Module Sets.
  Polymorphic Definition id {A}: fn A A.
  exists (fun x => x).
  intros ? ? p.
  apply p.
  Defined.

  Polymorphic Definition compose {A B C} (f: fn B C) (g: fn A B): fn A C.
  exists (fun x => f (g x)).
  intros ? ? p.
  apply map.
  apply map.
  apply p.
  Defined.

  Polymorphic Definition set: Category.
  exists Setoid fn @id @compose.
  - intros ? ? ? ? f g h.
    exists.
    exists (compose f (compose g h)).
    cbn.
    split.
    2: reflexivity.
    unfold compose.
    cbn.
    reflexivity.
  - intros ? ? f.
    exists.
    exists (compose id f).
    split.
    2: reflexivity.
    unfold compose.
    cbn.
    reflexivity.
  - intros ? ? f.
    exists.
    exists f.
    split.
    all: reflexivity.
  - intros ? ? ? ? ? ? ? p q.
    destruct p as [p pe], q as [q qe].
    cbn in pe, qe.
    destruct pe, qe.
    rewrite <- H.
    rewrite <- H0.
    rewrite <- H1.
    rewrite <- H2.
    apply reflexive.
  Defined.
End Sets.

Polymorphic Definition set := Sets.set.

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

Polymorphic Definition op: Category -> Category := Opposite.op.

Module Isomorphism.
  Section iso.
    Polymorphic Context `(K:Category).

    Polymorphic Cumulative Class hom' (A B: K) := {
      to: K A B ;
      from: K B A ;
      to_from: to ∘ from == id ;
      from_to: from ∘ to == id ;
    }.

    Polymorphic Definition eq {A B} (f g: hom' A B) : Prop := @to _ _ f == @to _ _ g /\ @from _ _ f == @from _ _ g.

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

    Polymorphic Definition hom A B := {| type := hom' A B; equal := eq |}.

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

  Module IsomorphismNotations.
    Notation "A <~> B" := (Isomorphism _ A B).
  End IsomorphismNotations.

  Import IsomorphismNotations.

  Polymorphic Definition transpose {C:Category} {A B: C} (f: A <~> B): B <~> A.
  exists (@from _ _ _ f) (@to _ _ _ f).
  - apply from_to.
  - apply to_from.
  Defined.
End Isomorphism.

Definition Isomorphism: Category -> Category := Isomorphism.Isomorphism.

Module Export Object.
  Import Isomorphism.
  Import IsomorphismNotations.

  Polymorphic Definition eq {C} (A B: @object C) := | A <~> B |.

  Polymorphic Instance eq_Equivalence A: Equivalence (@eq A).
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

  Polymorphic Definition Object (C: Category) := {| type := C |}.

  Coercion Object: Category >-> Setoid.
End Object.

Module Functor.
  Polymorphic Cumulative Class functor (C D: Category) := {
    fobj: C -> D ;
    map {A B}: C A B -> D (fobj A) (fobj B) ;

    map_composes {X Y Z} (f: C Y Z) (g: C X Y): map f ∘ map g == map (f ∘ g) ;

    map_id {A}: map (@id _ A) == id ;
    map_compat {A B} (f f': C A B): f == f' -> map f == map f' ;
  }.

  Coercion fobj: functor >-> Funclass.

  Section functor.
    Polymorphic Variables K L : Category.

    Polymorphic Definition hom' (A B: functor K L) := forall x, L (A x) (B x).

    Polymorphic Definition eq {A B} (f g: hom' A B): Prop := forall x, f x == g x.

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

    Polymorphic Definition hom A B := {| type := hom' A B |}.

    Polymorphic Definition id {A}: hom A A := fun _ => id.
    Polymorphic Definition compose {A B C} (f: hom B C) (g: hom A B): hom A C := fun _ => (f _) ∘ (g _).

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
End Functor.

Polymorphic Definition Functor: Category -> Category -> Category := Functor.Functor.

Polymorphic Add Parametric Morphism (C D: Category) (A B: C) (F: Functor C D) : (@Functor.map _ _ F A B)
    with signature (@equal _) ==> equal as map_mor.
Proof.
  intros.
  apply Functor.map_compat.
  apply H.
Qed.

Module cat.
  Import Functor.
  Import Isomorphism.
  Import IsomorphismNotations.

  Polymorphic Definition hom (A B: Category): set := Functor A B.

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
  exists (fun x => F (G x)) (fun _ _ x => map (map x)).
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
  Polymorphic Definition compose_compat {A B C : Category} (f f' : hom B C) (g g' : hom A B):
    (f == f') ->
    (g == g') ->
    compose f g == compose f' g'.
  intros p q.
  destruct p as [p], q as [q].
  exists.
  exists
    (fun x => map (@to _ _ _ q x) ∘ @to _ _ _ p (g x))
    (fun x => @from _ _ _ p (g x) ∘ map (@from _ _ _ q x)).
  - cbn.
    intro x.
    unfold Functor.eq, Functor.id, Functor.compose, Functor.hom ; cbn.
    rewrite <- (compose_assoc _ (@to _ _ _ p _)).
    rewrite (compose_assoc _ (@from _ _ _ p _)).
    set (p' := @to_from _ _ _ p (g x)).
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
      ((@from _ _ _ p (g x) ∘ map (@from _ _ _ q x))
         ∘ map (@to _ _ _ q x))
      with
        (@from _ _ _ p (g x) ∘ map (@from _ _ _ q x ∘ @to _ _ _ q x)).
    2: {
      rewrite <- compose_assoc.
      rewrite map_composes.
      reflexivity.
    }
    set (p' := @from_to _ _ _ p (g x)).
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
  exists Category hom @id @compose.
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
    where "A ~~> B" := (hom A B) ;

    id {A}: I ~> (A ~~> A) ;
    compose {A B C}: (B ~~> C) ⊗ (A ~~> B) ~> (A ~~> C) ;

    (* Not going to do this laws yet *)
  }.

  Module EnrichedNotations.
    Infix "~~>" := hom.
  End EnrichedNotations.
End Enriched.

Module Relation.
  Section relation.
    Polymorphic Variable S: Type.
    Polymorphic Variable rel : relation S.
    Polymorphic Context `(reflexive: Reflexive _ rel) `(transitive: Transitive _ rel).

    Polymorphic Definition eq {A B} (_ _: rel A B) := True.

    Polymorphic Instance eq_Equivalence A B : Equivalence (@eq A B).
    exists.
    all: intros; cbn; unfold eq; auto.
    Qed.

    Polymorphic Definition hom (A B: S):= {| type := rel A B; equal := eq |}.

    Polymorphic Definition compose {A B C} (f: rel B C) (g: rel A B): rel A C := transitive _ _ _ g f.
    Polymorphic Definition relation: Category.
      exists S hom reflexive @compose.
      all: intros; cbn; unfold eq; auto.
    Defined.
  End relation.
End Relation.

Polymorphic Definition relation := Relation.relation.

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
    Polymorphic Cumulative Record hom' A B := {
      slice: dom A ~> dom B;
      commutes: proj B ∘ slice == proj A
    }.

    Polymorphic Definition eq {A B} (f g: hom' A B) := slice _ _ f == slice _ _ g.

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

    Polymorphic Definition hom A B := {| type := hom' A B ; equal := eq |}.

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
    exists bundle hom @id @compose.
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

Definition source C: [C].
  exists 0.
  cbn.
  induction C.
  - auto.
  - auto.
Defined.
Definition target C: [C] := {| Over.proj := id |}.

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
  Definition hom (A B: nat): set := ([A]: cat) ~> [B].

  Definition id {A}: hom A A := id.
  Definition compose {A B C} (f: hom B C) (g: hom A B): hom A C := f ∘ g.

  Definition Δ: Category.
    exists nat hom @id @compose.
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
  Definition hom (A: Empty_set): Empty_set -> set := match A with end.

  Definition id {A}: hom A A := match A with end.
  Definition compose {A B C}: hom B C -> hom A B -> hom A C := match A with end.

  Definition Empty: Category.
    exists Empty_set hom @id @compose.
    all: intros; unfold eq, compose, id; cbn; auto.
    - destruct A.
    - destruct A.
    - destruct A.
    - destruct A.
  Defined.
End Empty.

Notation Empty := Empty.Empty.

Polymorphic Definition presheaf K: Category := Functor (op K) set.

Module Diagrams.
  Import Functor.

  Section diagrams.
    Polymorphic Context {C:Category}.

    Polymorphic Definition Empty: (op Empty: cat) ~> C.
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

    Polymorphic Definition Constant (c: C): (op one: cat) ~> C.
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
    Polymorphic Variable F: Functor (op D) C.

    Polymorphic Definition limit' (c: C): set.
    exists (forall t, c ~> F t) (fun x y => forall t, x t == y t).
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

    Polymorphic Definition limit_map {X Y: op C} (f: X ~> Y): limit' X ~> limit' Y.
    cbn in f, X, Y.
    unfold Opposite.hom in f.
    eexists _.
    Unshelve.
    2: {
      intros x t.
      apply (x t ∘ f).
    }
    1: {
      cbn.
      intros.
      rewrite (H t).
      reflexivity.
    }
    Defined.

    Polymorphic Definition limit: presheaf C.
    set (limit'' := limit' : op C -> set).
    exists limit'' @limit_map.
    - intros.
      cbn.
      unfold Opposite.compose.
      intros ? ?.
      cbn.
      rewrite compose_assoc.
      reflexivity.
    - intros ? ? ?.
      cbn.
      apply compose_id_right.
    - intros ? ? ? ? p ? ?.
      cbn.
      rewrite p.
      reflexivity.
    Defined.
  End limits.

  Polymorphic Definition unit {C}: presheaf C := limit Diagrams.Empty.

  Polymorphic Definition bang {C} (A: presheaf C): A ~> unit.
  intro t.
  cbn.
  eexists.
  Unshelve.
  2: {
    intro.
    cbn.
    intro x.
    destruct x.
  }
  1: {
    cbn.
    intro B.
    intro.
    intro.
    intro.
    destruct t0.
  }
  Defined.

  Polymorphic Instance product_Monoid C: Monoidal (presheaf C).
  admit.
  Admitted.

  Section yoneda.
    Polymorphic Variables C:Category.

    Polymorphic Definition yo (c: C) := limit (Diagrams.Constant c).

    Polymorphic Definition yo_map {A B: C} (f: A ~> B): yo A ~> yo B.
    intros X.
    eexists.
    Unshelve.
    2: {
      cbn.
      intros g x.
      apply (f ∘ g x).
    }
    intros x y.
    intro p.
    cbn.
    intros ?.
    cbn in p.
    rewrite (p _).
    reflexivity.
    Defined.

    Polymorphic Definition Yo: (C: cat) ~> presheaf C.
    exists yo @yo_map.
    - intros X Y Z f g ? ? ?; cbn.
      rewrite compose_assoc.
      reflexivity.
    - intros X Y g x; cbn.
      rewrite compose_id_left.
      reflexivity.
    - intros ? ? ? ? p ? ? ?.
      cbn.
      rewrite p.
      reflexivity.
    Defined.
  End yoneda.
End Presheaf.

Polymorphic Definition sSet := presheaf Δ.

Polymorphic Definition InfinityCategory := Enriched.Category sSet (Presheaf.product_Monoid _).
