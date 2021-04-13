(* Seems to make classes go faster? *)
Set Primitive Projections.
Unset Printing Primitive Projection Parameters.

Require Import Coq.Setoids.Setoid.

Reserved Notation "| A |" (at level 40).

Reserved Notation "A == B" (at level 70).

Reserved Notation "A ~> B" (at level 80).
Reserved Notation "A ∘ B" (at level 30).

Reserved Notation "A <~> B" (at level 80).
Reserved Notation "F 'ᵀ'" (at level 1).

Reserved Notation "F ! X" (at level 1).
Reserved Notation "F *" (at level 1).

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
  Polymorphic Cumulative Class Arrow := {
    type: Type ;
    equal: type -> type -> Prop
    where "A == B" := (equal A B) ;

    Setoid_Equivalence:> Equivalence equal
  }.

  Polymorphic Definition ThinArrow (A: Type): Arrow.
  exists A (fun _ _ => True).
  exists.
  all: unfold Reflexive, Symmetric, Transitive; cbn; intros; auto.
  Defined.

  Coercion type: Arrow >-> Sortclass.
  Coercion equal: Arrow >-> Funclass.

  Module Export ArrowNotations.
    Notation "A == B" := (equal A B).
  End ArrowNotations.

  Polymorphic Cumulative Class Category := {
    object: Type ;
    hom: object -> object -> Arrow
    where "A ~> B" := (hom A B) ;

    id {A}: hom A A ;
    compose {A B C}: hom B C -> hom A B -> hom A C
    where "f ∘ g" := (compose f g) ;

    compose_assoc {A B C D} (f: hom C D) (g: hom B C) (h: hom A B):
      (f ∘ (g ∘ h)) == ((f ∘ g) ∘ h );
    compose_id_left {A B} (f: hom A B): (id ∘ f) == f ;
    compose_id_right {A B} (f: hom A B): (f ∘ id) == f ;

    compose_compat {A B C} (f f': hom B C) (g g': hom A B):
      f == f' -> g == g' -> (f ∘ g) == (f' ∘ g') ;
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
    apply (compose_compat _ _ _ _ p q).
  Qed.
End Category.

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

  Polymorphic Add Parametric Morphism (C D: Category) (A B: C) (F: Functor C D) : (@Functor.map _ _ F A B)
      with signature (@equal _) ==> equal as map_mor.
  Proof.
    intros.
    apply Functor.map_compat.
    apply H.
  Qed.
End Functor.

Polymorphic Definition Functor: Category -> Category -> Category := Functor.Functor.

Module cat.
  Import TruncateNotations.

  Import Functor.
  Import Isomorphism.
  Import IsomorphismNotations.

  Polymorphic Definition eq {C D} (A B: Functor C D) :=
  forall x: C, | (@fobj _ _ A x) <~> (@fobj _ _ B x) |.

  Polymorphic Instance eq_Equivalence C D: Equivalence (@eq C D).
  exists.
  all: unfold Reflexive, Symmetric, Transitive, compose, id, hom ; cbn.
  - intros ? f.
    unfold eq.
    exists.
    apply Category.id.
  - intros ? ? p t.
    unfold eq in p.
    destruct (p t) as [p'].
    exists.
    apply Isomorphism.transpose.
    apply p'.
  - intros ? ? ? p q t.
    destruct (p t) as [p'], (q t) as [q'].
    exists.
    apply (q' ∘ p').
  Qed.

  Polymorphic Definition hom (A B: Category): Arrow := {| type := Functor A B ; equal := eq |}.

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
  exists (fun x => @fobj _ _ F (@fobj _ _ G x)) (fun _ _ x => map (map x)).
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

  Polymorphic Definition pullback {A B C} (f: hom A B): hom (Functor B C) (Functor A C).
  eexists (fun g => compose g f) _.
  Unshelve.
  4: {
    intros ? ? g ?.
    apply (g _).
  }
  all: cbn.
  all: unfold Functor.eq,Functor.hom',Functor.id,Functor.compose.
  - intros.
    reflexivity.
  - intros.
    reflexivity.
  - intros.
    rewrite (H _).
    reflexivity.
  Defined.

  Module Import FunctorNotations.
    Coercion fobj: functor >-> Funclass.
    Notation "F *" := (pullback F).
    Notation "F ! X" := (map (functor := F) X).
  End FunctorNotations.

  Polymorphic Definition to_iso {A B: Category} (f: Functor A B): Functor (Isomorphism A) (Isomorphism B).
  eexists.
  Unshelve.
  4: {
    intro x.
    apply (f x).
  }
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

  Polymorphic Definition compose_compat {A B C : Category} (f f' : hom B C) (g g' : hom A B):
    (f == f') ->
    (g == g') ->
    compose f g == compose f' g'.
  intros p q x.
  set (f_iso := to_iso f).
  destruct (q x) as [q'].
  destruct (p (g' x)) as [p'].
  set (pq := p' ∘ (f_iso ! q') : f (g x) <~> f' (g' x)).
  exists.
  eexists.
  Unshelve.
  3: apply (@to _ _ _ pq).
  3: apply (@from _ _ _ pq).
  - apply to_from.
  - apply from_to.
  Qed.

  Polymorphic Definition cat: Category.
  exists Category hom @id @compose.
  - intros ? ? ? ? ? ? ? ?.
    exists.
    apply Isomorphism.id.
  - intros ? ? ? ?.
    exists.
    apply Isomorphism.id.
  - intros ? ? ? ?.
    exists.
    apply Isomorphism.id.
  - apply @compose_compat.
  Defined.
End cat.

Import cat.FunctorNotations.
Polymorphic Definition cat: Category := cat.cat.

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

Module Product.
  Close Scope nat.

  Section products.
    Polymorphic Variable C D: Category.

    Polymorphic Definition tuple := prod C D.
    Polymorphic Definition hom' (A B: tuple) := prod (fst A ~> fst B) (snd A ~> snd B).

    Polymorphic Definition eq {A B} (f g: hom' A B) := fst f == fst g /\ snd f == snd g.

    Polymorphic Definition hom (A B: tuple): Arrow.
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

    Polymorphic Definition product: cat.
    eexists tuple hom _ _.
    Unshelve.
    5: {
      intros.
      split.
      all: apply id.
    }
    5: {
      intros.
      destruct X, X0.
      split.
      + apply (t ∘ t1).
      + apply (t0 ∘ t2).
    }
    all:cbn.
    all: unfold eq;cbn;intros;auto.
    - destruct f, g, h.
      cbn.
      split.
      all: apply compose_assoc.
    - destruct f.
      cbn.
      split.
      all: apply compose_id_left.
    - destruct f.
      cbn.
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

  (* Polymorphic Definition eval {A B C} (f: A ~> (Functor B C:cat)): product A B ~> C. *)
  Polymorphic Definition eval' {A B C} (f: A ~> (Functor B C:cat)): product A B -> C
    := fun x => f (fst x) (snd x).

  Polymorphic Definition eval_map {A B C} (f: A ~> (Functor B C:cat)):
    forall X Y,
      product A B X Y -> C (eval' f X) (eval' f Y).
  apply (fun X Y g => f ! (fst g) _ ∘ (f (fst X)) ! (snd g)).
  Defined.

  Polymorphic Definition eval {A B C} (f: A ~> (Functor B C:cat)): product A B ~> C.
  exists (eval' f) (eval_map f).
  - cbn.
    intros.
    destruct X, Y, Z.
    cbn.
    destruct f0, g.
    unfold eval_map.
    admit.
  - admit.
  - admit.
  Admitted.

  Polymorphic Definition fst {A B}: product A B ~> A.
  exists fst (fun _ _ => fst).
  - cbn.
    intros.
    destruct f, g.
    cbn.
    reflexivity.
  - intros.
    cbn.
    reflexivity.
  - intros.
    apply H.
  Defined.

  Polymorphic Definition snd {A B}: product A B ~> B.
  exists snd (fun _ _ => snd).
  - cbn.
    intros.
    destruct f, g.
    cbn.
    reflexivity.
  - intros.
    cbn.
    reflexivity.
  - intros.
    apply H.
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

    Polymorphic Definition hom (A B: sum): Arrow.
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

(* FIXME define Set as Prosets that are groupoids? *)
Module Proset.
  (* A partially ordered set is a thin category *)
  Polymorphic Definition IsThin (A: Arrow) := forall x y: A, x == y.
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
  Polymorphic Definition hom (C D: ASet): Arrow := (C: cat) ~> D.

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
      apply (ThinArrow (preorder X Y)).
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

  Polymorphic Definition prod (A B: Proset): Proset.
  exists (Product.product A B).
  intros ? ? ? p.
  destruct A0, B0.
  destruct x, p.
  cbn in t, t0, t1, t2.
  set (A' := ASet_IsSet _ _ t t1).
  set (B' := ASet_IsSet _ _ t0 t2).
  split.
  + apply A'.
  + apply B'.
  Defined.

  (* Huh domain doesn't even need to be a Proset *)
  Polymorphic Definition exp (A B: Proset): Proset.
  exists (Functor A B).
  intros X Y f g ?.
  apply (ASet_IsSet _ _ (f x) (g x)).
  Defined.

  Polymorphic Definition fst {A B: Proset}: prod A B ~> A := Product.fst.
  Polymorphic Definition snd {A B: Proset}: prod A B ~> B := Product.snd.

  Polymorphic Definition fanout {A B C: Proset}: (C ~> A) -> (C ~> B) -> (C ~> prod A B) := Product.fanout.
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

  Polymorphic Definition hom (C D: AProp): Arrow := ThinArrow AProp.

  Polymorphic Definition id {A}: hom A A.
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

    Polymorphic Definition phom (A B: K) := ThinArrow K.

    Polymorphic Definition pid {A}: phom A A.
    auto.
    Defined.

    Polymorphic Definition pcompose {A B C}: phom B C -> phom A B -> phom A C.
    auto.
    Defined.

    Polymorphic Definition AsAProp: Props.
    eexists _.
    Unshelve.
    2: {
      eexists _.
      Unshelve.
      2: {
        exists K @phom @pid @pcompose.
        all: cbn; auto.
      }
      exists.
    }
    cbn.
    unfold IsProp.
    intros x y.
    cbn in x, y.
    eexists.
    Unshelve.
    3: {
      cbn.
      apply x.
    }
    3: {
      cbn.
      apply y.
    }
    all: exists.
    Defined.
  End props.
End Props.

Import Props.PropNotations.

Polymorphic Definition Props: Category := Props.Props.
Polymorphic Definition Empty: Props := Props.AsAProp False.
Polymorphic Definition Trivial: Props := Props.AsAProp True.

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

  Definition source C: [C].
    exists 0.
    cbn.
    induction C.
    - auto.
    - auto.
  Defined.
  Definition target C: [C].
    exists C.
    cbn.
    auto.
  Defined.

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
    auto.
  Defined.
End Finite.

Import Finite.FiniteNotations.

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

Module Hom.
  Polymorphic Definition Hom C: Product.product (op C) C ~> Proset.
  eexists.
  Unshelve.
  4: {
    intro x.
    set (F := (C (Product.fst x) (Product.snd x))).
    set (H := @Setoid_Equivalence F).
    apply (Proset.AsASet F equal _ _).
  }
  4: {
    intros A B x.
    eexists.
    Unshelve.
    4: {
      intro f.
      apply (fst x ∘ f ∘ snd x).
    }
    all: cbn.
    all: auto.
    intros.
    unfold Opposite.compose.
    rewrite H.
    reflexivity.
  }
  all: cbn.
  - intros.
    intro.
    exists.
    cbn.
    eexists.
    Unshelve.
    3: {
      cbn.
      unfold Opposite.compose.
      cbn.
      cbn in x.
      destruct f, g.
      cbn.
      repeat rewrite compose_assoc.
      reflexivity.
    }
    3: {
      cbn.
      cbn in x.
      unfold Opposite.compose.
      destruct f, g.
      cbn.
      repeat rewrite compose_assoc.
      reflexivity.
    }
    all:cbn.
    all:auto.
  - intros ? ?.
    exists.
    cbn.
    eexists.
    Unshelve.
    3: {
      cbn.
      unfold Opposite.compose, Opposite.id.
      rewrite compose_id_left, compose_id_right.
      reflexivity.
    }
    3: {
      cbn.
      unfold Opposite.compose, Opposite.id.
      rewrite compose_id_left, compose_id_right.
      reflexivity.
    }
    all:cbn.
    all:auto.
  - cbn.
    exists.
    eexists.
    Unshelve.
    3: {
      cbn.
      unfold Opposite.compose.
      cbn in x.
      destruct H.
      rewrite H, H0.
      reflexivity.
    }
    3: {
      cbn.
      unfold Opposite.compose.
      cbn in x.
      destruct H.
      rewrite H, H0.
      reflexivity.
    }
    all:cbn.
    all:auto.
  Defined.
End Hom.

Module Diagrams.
  Import Functor.

  Section diagrams.
    Polymorphic Context {C:Category}.

    Polymorphic Definition Empty: ((op (Empty: Proset): cat) ~> C).
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

    Polymorphic Definition Constant (c: C): (op ((Trivial:Proset):cat): cat) ~> C.
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

Module Limits.
  Import Hom.

  Polymorphic Definition pt {D:cat}: D ~> Proset.
  eexists (fun _ => (Trivial:Proset)) _.
  Unshelve.
  4: {
    intros.
    apply id.
  }
  3: {
    intros.
    cbn.
    reflexivity.
  }
  all:cbn.
  2: {
    intro.
    reflexivity.
  }
  intros.
  exists.
  eexists.
  Unshelve.
  3,4:exists.
  all: cbn.
  all: auto.
  Defined.

  Polymorphic Definition limit {D:cat} (F: (op D:cat) ~> Proset): Proset :=
    Hom (Functor (op D) Proset) (pt, F).

  Polymorphic Definition unit := limit Diagrams.Empty.
  Polymorphic Definition bang {A} : A ~> unit.
  eexists _ _.
  Unshelve.
  4: {
    intros.
    intro.
    destruct x.
  }
  4: {
    intros.
    cbn.
    intro.
    cbn in x.
    destruct x.
  }
  all: cbn.
  all: auto.
  Defined.

  (* Not really sure there's a point here or what it means *)
  Polymorphic Definition yo (c: Proset) := limit (Diagrams.Constant c).
  Polymorphic Definition yo_map' {A B} (f: A ~> B): yo A -> yo B.
  intros ? ?.
  exists (fun _ => f (X I I)) (fun _ _ _ => f ! id).
  all: cbn.
  all: intros.
  - rewrite Functor.map_composes.
    rewrite compose_id_left.
    reflexivity.
  - intros.
    apply Functor.map_id.
  - intros.
    reflexivity.
  Defined.

  Polymorphic Definition yo_map'' {A B} (f: A ~> B):
    forall X Y, yo A X Y -> yo B (yo_map' f X) (yo_map' f Y).
  intros X Y g ?.
  destruct (g I I) as [g'].
  exists.
  eexists.
  Unshelve.
  3: {
    cbn.
    apply Functor.map.
    apply (@Isomorphism.to _ _ _ g').
  }
  3: {
    cbn.
    apply Functor.map.
    apply (@Isomorphism.from _ _ _ g').
  }
  all:cbn.
  all:rewrite Functor.map_composes.
  all:rewrite <- Functor.map_id.
  all:apply Functor.map_compat.
  1:rewrite Isomorphism.to_from.
  2:rewrite Isomorphism.from_to.
  all:reflexivity.
  Defined.

  Polymorphic Definition yo_map {A B} (f: A ~> B): yo A ~> yo B.
  exists (yo_map' f) (yo_map'' f).
  all: intros; cbn; auto.
  Defined.
End Limits.

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
  Definition hom (A B: nat): Arrow := ([A]: Proset) ~> [B].

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
