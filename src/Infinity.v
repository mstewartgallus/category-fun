(* Seems to make classes go faster? *)
Global
Set Primitive Projections.
Global
Unset Printing Primitive Projection Parameters.

Global
Set Universe Polymorphism.

Require Import Coq.Unicode.Utf8.
Require Import Coq.derive.Derive.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.ZArith.ZArith.
Require Coq.Program.Basics.
Require Import Psatz.

Set Program Mode.

Reserved Notation "| A |" (at level 40).

Reserved Notation "A /~ B" (at level 40).

Reserved Notation "A <: B" (at level 80).

Reserved Notation "A ~> B" (at level 80).
Reserved Notation "A ∘ B" (at level 30).

Reserved Notation "A <~> B" (at level 80).
Reserved Notation "F ⁻¹" (at level 1).

Reserved Notation "F 'ᵀ'" (at level 1).

Reserved Notation "X ⊗" (at level 75, right associativity).

Reserved Notation "'lim' A , P" (right associativity, at level 200).

(* FIXME get propositional truncation from elsewhere *)
Module Import Utils.
  Variant truncate A: Prop :=
  | truncate_intro (_: A): truncate A.
  Arguments truncate_intro [A] _.

  Module TruncateNotations.
    Notation "| A |" := (truncate A): type_scope.
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
    Bishop_Setoid: Setoid type ;
  }.
  Arguments type: clear implicits.
  Existing Instance Bishop_Setoid.

  Module Export BishopNotations.
    Coercion type: Bishop >-> Sortclass.
    Notation "A /~ B" := {| type := A ; Bishop_Setoid := B |}.
  End BishopNotations.
End Bishop.

Module Import Category.
  #[universes(cumulative)]
  Class Category := {
    object: Type ;
    mor: object → object → Bishop
    where "A ~> B" := (mor A B) ;

    id {A}: mor A A ;
    compose [A B C]: mor B C -> mor A B -> mor A C
    where "f ∘ g" := (compose f g) ;

    compose_assoc [A B C D] (f: mor C D) (g: mor B C) (h: mor A B):
      (f ∘ (g ∘ h)) == ((f ∘ g) ∘ h );
    compose_id_left [A B] (f: mor A B): (id ∘ f) == f ;
    compose_id_right [A B] (f: mor A B): (f ∘ id) == f ;

    compose_compat [A B C] (f f': mor B C) (g g': mor A B):
      f == f' → g == g' → f ∘ g == f' ∘ g' ;
  }.

  Arguments object: clear implicits.
  Arguments mor: clear implicits.

  Add Parametric Morphism [K: Category] (A B C: object K) : (@compose K A B C)
      with signature equiv ==> equiv ==> equiv as compose_mor.
  Proof.
    intros ? ? p ? ? q.
    apply compose_compat.
    apply p.
    apply q.
  Qed.

  Module Export CategoryNotations.
    Coercion object: Category >-> Sortclass.
    Coercion mor: Category >-> Funclass.

    Notation "f ∘ g" := (compose f g).
    Notation "A ~> B" := (mor _ A B) (only parsing).
  End CategoryNotations.
End Category.

Definition Preset: Category := {|
  object := Type ;
  mor A B := (A → B) /~ {| equiv f g := ∀ x, f x = g x |} ;
  id _ x := x ;
  compose _ _ _ f g x := f (g x) ;
|}.

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

Module Import Sets.
  Definition Bishop: Category := {|
    object := Bishop ;
    mor A B := { op: Preset A B | ∀ x y, x == y → op x == op y } /~ {| equiv x y := ∀ t, (x:>) t == (y:>) t |} ;
    id A := @id Preset A ;
    compose A B C := @compose Preset A B C ;
  |}.

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

  Obligation 7.
  Proof.
    rewrite (H _).
    apply (H3 _ _).
    rewrite (H0 _).
    reflexivity.
  Qed.

  Solve All Obligations with cbn; reflexivity.

  Add Parametric Morphism {A B} (f: Bishop A B) : (proj1_sig f)
      with signature equiv ==> equiv as fn_mor.
  Proof.
    intros.
    destruct f.
    cbn.
    auto.
  Qed.

  Definition simple (t:Type):Bishop := t /~ {| equiv := eq |}.
End Sets.

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

Module Import Isomorphism.
  #[universes(cumulative)]
   Record iso [K: Category] (A B: K) := {
    to: K A B ;
    from: K B A ;
    to_from: to ∘ from == id ;
    from_to: from ∘ to == id ;
  }.

  Arguments to [K A B] _.
  Arguments from [K A B] _.
  Arguments to_from [K A B] _.
  Arguments from_to [K A B] _.

  Definition Isomorphism (K: Category): Category := {|
    object := K ;
    mor A B := iso A B /~ {| equiv f g := to f == to g ∧ from f == from g |} ;
    id A :=  {| to := id ; from := id |} ;
    compose A B C f g :=
      {|
        to := to f ∘ to g ;
        from := from g ∘ from f
      |} ;
  |}.

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
    rewrite <- compose_assoc.
    rewrite -> (compose_assoc (to g)).
    rewrite to_from.
    rewrite compose_id_left.
    rewrite to_from.
    reflexivity.
  Qed.

  Obligation 5.
  Proof.
    rewrite <- compose_assoc.
    rewrite -> (compose_assoc (from f)).
    rewrite from_to.
    rewrite compose_id_left.
    rewrite from_to.
    reflexivity.
  Qed.

  Obligation 6.
  Proof.
    split.
    2: symmetry.
    all: apply compose_assoc.
  Qed.

  Obligation 7.
  Proof.
    split.
    + apply compose_id_left.
    + apply compose_id_right.
  Qed.

  Obligation 8.
  Proof.
    split.
    + apply compose_id_right.
    + apply compose_id_left.
  Qed.

  Obligation 9.
  Proof.
    split.
    + apply compose_compat.
      all:assumption.
    + apply compose_compat.
      all:assumption.
  Qed.

  Definition invert [K:Category] [A B: K] (f: Isomorphism _ A B): Isomorphism _ B A :=
    {|
    to := from f ;
    from := to f ;
    to_from := from_to f ;
    from_to := to_from f ;
    |}.

  Module Export IsomorphismNotations.
    Notation "A ⁻¹" := (invert A).
    Notation "A <~> B" := (Isomorphism _ A B).
  End IsomorphismNotations.
End Isomorphism.

Module Import Functor.
  #[universes(cumulative)]
  Record functor (C D: Category) := {
    fobj: C → D ;
    map [A B]: C A B → D (fobj A) (fobj B) ;

    map_composes [X Y Z] (f: C Y Z) (g: C X Y): map f ∘ map g == map (f ∘ g) ;

    map_id {A}: map (@id _ A) == id ;
    map_compat [A B] (f f': C A B): f == f' → map f == map f' ;
  }.

  Arguments fobj [C D] _.
  Arguments map [C D] _ [A B].
  Arguments map_composes [C D] _ [X Y Z].
  Arguments map_id [C D] _ {A}.
  Arguments map_compat [C D] _ [A B].

  Module Export FunctorNotations.
    Coercion fobj: functor >-> Funclass.
    Notation "X ⊗" := (map _ X) (only parsing).
  End FunctorNotations.

  Add Parametric Morphism (C D: Category) (A B: C) (F: functor C D) : (@map _ _ F A B)
      with signature equiv ==> equiv as map_mor.
  Proof.
    intros ? ? ?.
    apply map_compat.
    assumption.
  Qed.

  Definition Functor K L: Category := {|
    object := functor K L ;
    mor A B := (∀ x, L (A x) (B x)) /~ {| equiv f g := ∀ x, f x == g x |} ;
    id _ _ := id ;
    compose _ _ _ f g _ := f _ ∘ g _ ;
  |}.

  Obligation 1.
  Proof.
    exists.
    all: unfold Reflexive, Symmetric, Transitive, compose, id, mor; cbn.
    - intros.
      reflexivity.
    - intros ? ? p t.
      symmetry.
      apply (p t).
    - intros ? ? ? p q t.
      rewrite (p t), (q t).
      reflexivity.
  Qed.

  Obligation 2.
  Proof.
    apply compose_assoc.
  Qed.

  Obligation 3.
  Proof.
    apply compose_id_left.
  Qed.

  Obligation 4.
  Proof.
    apply compose_id_right.
  Qed.

  Obligation 5.
  Proof.
    apply compose_compat.
    all:auto.
  Qed.
End Functor.

Module Import Cat.
  Import TruncateNotations.

  #[local]
  Definition to_iso {A B: Category} (f: functor A B): functor (Isomorphism A) (Isomorphism B) := {|
    fobj x := f x ;
    map _ _ p :=
      {| to := map f (to p) ;
         from := map f (from p) |}
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

  Definition Cat: Category := {|
    object := Category ;
    mor A B := (functor A B) /~ {| equiv f g := ∀ x, | f x <~> g x | |};
    id _ := {| fobj x := x ; map _ _ f := f |} ;
    compose _ _ _ F G := {| fobj x := F (G x) ; map _ _ x := map F (map G x) |} ;
  |}.

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
      apply (p' ⁻¹).
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
    set (pq := compose (Category := Isomorphism _) p' (map f_iso q') : f (g x) <~> f' (g' x)).
    exists.
    exists (to pq) (from pq).
    - apply to_from.
    - apply from_to.
  Qed.
End Cat.

Module Free.
  Import Proset.
  Import ProsetNotations.

  #[local]
   Instance free (C: Proset): Category := {
    object := C ;
    mor A B := (A <: B) /~ {| equiv _ _ := True |} ;
  }.

  Obligation 1.
  Proof.
    exists.
    all: exists.
  Qed.

  Obligation 2.
  Proof.
    reflexivity.
  Qed.

  Obligation 3.
  Proof.
    rewrite H0, H.
    reflexivity.
  Qed.

  Definition Free: Functor Proset Cat := {|
    fobj := free ;
    map _ _ f := {| fobj := f |} ;
  |}.

  Obligation 5.
  Proof.
    exists.
    apply (id: Isomorphism _ _ _).
  Qed.

  Obligation 6.
  Proof.
    exists.
    apply (id: Isomorphism _ _ _).
  Qed.

  Obligation 7.
  Proof.
    exists.
    destruct (H x) as [p q].
    exists p q.
    all: exists.
  Qed.
End Free.

Module Import Forget.
  Import TruncateNotations.
  Import Proset.
  Import ProsetNotations.

  Definition Forget: Functor Cat Proset := {|
    fobj x := {| type := x ; preorder a b := | a ~> b | |} ;
    map A B f x := f x;
  |}.

  Obligation 1.
  Proof.
    admit.
  Admitted.

  Obligation 2.
  Proof.
    destruct H as [H'].
    exists.
    apply (map f H').
  Qed.

  Obligation 3.
  Proof.
    exists.
    all: exists; apply (map (Cat.to_iso ((f: Cat _ _) ∘ g))); apply id.
  Qed.

  Obligation 4.
  Proof.
    split.
    all: exists.
    all: apply (id: Isomorphism _ _ _).
  Qed.

  Obligation 5.
  Proof.
    destruct (H t) as [H'].
    split.
    - exists.
      apply (to H').
    - exists.
      apply (from H').
  Qed.
End Forget.

Module Pointed.
  Class Category := {
    Pointed_Category: Category.Category ;
    point: Pointed_Category ;
  }.

  Coercion Pointed_Category: Category >-> Category.Category.
  Existing Instance Pointed_Category.
  Arguments point Category: clear implicits.

  Record functor (C D: Category) := {
    Pointed_Functor: Functor C D ;
    preserves_base: Pointed_Functor (point C) ~> point D ;
  }.

  Coercion Pointed_Functor: functor >-> object.
End Pointed.

Module Import Circle.
  Import Pointed.

  Module Export Undirected.
    Local Open Scope Z_scope.

    Definition Circle: Category := {|
      Pointed_Category := {|
        object := True ;
        (* Represent a circle path as an integer *)
        mor _ _ := Z /~ {| equiv x y := x = y |} ;

        id _ := 0 ;
        compose _ _ _ f g := f + g ;
      |} ;

      point := I ;
    |}.

    Obligation 1.
    Proof.
      exists.
      all: unfold Reflexive, Symmetric, Transitive.
      all: lia.
    Qed.

    Solve All Obligations with cbn; lia.
  End Undirected.

  Module Directed.
    Definition Circle: Category := {|
      Pointed_Category := {|
        object := True ;
        mor _ _ := nat /~ {| equiv := eq |}  ;

        id _ := 0 ;
        compose _ _ _ f g := f + g ;
      |} ;
      point := I ;
    |}.

    Solve All Obligations with cbn; lia.
  End Directed.
End Circle.

Module Import Trivial.
  Definition Trivial: Category := {|
    object := True ;
    mor _ _ := True /~ {| equiv _ _ := True |} ;
    id _ := I ;
    compose _ _ _ _ _ := I ;
  |}.

  Obligation 1.
  Proof.
    exists.
    all:exists.
  Qed.
End Trivial.

Definition Empty: Category := {|
  object := False ;
  mor x := match x with end ;
  id x := match x with end ;
  compose x := match x with end ;
|}.

Solve All Obligations with contradiction.

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

Module Product.
  #[local]
  Close Scope nat.

  Section products.
    Variable C D: Category.

    Definition mor (A B: C * D): Bishop :=
      (fst A ~> fst B) * (snd A ~> snd B) /~ {| equiv f g := fst f == fst g ∧ snd f == snd g |}.

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
      mor := mor ;
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

  Definition fst {A B}: Cat (Product A B) A := {|
    fobj := fst ;
    map _ _ := fst
  |}.

  Definition snd {A B}: Cat (Product A B) B := {|
    fobj := snd ;
    map _ _ := snd
  |}.

  Solve All Obligations with reflexivity.

  Definition fanout {A B C} (f: Cat C A) (g: Cat C B): Cat C (Product A B) := {|
    fobj x := (f x, g x) ;
    map _ _ x := (map f x, map g x)
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

   Definition swap {A B}: Cat (Product.Product A B) (Product.Product B A) :=
     fanout snd fst.

   Definition dup {A}: Cat A (Product.Product A A) := fanout id id.
End Product.

Module Import Loop.
  Import Pointed.

  Definition Loop: Category.Category → Category.Category := Functor Circle.
End Loop.

Module Import Opposite.
  Section opposite.
    Context `(K:Category).

    Definition op: Category := {|
      object := object K ;
      mor := Basics.flip K ;
      id _ := id ;
      compose _ _ _ := Basics.flip (@compose K _ _ _) ;
    |}.

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
      unfold Basics.flip in *.
      rewrite H, H0.
      reflexivity.
    Qed.
  End opposite.
End Opposite.

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

Module Import Over.
  #[universes(cumulative)]
   Record bundle [C: Category] (c: C) := {
    dom: C ;
    proj: C dom c ;
   }.

  Arguments dom [C] [c] _.
  Arguments proj [C] [c] _.

  Section over.
    Variables (C: Category) (c: C).

    #[local]
    Definition mor (A B: bundle c) :=
      {f: dom A ~> dom B | proj B ∘ f == proj A } /~ {| equiv f g := (f :>) == (g :>) |}.

    Obligation 1.
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

    Instance Over: Category := {
      object := bundle c ;
      mor := mor ;
      id A := @id _ (dom A) ;
      compose A B C := @compose _ (dom A) (dom B) (dom C) ;
    }.

    Obligation 1.
    Proof.
      apply compose_id_right.
    Qed.

    Obligation 2.
    Proof.
      rewrite compose_assoc.
      rewrite H0, H.
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
      rewrite H, H0.
      reflexivity.
    Qed.
  End over.

  Module Export OverNotations.
    Notation "'lim' A , P" := {| dom := A ; proj := P |}.
    Notation "C / c" := (Over.Over C c).
  End OverNotations.

  Definition Σ [C:Category] [c d] (f: d ~> c): ((C/d):Cat) ~> (C/c) := {|
    fobj g := lim _, f ∘ proj g ;
    map _ _ g := g
  |}.

  Obligation 1.
  Proof.
    rewrite <- compose_assoc.
    rewrite H.
    reflexivity.
  Qed.

  Obligation 2.
  Proof.
    reflexivity.
  Qed.

  Obligation 3.
  Proof.
    reflexivity.
  Qed.
End Over.

Module Import Pullback.
  Record pullback [A B C: Category] (F: Functor A C) (G: Functor B C) := {
    pull: Product.Product A B ;
    assoc: F (fst pull) ~> G (snd pull)
  }.

  Arguments assoc [A B C F G] _.
  Arguments pull {A B C F G} _.

  Section pullback.
    Context [A B C: Category].
    Variable F: Functor A C.
    Variable G: Functor B C.

    (* Basically a comma category *)
    #[local]
    Definition mor (X Y: pullback F G) := {
      xs: pull X ~> pull Y
      | (map G (snd xs)) ∘ assoc X == assoc Y ∘ (map F (fst xs)) }
    /~ {| equiv x y := (x:>) == (y:>) |}.

    Obligation 1.
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

    Instance Pullback: Category := {
      object := pullback F G ;
      mor := mor ;

      id _ := exist _ id _ ;
      compose _ _ _ f g := (f:>) ∘ (g:>) ;
    }.

    Obligation 1.
    Proof.
      repeat rewrite map_id.
      rewrite compose_id_left, compose_id_right.
      reflexivity.
    Qed.

    Obligation 2.
    Proof.
      cbn in *.
      repeat rewrite <- map_composes.
      rewrite <- compose_assoc.
      rewrite H.
      rewrite compose_assoc.
      rewrite H0.
      rewrite <- compose_assoc.
      reflexivity.
    Qed.

    Obligation 3.
    Proof.
      cbn in *.
      split.
      all: apply compose_assoc.
    Qed.

    Obligation 4.
    Proof.
      split.
      all: apply compose_id_left.
    Qed.

    Obligation 5.
    Proof.
      split.
      all: apply compose_id_right.
    Qed.

    Obligation 6.
    Proof.
      split.
      all: apply compose_compat.
      all: auto.
    Qed.

    Definition forget: Functor Pullback (Product.Product A B) := {|
      fobj := pull ;
      map _ _ f := f :> ;
    |}.

    Obligation 1.
    Proof.
      cbn.
      split.
      all: reflexivity.
    Qed.

    Obligation 2.
    Proof.
      split.
      all: reflexivity.
    Qed.

    Definition p1: Functor Pullback A := Product.fst ∘ forget.
    Definition p2: Functor Pullback B := Product.snd ∘ forget.
  End pullback.

  #[local]
   Definition base' [X] (F: Cat/X) (G:Cat/X): Cat/X :=
    lim (Pullback (proj F) (proj G)), proj F ∘ Product.fst ∘ forget (proj F) (proj G).
End Pullback.

Module Import Elements.
  Record elem [C] (P: Functor C Bishop) := {
    base: C ;
    pick: P base ;
  }.

  Arguments base [C] [P] _.
  Arguments pick [C] [P] _.

  Section elem.
    Context [C: Category].
    Variable P: Functor C Bishop.

    Definition mor (A B: elem P) := base A ~> base B.

    Instance Elements: Category := {
      object := elem P ;
      mor := mor ;

      id _ := id ;
      compose _ _ _ := @compose _ _ _ _ ;
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
      all: auto.
    Qed.
  End elem.
End Elements.

Module Fiber.
  (* Mostly like a presheaf due to Grothendiek stuff I don't get.
    Not quite sure what the best name for this actually is :( *)
  Definition Fiber (C:Category): Category := Cat/C.

  Section fiber.
    Variable C: Category.

    #[local]
     Definition Mor (a: C): Functor (op C) Bishop := {|
      fobj b := C b a ;
      map _ _ f g := g ∘ f ;
      |}.

    Obligation 1.
    Proof.
      unfold Basics.flip in *.
      rewrite H.
      reflexivity.
    Qed.

    Obligation 2.
    Proof.
      unfold Basics.flip in *.
      rewrite compose_assoc.
      reflexivity.
    Qed.

    Obligation 3.
    Proof.
      unfold Basics.flip in *.
      apply compose_id_right.
    Qed.

    Obligation 4.
    Proof.
      unfold Basics.flip in *.
      rewrite H.
      reflexivity.
    Qed.

    #[local]
     Definition yo (a: C): Fiber C :=
      lim (op (Elements (Mor a))), {|
        fobj := @base _ _ ;
        map _ _ f := f ;
      |}.

    Solve All Obligations with reflexivity.

    #[local]
     Definition yo_map [A B: C] (f: C A B): yo A ~> yo B := {|
      fobj (x:op (Elements (Mor A))) :=
        {| base := base x ; pick := f ∘ pick x |}:op (Elements (Mor B)) ;
      map _ _ f := f ;
    |}.

    Obligation 1.
    Proof.
      reflexivity.
    Qed.

    Obligation 2.
    Proof.
      reflexivity.
    Qed.

    Obligation 4.
    Proof.
      exists.
      apply (id: Isomorphism _ _ _).
    Qed.

    (* Not precisely yoneda but not sure of a better name *)
    Definition Yo: Functor C (Fiber C) := {|
      fobj := yo ;
      map := @yo_map ;
    |}.

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

    Definition Limit [D] (F: Functor (op D) C): Fiber C := lim (op D), F.

    Definition Intersect (f: Fiber C) (g: Fiber C): Fiber C :=
       lim (Pullback (proj f) (proj g)), (proj f ∘ Pullback.p1 _ _).
  End fiber.
End Fiber.

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

Module Import Algebra.
  Module Import Algebra.
    #[universes(cumulative)]
    Record Algebra [C:Category] (F: functor C C) := {
      elem: C ;
      assoc: F elem ~> elem
    }.

    Arguments elem [C F] _.
    Arguments assoc [C F] _.
  End Algebra.

  Section algebra.
    Context [C: Category].
    Variable F: functor C C.

    #[local]
     Definition mor (A B: Algebra F) :=
      {m: elem A ~> elem B | m ∘ assoc A == assoc B ∘ map F m }
        /~
        {| equiv x y := (x :>) == (y :>) |}.

    Obligation 1.
    Proof.
      exists.
      all: unfold Reflexive, Symmetric, Transitive.
      - intros.
        reflexivity.
      - intros.
        symmetry.
        auto.
      - intros ? ? ? p q.
        rewrite p, q.
        reflexivity.
    Qed.

    Instance Algebra: Category := {
      object := Algebra F ;
      mor := mor ;

      id A := @id _ (elem A) ;
      compose A B C := @compose _ (elem A) (elem B) (elem C) ;
    }.

    Obligation 1.
    Proof.
      rewrite map_id, compose_id_left, compose_id_right.
      reflexivity.
    Qed.

    Obligation 2.
    Proof.
      rewrite <- map_composes.
      rewrite compose_assoc.
      rewrite <- H0.
      rewrite <- compose_assoc.
      rewrite H.
      rewrite compose_assoc.
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
      rewrite H, H0.
      reflexivity.
    Qed.
  End algebra.
End Algebra.

Module Import Monomorphism.
  Section monomorphism.
    Variable C: Category.

    #[local]
    Definition monic [A B: C] (f: C A B) := ∀ (Z:C) (x y: C Z A), (f ∘ x == f ∘ y) → x == y.

    #[local]
    Definition mor A B := {x: C A B | monic x} /~ {| equiv x y := (x :>) == (y :>) |}.

    Obligation 1.
    Proof.
      exists.
      - intro.
        reflexivity.
      - intros ? ? ?.
        symmetry.
        auto.
      - intros ? ? ? p q.
        rewrite p, q.
        reflexivity.
    Qed.

    Instance Monomorphism: Category := {
      object := C ;
      mor := mor ;
      id := @id _ ;
      compose := @compose _ ;
    }.

    Obligation 1.
    Proof.
      intros ? ? ?.
      repeat rewrite compose_id_left.
      auto.
    Qed.

    Obligation 2.
    Proof.
      intros ? ? ? p.
      repeat rewrite <- compose_assoc in p.
      apply (H _ _ _ (H0 _ _ _ p)).
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
      rewrite H, H0.
      reflexivity.
    Qed.
  End monomorphism.
End Monomorphism.


Module Import Finite.
 (* Define finite totally ordered sets *)
  #[local]
  Definition mor (A B: nat) := (A ≤ B) /~ {| equiv _ _ := True |}.

  Obligation 1.
  Proof.
    exists.
    all: exists.
  Qed.

  #[local]
  Definition id {A}: mor A A := le_n A.

  #[local]
   Definition compose {A B C}: mor B C → mor A B → mor A C.
  Proof.
    cbn.
    intros f g.
    rewrite g, f.
    reflexivity.
  Defined.

  #[local]
   Instance le: Category := {
    object := nat ;
    mor := mor ;
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
Definition const {C A:Category} (x: A): Functor C A := {|
  fobj _ := x ;
  map _ _ _ := id ;
|}.

Obligation 1.
Proof.
  apply compose_id_left.
Qed.

Obligation 2.
Proof.
  reflexivity.
Qed.

Obligation 3.

Proof.
  reflexivity.
Qed.

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

Definition sSet := Fiber.Fiber Δ.
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


Module Import Cartesian.
  Class Cartesian (C: Category) := {
    prod: Functor (Product.Product C C) C ;
    fanout {x y z: C}: z ~> x → z ~> y → z ~> prod (x, y) ;
    fst {x y: C}: prod (x, y) ~> x ;
    snd {x y: C}: prod (x, y) ~> y ;
  }.
End Cartesian.

Module Import Subobject.
  Instance Subobject C c: Category := Monomorphism C/c.
End Subobject.

Module Import Epimorphism.
  Section epimorphism.
    Variable C: Category.

    #[local]
    Definition epic [A B: C] (f: C A B) := ∀ (Z:C) (x y: C B Z), (x ∘ f == y ∘ f) → x == y.

    #[local]
    Definition mor A B := {x: C A B | epic x} /~ {| equiv x y := (x :>) == (y :>) |}.

    Obligation 1.
    Proof.
      exists.
      - intro.
        reflexivity.
      - intros ? ? ?.
        symmetry.
        auto.
      - intros ? ? ? p q.
        rewrite p, q.
        reflexivity.
    Qed.

    Instance Epimorphism: Category := {
      object := C ;
      mor := mor ;
      id := @id _ ;
      compose := @compose _ ;
    }.

    Obligation 1.
    Proof.
      intros ? ? ?.
      repeat rewrite compose_id_right.
      auto.
    Qed.

    Obligation 2.
    Proof.
      intros ? ? ? p.
      repeat rewrite compose_assoc in p.
      apply (H0 _ _ _ (H _ _ _ p)).
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
      rewrite H, H0.
      reflexivity.
    Qed.
  End epimorphism.
End Epimorphism.

Module Import Arrow.
  Record arrow (K: Category) := {
    source: K ;
    target: K ;
    proj: source ~> target ;
  }.

  Arguments source [K] _.
  Arguments target [K] _.
  Arguments proj [K] _.

  Record arr [K] (A B: arrow K) := {
    source_arr: source A ~> source B ;
    target_arr: target A ~> target B ;
    commutes: target_arr ∘ proj A == proj B ∘ source_arr ;
  }.

  Arguments source_arr [K A B] _.
  Arguments target_arr [K A B] _.
  Arguments commutes [K A B] _.

  Section arrows.
    Variables K: Category.

    #[local]
    Definition mor A B := arr A B /~ {| equiv f g := (target_arr f == target_arr g) ∧ (source_arr f == source_arr g) |}.

    Obligation 1 of mor.
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
      object := arrow K ;
      mor := mor ;
      id _ := {| source_arr := id ; target_arr := id |} ;
      compose _ _ _ f g := {| target_arr := target_arr f ∘ target_arr g ;
                              source_arr := source_arr f ∘ source_arr g |} ;
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
      rewrite (commutes g).
      rewrite compose_assoc.
      rewrite compose_assoc.
      rewrite (commutes f).
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

Module Import Interval.
  #[local]
   Definition mor (A B: Prop): Bishop := (A → B) /~ {| equiv _ _ := True |}.

  Obligation 1.
  Proof.
    exists.
    all: exists.
  Qed.


  #[local]
   Definition id {A: Prop}: mor A A := λ x, x.

  #[local]
   Definition compose [A B C: Prop] (f: mor B C) (g: mor A B): mor A C :=
    λ x, f (g x).

  Instance Interval: Category := {
    object := Prop ;
    mor := mor ;

    id := @id ;
    compose := @compose ;
  }.
End Interval.


Instance UndirectedInterval: Category := {
  object := bool ;
  mor _ _ := True /~ {| equiv _ _ := True |} ;

  id _ := I ;
  compose _ _ _ _ _ := I ;
}.

Obligation 1.
Proof.
  exists.
  all:exists.
Qed.

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

Module Import Epimono.
  Section epimon.
    Context [K: Category].
    Context [A B: K].
    Variable F: K A B.

    Record zigzag := {
      pull: K ;
      epi: Epimorphism K A pull ;
      mono: Monomorphism K pull B ;
      commutes: proj1_sig mono ∘ proj1_sig epi == F
    }.

    #[local]
    Definition mor (X Y: zigzag) := {f: K (pull X) (pull Y) |
                                      proj1_sig (epi Y) == f ∘ proj1_sig (epi X) ∧
                                      proj1_sig (mono Y) ∘ f == proj1_sig (mono X)} /~ {| equiv x y := (x :>) == (y :>) |}.

    Obligation 1.
    Proof.
      exists.
      - intros ?.
        reflexivity.
      - intros ? ? ?.
        symmetry.
        auto.
      - intros ? ? ? p q.
        rewrite p, q.
        reflexivity.
    Qed.

    #[local]
    Definition id {X}: mor X X := id.

    Obligation 1.
    Proof.
      split.
      - rewrite compose_id_left.
        reflexivity.
      - rewrite compose_id_right.
        reflexivity.
    Qed.

    #[local]
    Definition compose {X Y Z} (f: mor Y Z) (g: mor X Y): mor X Z := f ∘ g.

    Obligation 1.
    Proof.
      split.
      - rewrite <- compose_assoc.
        rewrite e1, e.
        reflexivity.
      - rewrite compose_assoc.
        rewrite e2, e0.
        reflexivity.
    Qed.

    Instance Epimono: Category := {
      object := zigzag ;
      mor := mor ;
      id := @id ;
      compose := @compose ;
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
      rewrite H, H0.
      reflexivity.
    Qed.
  End epimon.
End Epimono.

Instance Discrete X: Category := {
  object := X ;
  mor A B := (A = B) /~ {| equiv _ _ := True |} ;

  id _ := eq_refl ;
  compose _ _ _ _ _  := eq_refl ;
}.

Obligation 1.
Proof.
  exists.
  all: exists.
Qed.

Instance Bool: Category := Discrete bool.

Instance Cylinder K: Category := Product.Product K Interval.

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
    Definition mor (A B: sum): Bishop := hom' A B /~ {| equiv := eq |}.

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
    eexists sum mor _ _.
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

  Definition inl {A B:Category}: Cat A (Coproduct A B) := {| fobj := inl ; map _ _ x := x |}.
  Definition inr {A B:Category}: Cat B (Coproduct A B) := {| fobj := inr ; map _ _ x := x |}.

  Solve All Obligations with reflexivity.
End Coproduct.
