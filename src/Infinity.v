(* Seems to make classes go faster? *)
Global
Set Primitive Projections.
Global
Unset Printing Primitive Projection Parameters.

Global
Set Universe Polymorphism.

From Ltac2 Require Import Ltac2.

Set Default Proof Mode "Classic".

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

Reserved Notation "X ⊗ Y" (at level 30, right associativity).


Reserved Notation "A <~> B" (at level 80).
Reserved Notation "F ⁻¹" (at level 1).

Reserved Notation "F 'ᵀ'" (at level 1).

Reserved Notation "'lim' A , P" (right associativity, at level 200).

Reserved Notation "·".
Reserved Notation "∅".

Reserved Notation "X × Y" (at level 30, right associativity).
Reserved Notation "⟨ A , B ⟩".
Reserved Notation "'π₁'".
Reserved Notation "'π₂'".

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

Module Bishops.
  Definition True := True /~ {| equiv _ _ := True |}.
  Obligation 1.
  Proof.
    exists.
    all:exists.
  Qed.

  Definition False := False /~ {| equiv x := match x with end |}.
  Obligation 1.
  Proof.
    exists.
    all:intro;contradiction.
  Qed.
End Bishops.

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

  Module Reflection.
    Inductive ast {K: Category}: K → K → Type :=
    | ast_id A: ast A A
    | ast_compose {A B C}: ast B C → ast A B → ast A C
    | ast_var {A B}: K A B → ast A B
    .


    #[local]
    Fixpoint denote [K: Category] [A B] (p: ast A B): K A B :=
      match p with
      | ast_id _ => id
      | ast_compose f g => denote f ∘ denote g
      | ast_var f => f
      end.

    #[local]
    Instance ast_eq [K: Category] (A B: K): Setoid (ast A B) := {
      equiv x y := denote x == denote y
    }.

    Obligation 1.
    Proof.
      exists.
      - intros ?.
        reflexivity.
      - intro.
        symmetry.
        assumption.
      - intros ? ? ? p q.
        rewrite p, q.
        reflexivity.
    Qed.

    Inductive path {K: Category} (A: K): K → Type :=
    | path_id: path A A
    | path_compose {B C}: K B C → path A B → path A C
    .

    Arguments path_id {K A}.
    Arguments path_compose {K A B C}.

    #[local]
    Fixpoint pdenote {K: Category} [A B: K] (f: path A B): K A B :=
      match f with
      | path_id => id
      | path_compose h t => h ∘ pdenote t
      end.

    #[local]
    Instance path_eq [K: Category] (A B: K): Setoid (path A B) := {
      equiv x y := pdenote x == pdenote y
    }.

    Obligation 1.
    Proof.
      exists.
      - intros ?.
        reflexivity.
      - intro.
        symmetry.
        assumption.
      - intros ? ? ? p q.
        rewrite p, q.
        reflexivity.
    Qed.

    #[local]
     Definition sing [K: Category] [A B: K] (x: K A B): path A B :=
      path_compose x path_id.

    #[local]
     Fixpoint app [K: Category] [A B C: K] (x: path B C) (y: path A B): path A C :=
      match x with
      | path_id => y
      | path_compose h t => path_compose h (app t y)
      end.

    #[local]
    Fixpoint flatten [K: Category] [A B: K] (x: ast A B): path A B :=
      match x with
      | ast_id _ => path_id
      | ast_compose f g => app (flatten f) (flatten g)
      | ast_var f => sing f
      end.

    #[local]
    Lemma flatten_correct' [K: Category] [A B C: K] (f: path B C) (g: path A B):
      pdenote f ∘ pdenote g == pdenote (app f g).
    Proof.
      induction f.
      - cbn.
        rewrite compose_id_left.
        reflexivity.
      - cbn.
        rewrite <- compose_assoc.
        rewrite <- IHf.
        reflexivity.
    Qed.

    #[local]
     Theorem flatten_correct [K: Category] [A B: K] (f: ast A B): denote f == pdenote (flatten f).
    Proof.
      induction f.
      - reflexivity.
      - cbn.
        rewrite <- flatten_correct'.
        rewrite IHf1, IHf2.
        reflexivity.
      - cbn.
        rewrite compose_id_right.
        reflexivity.
    Qed.

    #[local]
     Theorem flatten_injective [K: Category] [A B] [x y: ast A B]:
      flatten x == flatten y → x == y.
    Proof.
      cbn.
      repeat rewrite <- flatten_correct.
      intro.
      assumption.
    Qed.

    #[local]
    Ltac2 rec reify (p: constr) :=
      lazy_match! p with
    | (@id ?k ?a) =>
      constr: (ast_id $a)
    | (@compose ?k ?a ?b ?c ?f ?g) =>
      let nf := reify f in
      let ng := reify g in
      constr: (ast_compose $nf $ng)
    | ?p =>
      constr: (ast_var $p)
    end.

    Ltac2 category () :=
      lazy_match! goal with
    | [ |- ?f == ?g ] =>
      let rf := reify f in
      let rg := reify g in
      change (denote $rf == denote $rg) ; apply flatten_injective ; cbn
    end.

    Ltac category :=
      ltac2:(Control.enter category).
  End Reflection.
End Category.

Import Category.Reflection.

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
    category.
    reflexivity.
  Qed.

  Obligation 3.
  Proof.
    category.
    reflexivity.
  Qed.

  Obligation 4.
  Proof.
    category.
    reflexivity.
  Qed.

  Obligation 5.
  Proof.
    apply compose_compat.
    all:auto.
  Qed.
End Functor.

Module Circle.
  Module Undirected.
    Local Open Scope Z_scope.

    Definition Circle: Category := {|
      object := True ;
      mor _ _ := Z /~ {| equiv := eq |} ;

      id _ := 0 ;
      compose _ _ _ f g := f + g ;
    |}.

    Solve All Obligations with cbn; lia.
  End Undirected.

  Module Directed.
    Definition Circle: Category := {|
      object := True ;
      mor _ _ := nat /~ {| equiv := eq |} ;

      id _ := 0 ;
      compose _ _ _ f g := f + g ;
    |}.

    Solve All Obligations with cbn; lia.
  End Directed.
End Circle.

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
    category.
    reflexivity.
  Qed.

  Obligation 3.
  Proof.
    category.
    reflexivity.
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
    all: category.
    all: reflexivity.
  Qed.

  Obligation 8.
  Proof.
    split.
    all: category.
    all: reflexivity.
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

Module Product.
  #[local]
  Close Scope nat.

  Definition Product (C D: Category): Category := {|
    object := C * D ;
    mor A B :=  (fst A ~> fst B) * (snd A ~> snd B) /~ {| equiv f g := fst f == fst g ∧ snd f == snd g |} ;
    id _ := (id, id) ;
    compose _ _ _ f g := (fst f ∘ fst g, snd f ∘ snd g)
  |}.

  Next Obligation.
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

  Next Obligation.
  Proof.
    split.
    all: category.
    all: reflexivity.
  Qed.

  Next Obligation.
  Proof.
    split.
    all: category.
    all: reflexivity.
  Qed.

  Next Obligation.
  Proof.
    split.
    all: category.
    all: reflexivity.
  Qed.

  Next Obligation.
  Proof.
    split.
    + rewrite H, H0.
      reflexivity.
    + rewrite H1, H2.
      reflexivity.
  Qed.
End Product.

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

Module Bicategory.
  Class Bicategory := {
    object: Type ;
    mor: object → object → Category ;

    id {A}: mor A A ;
    compose {A B C}: Functor (mor B C) (Functor (mor A B) (mor A C)) ;

    (* FIXME laws *)
  }.

  Module Export BicategoryNotations.
    Coercion object: Bicategory >-> Sortclass.
    Coercion mor: Bicategory >-> Funclass.
  End BicategoryNotations.
End Bicategory.

Import Bicategory.BicategoryNotations.

Module Import Cat.
  Import TruncateNotations.
  Import Bicategory.

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

  Definition Cat: Bicategory := {|
    object := Category ;
    mor A B := Functor A B ;
    id _ := {| fobj x := x ; map _ _ f := f |} ;
    compose A B C :=
      {|
        fobj F := {| fobj G := {| fobj x := F (G x) ; map _ _ x := map F (map G x) |} ;
                     map _ _ G x := map F (G x) ;
                  |} ;
        map _ _ F G x := F (G x) ;
      |} ;
  |}.

  Next Obligation.
  Proof.
    reflexivity.
  Qed.

  Next Obligation.
  Proof.
    reflexivity.
  Qed.

  Next Obligation.
  Proof.
    repeat rewrite <- map_composes.
    reflexivity.
  Qed.

  Next Obligation.
  Proof.
    repeat rewrite map_id.
    reflexivity.
  Qed.

  Next Obligation.
  Proof.
    rewrite H.
    reflexivity.
  Qed.

  Next Obligation.
  Proof.
    rewrite map_composes.
    reflexivity.
  Qed.

  Next Obligation.
  Proof.
    rewrite map_id.
    reflexivity.
  Qed.

  Next Obligation.
  Proof.
    rewrite (H x).
    reflexivity.
  Qed.

  Solve Obligations with reflexivity.
End Cat.

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

    Instance Elements: Category := {
      object := elem P ;
      mor A B := base A ~> base B ;

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


Definition Empty: Category := {|
  object := False ;
  mor x := match x with end ;
  id x := match x with end ;
  compose x := match x with end ;
|}.

Solve All Obligations with contradiction.

Module Import Hom.
   Definition Hom S: Functor S (Functor (op S) Bishop) := {|
    fobj a := {|
               fobj b := S b a ;
               map _ _ f g := g ∘ f ;
             |} ;
    map _ _ f _ g := f ∘ g ;
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
    all: category.
    all: reflexivity.
  Qed.

  Obligation 3.
  Proof.
    unfold Basics.flip in *.
    all: category.
    all: reflexivity.
  Qed.

  Obligation 4.
  Proof.
    unfold Basics.flip in *.
    rewrite H.
    reflexivity.
  Qed.

  Obligation 5.
  Proof.
    rewrite H.
    reflexivity.
  Qed.

  Obligation 6.
  Proof.
    all: category.
    all: reflexivity.
  Qed.

  Obligation 7.
  Proof.
    all: category.
    all: reflexivity.
  Qed.

  Obligation 8.
  Proof.
    rewrite H.
    reflexivity.
  Qed.
End Hom.

Module Import Pullback.
  #[universes(cumulative)]
  Record pullback [A B C: Category] (F: Functor A C) (G: Functor B C) := {
    source: A ;
    target: B ;
    assoc: F source <~> G target ;
  }.

  Arguments assoc [A B C F G] _.
  Arguments source {A B C F G} _.
  Arguments target {A B C F G} _.

  (* Basically a comma category *)
  #[universes(cumulative)]
  Record comma [A B C] (F: Functor A C) (G: Functor B C) (X Y: pullback F G) := {
    source_mor: source X ~> source Y ;
    target_mor: target X ~> target Y ;
    commutes: map G target_mor ∘ to (assoc X) == to (assoc Y) ∘ map F source_mor ;
  }.

  Arguments source_mor [A B C F G X Y] _.
  Arguments target_mor [A B C F G X Y] _.
  Arguments commutes [A B C F G X Y] _.

  Definition Pullback [A B C] (F: Functor A C) (G: Functor B C): Category := {|
    object := pullback F G ;
    mor A B := comma F G A B /~
                     {|
                       equiv x y :=
                         source_mor x == source_mor y ∧ target_mor x == target_mor y |} ;

    id _ := {| source_mor := id ; target_mor := id |} ;
    compose _ _ _ f g :=
      {|
        source_mor := source_mor f ∘ source_mor g ;
        target_mor := target_mor f ∘ target_mor g ;
      |} ;
  |}.

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

  Obligation 2.
  Proof.
    repeat rewrite map_id.
    category.
    reflexivity.
  Qed.

  Obligation 3.
  Proof.
    cbn in *.
    repeat rewrite <- map_composes.
    rewrite <- compose_assoc.
    rewrite commutes.
    rewrite compose_assoc.
    rewrite commutes.
    rewrite <- compose_assoc.
    reflexivity.
  Qed.

  Obligation 4.
  Proof.
    cbn in *.
    split.
    all: category.
    all: reflexivity.
  Qed.

  Obligation 5.
  Proof.
    split.
    all: category.
    all: reflexivity.
  Qed.

  Obligation 6.
  Proof.
    split.
    all: category.
    all: reflexivity.
  Qed.

  Obligation 7.
  Proof.
    split.
    all: apply compose_compat.
    all: auto.
  Qed.

  Definition p1 {A B C} (F: Functor A C) (G: Functor B C): Functor (Pullback F G) A := {|
    fobj := source ;
    map _ _ f := source_mor f ;
  |}.

  Solve All Obligations with reflexivity.

  Definition p2 {A B C} (F: Functor A C) (G: Functor B C): Functor (Pullback F G) B := {|
    fobj := target ;
    map _ _ f := target_mor f ;
  |}.

  Solve All Obligations with reflexivity.
End Pullback.

Module Import Fibred.
  (*
   By the Grothendiek construction
   Indexed categories can by represented as fibered categories.
  *)
  #[universes(cumulative)]
  Record diagram S := {
    dom: Cat ;
    proj: Cat dom S ;
   }.

  Arguments dom [S] _.
  Arguments proj [S] _.

  (* Define the (not lax) 2-slice category. We just define the 1 morphisms *)
  #[universes(cumulative)]
  Record over [S] (A B: diagram S) := {
    slice: Cat (dom A) (dom B) ;
    commutor t: proj A t <~> proj B (slice t) ;
  }.

  Arguments slice [S A B].
  Arguments commutor [S A B].

  Definition fibred S (F G: diagram S): Category := {|
    object := over F G ;

    (* FIXME check commutor *)
    mor A B := (∀ X, slice A X ~> slice B X) /~ {| equiv x y := ∀ t, x t == y t |} ;

    id _ _ := id ;
    compose _ _ _ f g t := f t ∘ g t ;
  |}.

  Obligation 1.
  Proof.
    exists.
    - intros ? ?.
      reflexivity.
    - admit.
    - admit.
  Admitted.

  Obligation 2.
  Proof.
    all: category.
    all: reflexivity.
  Qed.

  Obligation 3.
  Proof.
    all: category.
    all: reflexivity.
  Qed.

  Obligation 4.
  Proof.
    all: category.
    all: reflexivity.
  Qed.

  Obligation 5.
  Proof.
    rewrite (H t), (H0 t).
    reflexivity.
  Qed.

  Solve All Obligations with reflexivity.

  Import Bicategory.

  Definition Fibred S: Bicategory := {|
    object := diagram S ;
    mor := fibred S ;

    id _ := {| slice := id ; commutor _ := Category.id |}  ;
    compose _ _ _ :=
      {|
        fobj F :=
          {|
            fobj G :=
              {|
                slice := compose (slice F) (slice G) ;
                commutor t := commutor F (slice G t) ∘ (commutor G t) |} ;
            map _ _ G x := map (slice F) (G x) ;
          |} ;
        map _ _ F G x := F (slice G x) ;
      |} ;
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
    rewrite (H2 t).
    reflexivity.
  Qed.

  Solve Obligations with reflexivity.

  Module Export FibredNotations.
    Notation "'lim' A , P" := {| dom := A ; proj := P |}.
  End FibredNotations.

  Definition Terminal {C}: Fibred C := lim _, id.
  Definition Bang {C} {A: Fibred C}: Fibred C A Terminal :=
    {| slice := proj A ; commutor _ := Category.id |}.

  Definition Initial {C}: Fibred C := lim Empty, {| fobj x := match x with end ; map A := match A with end |}.

  Solve All Obligations with cbn; contradiction.

  Definition Absurd {C} {A: Fibred C}: Fibred C Initial A :=
    {| slice := {| fobj (x: Empty) := match x with end ;
                   map A := match A with end |} |}.

  Solve All Obligations with cbn; contradiction.

  Definition Product {C} (f: Fibred C) (g: Fibred C): Fibred C
    := lim (Pullback (proj f) (proj g)), compose (proj f) (Pullback.p1 (proj f) (proj g)).

  Definition Fanout {K} {A B C: Fibred K} (f: Fibred K C A) (g: Fibred K C B): Fibred K C (Product A B) :=
    {| slice :=
    {|
      fobj (x:dom C) :=
        {|
          source := slice f x ;
          target := slice g x ;
          assoc := commutor g x ∘ (commutor f x) ⁻¹ ;
        |}: Pullback _ _ ;
    map _ _ x :=
      {|
        source_mor := map (slice f) x ;
        target_mor := map (slice g) x ;
      |} ;
    |}
    |}.

  Obligation 1.
  Proof.
    admit.
  Admitted.

  Obligation 2.
  Proof.
    split.
    all: apply map_composes.
  Qed.

  Obligation 3.
  Proof.
    split.
    all: apply map_id.
  Qed.

  Obligation 4.
  Proof.
    split.
    all: rewrite H.
    all: reflexivity.
  Qed.

  Obligation 5.
  Proof.
   apply f.
  Qed.

  Definition Fst {C} {A B: Fibred C}: Fibred C (Product A B) A :=
    {|
    slice :=
      {|
        fobj := Pullback.p1 _ _ ;
        map _ _ f := source_mor f ;
      |} ;
    commutor _ := Category.id ;
    |}.

  Definition Snd {C} {A B: Fibred C}: Fibred C (Product A B) B :=
    {|
    slice :=
      {|
        fobj := Pullback.p2 _ _ ;
        map _ _ f := target_mor f ;
      |} ;
    commutor t := assoc t ;
    |}.

  Solve All Obligations with reflexivity.

  Module ToposNotations.
    Notation "!" := Bang.
    Notation "·" := Terminal.

    Notation "∅" := Initial.

    Infix "×" := Product.
    Notation "⟨ A , B ⟩" := (Fanout A B).
    Notation "'π₁'" := Fst.
    Notation "'π₂'" := Snd.
  End ToposNotations.
End Fibred.

Module Group.
  Import Circle.Undirected.
  Import ToposNotations.

  Definition Group := Fibred Circle.

  Definition Terminal: Group := ·.
  Definition bang A: Group A Terminal := !.
End Group.

Module Monoid.
  Import Circle.Directed.
  Import ToposNotations.

  Definition Monoid := Fibred Circle.

  Definition S1: Monoid := Yo Circle I.
  Definition Loop (n: nat): S1 ~> S1 := map (Yo Circle) n.

  Definition Initial: Monoid := ∅.
  Definition Terminal: Monoid := ·.

  Definition Product (A B: Monoid): Monoid := A × B.
  Definition Fanout {C A B: Monoid} (f: C ~> A) (g: C ~> B): C ~> A × B := ⟨ f , g ⟩.
  Definition Fst {A B}: Product A B ~> A := π₁.
  Definition Snd {A B}: Product A B ~> B := π₂.
End Monoid.

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

Module Import Monoid.
  Class Monoid := {
    M: Bishop ;

    unit: M ;
    app: M → M → M
    where "f ⊗ g" := (app f g) ;

    app_assoc (f: M) (g: M) (h: M):
      (f ⊗ (g ⊗ h)) == ((f ⊗ g) ⊗ h );
    app_unit_left (f: M): (unit ⊗ f) == f ;
    app_unit_right (f: M): (f ⊗ unit) == f ;

    app_compat (f f': M) (g g': M):
      f == f' → g == g' → f ⊗ g == f' ⊗ g' ;
  }.

  Add Parametric Morphism [K: Monoid] : (@app K)
      with signature equiv ==> equiv ==> equiv as app_mor.
  Proof.
    intros ? ? p ? ? q.
    apply app_compat.
    apply p.
    apply q.
  Qed.

  Module Export MonoidNotations.
    Coercion M: Monoid >-> Bishop.

    Notation "f ⊗ g" := (app f g).
  End MonoidNotations.
End Monoid.


Module Import Trivial.
  Definition Trivial: Monoid := {|
    M := Bishops.True ;

    unit := I ;
    app _ _ := I ;
  |}.
End Trivial.

Module Complex.
  Local Open Scope Z_scope.

  Definition Complex: Monoid := {|
    M := (Z * Z)%type /~ {| equiv x y := fst x = fst y ∧ snd x = snd y |} ;

    unit := (0, 0) ;
    app x y := (fst x + fst y, snd x + snd y) ;
 |}.

  Obligation 1.
  Proof.
    exists.
    all: split.
    all: lia.
  Qed.

  Solve All Obligations with cbn; lia.
End Complex.

Module Import Mon.
  #[universes(cumulative)]
  Record mon (C: Monoid) (D: Monoid) := {
    act: C → D ;

    act_composes f g: act f ⊗ act g == act (f ⊗ g) ;

    act_unit: act unit == unit ;
    act_compat f f': f == f' → act f == act f' ;
  }.

  Arguments act [C D] _.

  Module Export MonNotations.
    Coercion act: mon >-> Funclass.
  End MonNotations.
  Add Parametric Morphism C D (F: mon C D) : (act F)
      with signature equiv ==> equiv as act_mor.
  Proof.
    intros ? ? ?.
    apply act_compat.
    assumption.
  Qed.

  Definition Mon: Category := {|
    object := Monoid ;
    mor A B := mon A B /~ {| equiv x y := ∀ t, x t == y t |} ;

    id _ := {| act x := x |} ;
    compose _ _ _ f g := {| act x := f (g x) |}
  |}.

  Obligation 1.
  Proof.
    exists.
    - intros ? ?.
      reflexivity.
    - intros ? ? p ?.
      symmetry.
      apply (p _).
    - intros ? ? ? p q t.
      rewrite (p t), (q t).
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

  Obligation 5.
  Proof.
    repeat rewrite <- act_composes.
    reflexivity.
  Qed.

  Obligation 6.
  Proof.
    repeat rewrite act_unit.
    reflexivity.
  Qed.

  Obligation 7.
  Proof.
    rewrite H2.
    reflexivity.
  Qed.

  Obligation 8.
  Proof.
    reflexivity.
  Qed.

  Obligation 9.
  Proof.
    reflexivity.
  Qed.

  Obligation 10.
  Proof.
    reflexivity.
  Qed.

  Obligation 11.
  Proof.
    rewrite (H _), (H0 _).
    reflexivity.
  Qed.
End Mon.
Module Import Interval.
  Module Export Undirected.
    Definition Interval: Category := {|
      object := bool ;
      mor _ _ := Bishops.True ;

      id _ := I ;
      compose _ _ _ _ _ := I ;
   |}.
  End Undirected.

  Module Directed.
    #[local]
     Definition mor (A B: bool) :=
      (if A then if B then True else False else True) /~ {| equiv _ _ := True |}.

    Obligation 1.
    Proof.
      exists.
      all: exists.
    Qed.

    #[local]
     Definition id {A}: mor A A :=
      match A with
      | true => I
      | false => I
      end.

    #[local]
     Definition compose {A B C}: mor B C → mor A B → mor A C.
    destruct B.
    - destruct C.
      all: try contradiction.
      destruct A.
      all: exists.
    - destruct A.
      all: try contradiction.
      destruct C.
      all: exists.
    Defined.

    Set Program Mode.

    Definition Interval: Category := {|
      object := bool ;
      Category.mor := mor ;
      Category.id := @id ;
      Category.compose := @compose ;
    |}.
  End Directed.
End Interval.

Module Import Arrow.
  Module Export Directed.
    Import Interval.Directed.

    Definition Arrow := Functor Interval.
  End Directed.
End Arrow.

Module Import Finite.
  Definition Finite: Category := {|
    object := nat ;
    mor A B := ({x | x ≤ A} → {x | x ≤ B }) /~ {| equiv x y := ∀ t, proj1_sig (x t) = proj1_sig (y t) |};

    id _ x := x ;
    compose _ _ _ f g x := f (g x) ;
  |}.

  Obligation 1.
  Proof.
    exists.
    - intros ? ?.
      reflexivity.
    - intros ? ? p.
      symmetry.
      apply (p t).
    - intros ? ? ? p q t.
      rewrite (p t), (q t).
      reflexivity.
  Defined.

  Obligation 5.
  Proof.
    admit.
  Admitted.
End Finite.

Module Import Deloop.
  Module Export Undirected.
    Local Open Scope Z_scope.

    Definition Deloop (C: Category) (c: C): Category := {|
      object := True ;
      mor _ _ := (C c c * Z) /~ {| equiv x y := fst x == fst y ∧ snd x = snd y |} ;

      id _ := (id, 0) ;
      compose _ _ _ f g := (fst f ∘ fst g, snd f + snd g) ;
   |}.

    Obligation 1.
    Proof.
      exists.
      all: split.
      - reflexivity.
      - reflexivity.
      - symmetry.
        destruct H1.
        assumption.
      - symmetry.
        destruct H1.
        assumption.
      - destruct H1, H2.
        rewrite H1, H2.
        reflexivity.
      - destruct H1, H2.
        rewrite H3, H4.
        reflexivity.
    Qed.

    Obligation 2.
    Proof.
      cbn.
      split.
      - apply compose_assoc.
      - lia.
    Qed.

    Obligation 3.
    Proof.
      cbn.
      split.
      - apply compose_id_left.
      - lia.
    Qed.

    Obligation 4.
    Proof.
      cbn.
      split.
      - apply compose_id_right.
      - lia.
    Qed.

    Obligation 5.
    Proof.
      cbn.
      split.
      - rewrite H, H0.
        reflexivity.
      - cbn in *.
        lia.
    Qed.
  End Undirected.

  Module Directed.
    Definition Deloop (C: Category) (c: C) : Category := {|
      object := True ;
      mor _ _ := (C c c * nat) /~ {| equiv x y := fst x == fst y ∧ snd x = snd y |} ;

      id _ := (id, 0) ;
      compose _ _ _ f g := (fst f ∘ fst g, snd f + snd g) ;
    |}.

    Obligation 1.
    Proof.
      exists.
      all: split.
      - reflexivity.
      - reflexivity.
      - symmetry.
        destruct H1.
        assumption.
      - symmetry.
        destruct H1.
        assumption.
      - destruct H1, H2.
        rewrite H1, H2.
        reflexivity.
      - destruct H1, H2.
        rewrite H3, H4.
        reflexivity.
    Qed.

    Obligation 2.
    Proof.
      cbn.
      split.
      - apply compose_assoc.
      - lia.
    Qed.

    Obligation 3.
    Proof.
      cbn.
      split.
      - apply compose_id_left.
      - lia.
    Qed.

    Obligation 4.
    Proof.
      cbn.
      split.
      - apply compose_id_right.
      - lia.
    Qed.

    Obligation 5.
    Proof.
      cbn.
      split.
      - rewrite H, H0.
        reflexivity.
      - cbn in *.
        lia.
    Qed.
  End Directed.
End Deloop.


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

Module Import Loop.
  Import Pointed.

  Definition Loop: Category.Category → Category.Category := Functor Circle.
End Loop.

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


Module Import Chain.
  Section chain.
    Variable X: Category.

    (* Every abelian group can be thought of as an action on the circle *)

    Definition complex := Functor (op Δ) X.
    Definition d (n: nat) (V: complex): V (1 + n) ~> V n :=
      @map _ _ V (1 + n) n {|
             fobj x := lim (dom x), le_S _ _ (proj x) ;
             map _ _ f := f ;
           |}.

    Definition zero n (V: complex) := d n V ∘ d (1 + n) V.

  End chain.
End Chain.

Definition InftyCat := Fiber.Fiber Δ.

Definition pure (c: Category): InftyCat := lim c, {| fobj _ := 0 ; map _ _ _ := id |}.

Obligation 1.
Proof.
  exists.
  apply (id: Isomorphism _ _ _).
Qed.

Obligation 2.
Proof.
  exists.
  apply (id: Isomorphism _ _ _).
Qed.

Obligation 3.
Proof.
  exists.
  apply (id: Isomorphism _ _ _).
Qed.

Definition InftyYo: Functor Δ InftyCat := Fiber.Yo Δ.


Definition True_set := True /~ {| equiv _ _ := True |}.

Obligation 1.
Proof.
  exists.
  all: exists.
Qed.


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

(* Module Import Interval. *)
(*   #[local] *)
(*    Definition mor (A B: Prop): Bishop := (A → B) /~ {| equiv _ _ := True |}. *)

(*   Obligation 1. *)
(*   Proof. *)
(*     exists. *)
(*     all: exists. *)
(*   Qed. *)


(*   #[local] *)
(*    Definition id {A: Prop}: mor A A := λ x, x. *)

(*   #[local] *)
(*    Definition compose [A B C: Prop] (f: mor B C) (g: mor A B): mor A C := *)
(*     λ x, f (g x). *)

(*   Instance Interval: Category := { *)
(*     object := Prop ; *)
(*     mor := mor ; *)

(*     id := @id ; *)
(*     compose := @compose ; *)
(*   }. *)
(* End Interval. *)

(* Instance Interval: Category := { *)
(*   object := bool ; *)
(*   mor _ _ := True /~ {| equiv _ _ := True |} ; *)

(*   id _ := I ; *)
(*   compose _ _ _ _ _ := I ; *)
(* }. *)

(* Obligation 1. *)
(* Proof. *)
(*   exists. *)
(*   all:exists. *)
(* Qed. *)


Definition Arr C := Functor Interval C.
Definition Endo C := Functor Circle.Directed.Circle C.

Definition Iso C := Functor Interval C.
Definition Auto C := Functor Circle C.

Definition Cylinder C := Product.Product C Interval.


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
