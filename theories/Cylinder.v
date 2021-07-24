Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Strings.String.

Require Import Blech.Bishop.
Require Import Blech.Type.Some.
Require Import Blech.Functor.
Require Import Blech.Category.
Require Import Blech.Category.Funct.
Require Import Blech.Category.Prod.
Require Import Blech.Category.Bsh.
Require Import Blech.Category.Op.
Require Import Blech.Category.El.
Require Import Blech.Groupoid.
Require Import Blech.Groupoid.Core.

Import BishopNotations.
Import SomeNotations.
Import CategoryNotations.
Import GroupoidNotations.
Import CoreNotations.
Import OpNotations.
Import FunctorNotations.

Open Scope category_scope.
Open Scope bishop_scope.

Import IfNotations.

Definition Decidable (T: Type) := ∀ (x y: T), {x = y} + {x ≠ y}.
Existing Class Decidable.

Definition eq_dec {T: Type} `{D:Decidable T} := D.


Definition ns (A: Type): nat → Type :=
  fix loop n :=
    match n with
    | O => True
    | S n' => prod A (loop n')
    end.

#[universes(cumulative)]
Inductive sort {V} :=
| true | false

| prod (_ _: sort)
| Forall (_: V → sort)
| span {E} (_: E → sort)
.
Arguments sort: clear implicits.

Inductive prop {V}: sort V → Type :=
| prop_true: prop true
| prop_false: prop false
| prop_prod {A B}: prop A → prop B → prop (prod A B)
.

Fixpoint pnf {V} (n: nat) (S: sort V): Type :=
  match n with
  | O => prop S
  | S n' =>
    if S is Forall P
    then
      forall x, pnf n' (P x)
    else
      False
  end.

Definition app {V n} {S: sort V} (p:pnf n S): ns V n → sort V.
Proof.
  generalize dependent p.
  generalize dependent S.
  induction n.
  - cbn in *.
    intros.
    apply S.
  - cbn in *.
    destruct S.
    all: try contradiction.
    intro p.
    intro HT.
    destruct HT as [H T].
    apply (IHn (s H) (p _) T).
Defined.



Fixpoint eqb {V} `{Decidable V} (x y: @sort V _): bool :=
  match (x, y) with
  | (true, true) => Datatypes.true
  | (false, false) => Datatypes.true
  | (prod A B, prod A' B') => eqb A A' && eqb B B'
  | (Forsome F, Forsome F') => λ x, eqb (F x) (F x)
  | _ => Datatypes.false
  end.
Instance sort_Decidable V `(Decidable V): Decidable (@sort V _) :=
  λ x y :=
Proof.
  unfold Decidable in *.
  intros x y.
  induction x, y.
  all: try (left; reflexivity).
  all: try (right; discriminate).
  
}.

Definition eq {V: Decidable} (x y: V): sort V := if eq_dec x y then true else false.

Definition η {V: Decidable} (x: V): sort V := Forsome (eq x).

Definition foo {V: Decidable}: sort V := Forall (λ p, prod p p).

Definition st (λ x, η x).

  Inductive term {Var Val: sort → Type}: sort → Type :=
| bang: term pt
| true: term bool | false: term bool

| tuple {A B}: term A → term B → term (prod A B)
| fst {A B}: term (prod A B) → term A
| snd {A B}: term (prod A B) → term B

| app {A B}: term (exp A B) → term A → term B

| var {A}: Var A → term A
| lam {A B}: Var A → (Val A → term B) → term (exp A B)
.

Inductive xs: sort → Type :=
| x: xs pt .
Check lam x (λ x', var x).

Inductive form {V}: nat → Type :=
| η (_: V): form 0
| d {p} (_: form p): form (p + 1)
| wedge {p q} (_: form p) (_: form q): form (p + q)
.
Arguments form: clear implicits.
Infix "∧" := wedge.

Record subset A := sup {
  s: Type ;
  π: s → A ;
}.

Arguments sup {A s}.
Arguments s {A}.
Arguments π {A}.

Notation "'lim' x .. y , P" := (sup (λ x, .. (sup (λ y,  P)) .. )) (at level 200, x binder, y binder).

(* FIXME add complicated setoid relations *)
.
Notation "!" := bang.

Notation "·" := point.
Infix "×" := prod (at level 30, right associativity).

Open Scope nat_scope.

Definition bangRule: subset (form term 1) :=
  lim (x: unit), η ! ∧ d (η ·).

Definition tupleRule: form (subset term) 1 :=
  η (lim (x: unit), !) ∧ d (η (lim (x: unit), ·)).

Definition tupleRule := lim '(e0, e1, A, B), tuple e0 e1 ∈ prod A B.

Definition appRule := λ e0 e1, app e0 e1 ∈ (
                                     η (λ Γ, Γ e0) ∧ η (λ Γ, Γ e1)
                                   ).
#[local]
Obligation Tactic := Reflect.category_simpl.

Reserved Notation "f ◃ g" (at level 30, no associativity).
Reserved Notation "f ▹ g" (at level 30, no associativity).
Reserved Notation "f ▵ g" (at level 30, no associativity).
Reserved Notation "i ~ j" (at level 30, no associativity).

#[universes(cumulative)]
Class Cylinder := {
  Obj: Type ;
  Mor: string → Obj → Obj → Bishop ;

  id [s] A: Mor s A A ;
  compose [s] [A B C]: Mor s B C -> Mor s A B -> Mor s A C
  where "f ∘ g" := (compose f g) ;

  compose_assoc [s A B C D] (f: Mor s C D) (g: Mor s B C) (h: Mor s A B):
    (f ∘ (g ∘ h)) == ((f ∘ g) ∘ h );
  compose_id_left [s A B] (f: Mor s A B): (id B ∘ f) == f ;
  compose_id_right [s A B] (f: Mor s A B): (f ∘ id A) == f ;

  compose_compat [s A B C]: Proper (equiv ==> equiv ==> equiv) (@compose s A B C) ;

  left_commute [A B C] [i j]: Mor i B C -> Mor j A B -> Mor j B C
  where "f ◃ g" := (left_commute f g) ;

  right_commute [A B C] [i j]: Mor i B C -> Mor j A B -> Mor i A B
  where "f ▹ g" := (right_commute f g) ;

  left_right_commute [A B C] [i j]: Mor i B C -> Mor j A B -> (Mor j B C * Mor i A B) :=
   λ f g, (f ◃ g, f ▹ g) ;

     (* FIXME figure out the rest of the laws *)
  left_id [s t A B] (f: Mor t A B): (@id s B ◃ f) == @id t B ;
  right_id [s t A B] (f: Mor s A B): (f ▹ @id t A) == @id s A ;

  left_Proper [s t A B C]: Proper (equiv ==> equiv ==> equiv) (@left_commute s t A B C) ;
  right_Proper [s t A B C]: Proper (equiv ==> equiv ==> equiv) (@right_commute s t A B C) ;

  diag (i j: string): Obj
  where "i ~ j" := (diag i j);

  refl {i A}: Mor i A (i ~ i) ;
  sym {i j}: Mor i (i ~ j) (j ~ i) ;
  trans {i j k A}:
    Mor j A (i ~ j) → Mor j A (j ~ k) → Mor j A (i ~ k) ;
}.

Arguments Obj: clear implicits.
Arguments Mor: clear implicits.

Coercion Obj: Cylinder >-> Sortclass.
Coercion Mor: Cylinder >-> Funclass.

Existing Instance compose_compat.
Existing Instance left_Proper.
Existing Instance right_Proper.

Module Import CylinderNotations.
  Bind Scope category_scope with Cylinder.
  Bind Scope object_scope with Obj.
  Bind Scope morphism_scope with Mor.

  Notation "f ∘ g" := (compose f g) : morphism_scope.
  Notation "f ◃ g" := (left_commute f g) : morphism_scope.
  Notation "f ▹ g" := (right_commute f g) : morphism_scope.
  Notation "f ▵ g" := (left_right_commute f g) : morphism_scope.

  Notation "i ~ j" := (diag i j) : object_scope.

  Notation "A → B" := (Mor _ A B) (only parsing) : bishop_scope.
  Notation "A ~> B" := (Mor _ A B) (only parsing) : bishop_scope.
End CylinderNotations.

Check trans (id _) _.

#[universes(cumulative)]
Class Closed := {
  C: Category ;

  pt: C ;
  prod: Functor (C * C) C ;
  exp: Functor (C ᵒᵖ * C) C ;

  (* FIXME laws *)
  bang x: C x pt ;
  fanout {x y z}: C z x → C z y → C z (prod (x, y)) ;
  π1 {x y}: C (prod (x, y)) x ;
  π2 {x y}: C (prod (x, y)) y ;
}.
Coercion C: Closed >-> Category.
Existing Instance C.

Notation "⊤" := pt.
Notation "A × B" := (prod (A, B)) (at level 30, right associativity).
Notation "[ A , B ]" := (exp (A, B)).

Notation "!" := bang.

#[universes(cumulative)]
Class Cylinder := {
  H (s: string): Closed ;

  diag (x y: string): Bsh ;

  alpha {i j}: Functor (H i) (H j) ;

  (* Seems absurdly wrong *)
  assoc i j: H i b c → H j a b ;
}.
Coercion H: Cylinder >-> Funclass.
Existing Instance H.

Infix "∝" := assoc (at level 30, no associativity).
Infix "~" := diag (at level 30, no associativity).

Section open.
  Context `{C:Cylinder}.

  Check ("x" ∝ "y") (⊤, ⊤).
  Check map ("x" ∝ "y") (id _,  _).
  (! ⊤).
#[universes(cumulative)]
Record Var (C: Category) := {
  pt: C ;
  prod: Functor (C * C) C ;
  exp: Functor (C ᵒᵖ * C) C ;

  (* FIXME laws *)

  bang x: C x pt ;
  push {x y}: C pt x → C y (prod (x, y)) ;

  (* Doesn't seem quite right *)
  π1 {x y}: C (prod (x, y)) x ;
  π2 {x y}: C (prod (x, y)) y ;

  pass {x y}: C pt x → C (exp (x, y)) y ;

  curr {x y z}:
    C (prod (x, y)) z → C y (exp (x, z)) ;
  ev {x y}: C (prod (x, exp (x, y))) y ;
}.

Arguments pt {C}.
Arguments prod {C}.
Arguments exp {C}.

Arguments bang {C}.
Arguments push {C} v {x y}.
Arguments π1 {C} v {x y}.
Arguments π2 {C} v {x y}.

Arguments curr {C} v {x y z}.
Arguments ev {C} v {x y}.

#[universes(cumulative)]
Class Variadic := {
  C: Category;
  (* FIXME require finite ? *)
  α: Type;

  var: α → Var C ;

  diag: α → α → C ;

  assoc {i j} {A B C}:
    prod (var i) (A, prod (var j) (B, C)) ~> prod (var j) (prod (var i) (A, B), C) ;

  (* Just for playing with *)
  Z: C ;
  z i: nat → C (pt (var i)) Z ;
}.

Coercion C: Variadic >-> Category.
Existing Instance C.

Coercion var: α >-> Var.

Notation "⊤" := pt.
Notation "A [ i ]× B" := (prod i (A, B)) (at level 30, right associativity).
Notation "A ~[ i ]> B" := (exp i (A, B)) (at level 90, right associativity).
Notation "!" := bang.

Section open.
  Context `{V:Variadic}.

  Definition foo (i j: α) A: A ~> Z [i]× Z [j]× A :=
    push i (z i 4) ∘ push j (z j 5).

  Definition ident (i j: α) A B: A ~> (B ~[i]> B) :=
    curr i (π1 i).

  Check λ (i: α), curr i (π1 i).
