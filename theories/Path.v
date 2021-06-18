Require Import Blech.Defaults.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Require Import Blech.Bishop.
Require Blech.Reflect.

Import BishopNotations.

Open Scope bishop_scope.



(* Dumb name but I don't really know a better name for single sorted
categories and I had to give *some* name *)
#[universes(cumulative)]
Class Path := {
  P: Bishop ;

  s: P → P ;
  t: P → P ;

  glue: { '(x, y) | s x = t y } -> P ;

  glue_assoc f g h p q r s:
    glue (exist _ (f, glue (exist _ (g, h) p)) q) == glue (exist _ (glue (exist _ (f, g) r), h) s) ;

  s_s x: s (s x) == s x ;
  t_s x: t (s x) == s x ;

  s_t x: s (t x) == t x ;
  t_t x: t (t x) == t x ;

  s_glue x y p: t (glue (exist _ (x, y) p)) == t x ;
  t_glue x y p: s (glue (exist _ (x, y) p)) == s y ;

  s_compat x x': x == x' → s x == s x' ;
  t_compat x x': x == x' → t x == t x' ;
  glue_compat f f' g g' p q:
  f == f' → g == g' → glue (exist _ (f, g) p) == glue (exist _ (f', g') q) ;
}.

Arguments P: clear implicits.

Module Export PathNotations.
  Declare Scope path_scope.
  Delimit Scope path_scope with path.

  Bind Scope path_scope with P.

  Coercion P: Path >-> Bishop.
End PathNotations.

Add Parametric Morphism (P:Path) : (@s P)
    with signature equiv ==> equiv as s_mor.
Proof.
  apply s_compat.
Qed.

Add Parametric Morphism (P:Path) : (@t P)
    with signature equiv ==> equiv as t_mor.
Proof.
  apply t_compat.
Qed.
