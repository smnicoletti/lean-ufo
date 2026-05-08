import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure syntax test.

The old unary fact syntax `x : P` is intentionally no longer accepted.  This
file is run by the test driver as a negative parser fixture and must not be
imported by normal modules.
-/

open LeanUfo.UFO.DSL

ufo_model RejectedOldSyntaxExample : UFO where
  worlds actual
  things K I
  given actual:
    I :: K
    I : Object
    K : ObjectKind
  derive_relations
  certify
