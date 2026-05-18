import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax21 fixture.

`X` is a stable object, but no kind is available as its necessary kind.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx21EndurantNoKind : UFO where
  worlds actual
  things X
  given actual:
    Object(X)
  derive_relations
  certify
