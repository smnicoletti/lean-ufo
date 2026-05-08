import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax21 fixture.

`X` is a stable object, but no kind is available as its necessary kind.  This
was first discovered while attempting to isolate ax4; the useful first failure
is ax21, so the fixture is kept here.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx21EndurantNoKind : UFO where
  worlds actual
  things A B C X
  given actual:
    Object(X)
    X :: A
    A :: B
    B :: C
  derive_relations
  certify
