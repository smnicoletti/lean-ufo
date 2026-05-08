import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax56 fixture.

An object is asserted to be constituted by a perdurant, violating the
same-category requirement for constitution.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx56ConstitutionDifferentCategory : UFO where
  worlds actual
  things K X Y
  given actual:
    ObjectKind(K)
    Object(X)
    X :: K
    Perdurant(Y)
    ConstitutedBy(X, Y)
  derive_relations
  certify
