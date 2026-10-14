import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax66 fixture.

An object is asserted to inhere in another object, but inherence requires the
inhering entity to be a moment.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx66InherenceFromNonMoment : UFO where
  worlds actual
  things K X B
  given actual:
    ObjectKind(K)
    Object(X)
    Object(B)
    X :: K
    B :: K
    InheresIn(X, B)
  derive_relations
  certify
