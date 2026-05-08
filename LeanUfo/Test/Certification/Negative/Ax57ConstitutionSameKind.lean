import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax57 fixture.

Two objects of the same kind are related by constitution.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx57ConstitutionSameKind : UFO where
  worlds actual
  things K X Y
  given actual:
    ObjectKind(K)
    Object(X)
    Object(Y)
    X :: K
    Y :: K
    ConstitutedBy(X, Y)
  derive_relations
  certify
