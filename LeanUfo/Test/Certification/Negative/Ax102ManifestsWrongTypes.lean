import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax102 fixture.

`Manifests(P,E)` is asserted while `P` is not classified as a perdurant.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx102ManifestsWrongTypes : UFO where
  worlds actual
  things K P E
  given actual:
    ObjectKind(K)
    Object(P)
    Object(E)
    P :: K
    E :: K
    Manifests(P, E)
  derive_relations
  certify
