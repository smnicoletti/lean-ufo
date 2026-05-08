import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax71 fixture.

A relator is founded by an object, but foundations must be perdurants.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx71FoundedByWrongFoundationType : UFO where
  worlds actual
  things RK K R B
  given actual:
    RelatorKind(RK)
    ObjectKind(K)
    Relator(R)
    Moment(R)
    Object(B)
    R :: RK
    B :: K
    FoundedBy(R, B)
  derive_relations
  certify
