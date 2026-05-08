import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax80 fixture.

`Mediates(R,B)` is asserted even though `R` is not a relator and no qua
individual part witnesses mediation.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx80MediatesWithoutRelator : UFO where
  worlds actual
  things K R B
  given actual:
    ObjectKind(K)
    Object(R)
    Object(B)
    R :: K
    B :: K
    Mediates(R, B)
  derive_relations
  certify
