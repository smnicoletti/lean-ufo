import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax87 fixture.

`V` is asserted as a quale but is not tied to any quality structure by
membership facts.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx87QualeWithoutUniqueQualityStructure : UFO where
  worlds actual
  things V
  given actual:
    Quale(V)
    AbstractIndividual(V)
  derive_relations
  certify
