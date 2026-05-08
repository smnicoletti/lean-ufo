import LeanUfo.UFO.DSL.Syntax

/-!
Candidate ax81 fixture.

`Characterization(T, M)` is asserted, but neither endpoint is given the type
classification required by ax81.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx81CharacterizationWrongTypes : UFO where
  worlds actual
  things T M
  given actual:
    AbstractIndividual(T)
    AbstractIndividual(M)
    Characterization(T, M)
  derive_relations
  certify

