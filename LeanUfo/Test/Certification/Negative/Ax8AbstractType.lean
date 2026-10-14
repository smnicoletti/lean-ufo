import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax8 fixture.

`T` behaves as a type because `I :: T`, but it is also asserted as an abstract
individual.  This violates `AbstractIndividual(x) -> Individual(x)`.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx8AbstractType : UFO where
  worlds actual
  things T I
  given actual:
    I :: T
    AbstractIndividual(T)
  derive_relations
  certify
