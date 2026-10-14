import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax7 fixture.

`T` behaves as a type because `I :: T`, but it is also asserted as a concrete
individual.  This violates `ConcreteIndividual(x) -> Individual(x)`.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx7ConcreteType : UFO where
  worlds actual
  things T I
  given actual:
    I :: T
    ConcreteIndividual(T)
  derive_relations
  certify
