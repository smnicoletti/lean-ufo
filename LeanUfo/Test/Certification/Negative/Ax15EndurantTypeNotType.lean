import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax15 fixture.

`T` is an abstract individual because nothing instantiates it, but it is also
asserted as an endurant type.  This violates `EndurantType(x) -> Type(x)`.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx15EndurantTypeNotType : UFO where
  worlds actual
  things T
  given actual:
    AbstractIndividual(T)
    EndurantType(T)
  derive_relations
  certify
