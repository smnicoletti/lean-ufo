import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax16 fixture.

`T` is an abstract individual because nothing instantiates it, but it is also
asserted as a perdurant type.  This violates `PerdurantType(x) -> Type(x)`.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx16PerdurantTypeNotType : UFO where
  worlds actual
  things T
  given actual:
    AbstractIndividual(T)
    PerdurantType(T)
  derive_relations
  certify
