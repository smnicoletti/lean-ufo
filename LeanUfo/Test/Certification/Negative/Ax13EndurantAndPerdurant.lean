import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax13 fixture.

One thing is an object, hence an endurant, and is also explicitly asserted as a
perdurant.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx13EndurantAndPerdurant : UFO where
  worlds actual
  things X

  given actual:
    Object(X)
    Perdurant(X)

  derive_relations
  certify
