import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax14 fixture.

`I` is asserted as a concrete individual without being classified as either an
endurant or a perdurant.  This violates the concrete-individual biconditional.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx14ConcreteNeitherEndurantNorPerdurant : UFO where
  worlds actual
  things I
  given actual:
    ConcreteIndividual(I)
  derive_relations
  certify
