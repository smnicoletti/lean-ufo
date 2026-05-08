import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax9 fixture.

`I` is an individual because nothing instantiates it, but it is asserted as both
concrete and abstract.  This violates their disjointness.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx9ConcreteAbstract : UFO where
  worlds actual
  things I
  given actual:
    ConcreteIndividual(I)
    AbstractIndividual(I)
  derive_relations
  certify
