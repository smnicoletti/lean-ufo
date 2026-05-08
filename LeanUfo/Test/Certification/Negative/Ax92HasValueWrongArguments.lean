import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax92 fixture.

`HasValue(X, Y)` is asserted for an object and a non-quale abstract individual.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx92HasValueWrongArguments : UFO where
  worlds actual
  things K X Y
  given actual:
    Kind(K)
    ObjectKind(K)
    X :: K
    ConcreteIndividual(X)
    Endurant(X)
    Object(X)
    AbstractIndividual(Y)
    HasValue(X, Y)
  derive_relations
  certify
