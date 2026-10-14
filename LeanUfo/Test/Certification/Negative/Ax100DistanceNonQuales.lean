import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax100 fixture.

`Distance(X,Y,R)` is asserted even though `X` and `Y` are not quales.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx100DistanceNonQuales : UFO where
  worlds actual
  things X Y R
  given actual:
    AbstractIndividual(X)
    AbstractIndividual(Y)
    AbstractIndividual(R)
    Distance(X, Y, R)
  derive_relations
  certify
