import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax35 fixture.

`I` satisfies the endurant partition extensionally, but is placed on both
disjoint sides of it: substantial and moment.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx35SubstantialAndMoment : UFO where
  worlds actual
  things K I
  given actual:
    ObjectKind(K)
    ConcreteIndividual(I)
    Endurant(I)
    Substantial(I)
    Moment(I)
    I :: K
  derive_relations
  certify
