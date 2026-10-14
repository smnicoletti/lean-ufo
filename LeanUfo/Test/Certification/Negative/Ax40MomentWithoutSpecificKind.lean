import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax40 fixture.

`I` is a moment but neither a relator nor an intrinsic moment.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx40MomentWithoutSpecificKind : UFO where
  worlds actual
  things K I
  given actual:
    ObjectKind(K)
    ConcreteIndividual(I)
    Endurant(I)
    Moment(I)
    I :: K
  derive_relations
  certify
