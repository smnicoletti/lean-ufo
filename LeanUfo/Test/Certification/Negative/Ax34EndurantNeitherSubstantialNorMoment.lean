import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax34 fixture.

`I` is a concrete endurant, but it is not classified as either substantial or
moment.  Earlier individual-level partitions are satisfied explicitly; the
first semantic failure should therefore be the §3.3 endurant partition.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx34EndurantNeitherSubstantialNorMoment : UFO where
  worlds actual
  things K I
  given actual:
    ObjectKind(K)
    ConcreteIndividual(I)
    Endurant(I)
    I :: K
  derive_relations
  certify
