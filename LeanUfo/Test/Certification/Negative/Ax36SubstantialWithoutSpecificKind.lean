import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax36 fixture.

`I` is substantial but none of the specific substantial predicates
(`Object`, `Collective`, `Quantity`) hold.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx36SubstantialWithoutSpecificKind : UFO where
  worlds actual
  things K I
  given actual:
    ObjectKind(K)
    ConcreteIndividual(I)
    Endurant(I)
    Substantial(I)
    I :: K
  derive_relations
  certify
