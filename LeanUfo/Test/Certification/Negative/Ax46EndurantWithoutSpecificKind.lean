import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax46 fixture.

`I` is an endurant object and necessarily instantiates a generic `Kind`, which
satisfies ax21.  The kind is not one of the specific endurant kinds required by
ax46.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx46EndurantWithoutSpecificKind : UFO where
  worlds actual
  things K I
  given actual:
    Kind(K)
    Object(I)
    I :: K
  derive_relations
  certify
