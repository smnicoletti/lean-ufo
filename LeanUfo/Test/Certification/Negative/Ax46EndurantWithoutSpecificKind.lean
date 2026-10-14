import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax46 fixture.

`I` is an endurant object and necessarily instantiates a generic `Kind`, which
satisfies ax21.  A collective co-instance keeps the generic kind from collapsing
to `ObjectKind`, so the kind is not one of the specific endurant kinds required
by ax46.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx46EndurantWithoutSpecificKind : UFO where
  worlds actual
  things K I J
  given actual:
    Kind(K)
    SubstantialType(K)
    Object(I)
    Collective(J)
    I :: K
    J :: K
  derive_relations
  certify
