import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax39 fixture.

`I` is classified as both collective and quantity.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx39CollectiveAndQuantity : UFO where
  worlds actual
  things K I
  given actual:
    ObjectKind(K)
    Collective(I)
    Quantity(I)
    I :: K
  derive_relations
  certify
