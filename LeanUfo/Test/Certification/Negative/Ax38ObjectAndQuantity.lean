import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax38 fixture.

`I` is classified as both object and quantity.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx38ObjectAndQuantity : UFO where
  worlds actual
  things K I
  given actual:
    ObjectKind(K)
    Object(I)
    Quantity(I)
    I :: K
  derive_relations
  certify
