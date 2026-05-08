import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax41 fixture.

`I` is classified as both relator and intrinsic moment.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx41RelatorAndIntrinsicMoment : UFO where
  worlds actual
  things K I
  given actual:
    ObjectKind(K)
    Relator(I)
    IntrinsicMoment(I)
    I :: K
  derive_relations
  certify
