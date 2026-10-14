import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax42 fixture.

`I` is an intrinsic moment but is not classified as either mode or quality.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx42IntrinsicMomentWithoutModeOrQuality : UFO where
  worlds actual
  things K I
  given actual:
    ObjectKind(K)
    IntrinsicMoment(I)
    I :: K
  derive_relations
  certify
