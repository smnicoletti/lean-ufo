import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax43 fixture.

`I` is a mode and also instantiates a unique quality kind, which makes it a
quality by the §3.3 derived definition.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx43ModeAndQuality : UFO where
  worlds actual
  things QK I
  given actual:
    QualityKind(QK)
    Mode(I)
    I :: QK
  derive_relations
  certify
