import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax68 fixture.

`M` is a mode, hence a moment, but it has no `InheresIn` chain to any
non-moment bearer.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx68MomentWithoutUltimateBearer : UFO where
  worlds actual
  things MK M
  given actual:
    ModeKind(MK)
    Mode(M)
    M :: MK
  derive_relations
  certify
