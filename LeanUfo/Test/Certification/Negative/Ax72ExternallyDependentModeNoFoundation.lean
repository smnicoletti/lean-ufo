import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax72 fixture.

`M` becomes an externally dependent mode in the finite taxonomy, but no
foundation is available for it.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx72ExternallyDependentModeNoFoundation : UFO where
  worlds actual
  things MK M
  given actual:
    ModeKind(MK)
    Mode(M)
    M :: MK
  derive_relations
  certify
