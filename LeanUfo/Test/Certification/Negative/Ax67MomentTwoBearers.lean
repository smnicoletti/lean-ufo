import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax67 fixture.

The same mode inheres in two distinct bearers.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx67MomentTwoBearers : UFO where
  worlds actual
  things BK MK M B1 B2
  given actual:
    ObjectKind(BK)
    ModeKind(MK)
    Mode(M)
    Object(B1)
    Object(B2)
    M :: MK
    B1 :: BK
    B2 :: BK
    InheresIn(M, B1)
    InheresIn(M, B2)
  derive_relations
  certify
