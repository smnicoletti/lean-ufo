import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax65 fixture.

`M` inheres in `B` and exists at `actual`, but `B` does not exist there.  This
makes the existential-dependence consequence of inherence non-vacuously false.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx65InherenceExistingMomentWithoutBearerExistence : UFO where
  worlds actual
  things BK MK B M
  given actual:
    ObjectKind(BK)
    ModeKind(MK)
    Object(B)
    Mode(M)
    B :: BK
    M :: MK
    Ex(M)
    InheresIn(M, B)
  derive_relations
  certify
