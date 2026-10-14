import LeanUfo.UFO.DSL.Syntax

/-!
Self-contained positive ultimate-bearer fixture for the test suite.

The mode `AppleColorMode` inheres in `Apple1`, supplying the ultimate bearer
needed by ax68 in the generated finite model.
-/

open LeanUfo.UFO.DSL

ufo_model TestUltimateBearerExample : UFO where
  worlds actual
  things Apple ColorModeKind Apple1 AppleColorMode

  given actual:
    ObjectKind(Apple)
    Object(Apple1)
    Apple1 :: Apple

    ModeKind(ColorModeKind)
    AppleColorMode :: ColorModeKind
    IntrinsicMoment(AppleColorMode)
    Mode(AppleColorMode)
    InheresIn(AppleColorMode, Apple1)
  derive_relations
  certify

