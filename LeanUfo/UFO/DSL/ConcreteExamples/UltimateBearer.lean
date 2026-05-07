import LeanUfo.UFO.DSL.Syntax

/-
Small ultimate-bearer example.

`AppleColorMode` is a mode, hence an intrinsic moment.  The full UFO
certificate requires every moment to have a unique ultimate bearer.  The direct
inherence fact below makes `Apple1` that bearer.
-/

open LeanUfo.UFO.DSL

ufo_model UltimateBearerExample : UFO where
  worlds actual
  things Apple ColorModeKind Apple1 AppleColorMode

  given actual:
    Apple : ObjectKind
    Apple1 : Object
    Apple1 :: Apple

    ColorModeKind : ModeKind
    AppleColorMode :: ColorModeKind
    AppleColorMode : IntrinsicMoment
    AppleColorMode : Mode
    AppleColorMode InheresIn Apple1

  derive_relations
  certify
