import LeanUfo.UFO.DSL.Syntax

/-
Negative diagnostic example: symmetric constitution between two endurants.

This is a small variation of `WoodenTable.lean`.  The passing example has one
endurant constituting another endurant.  Here the constitution relation is
asserted in both directions, violating the asymmetry constraint.

The model is intentionally not certifiable.  Open this file in VS Code to see
the UFO diagnostics widget stop at `certified_ax61`.
-/

open LeanUfo.UFO.DSL

ufo_model FailedConstitutionExample : UFO where
  worlds w1 w2
  things
    WoodPortion
    WoodenTableComponent
    Object0
    Object1

  given everywhere:
    QuantityKind(WoodPortion)
    ObjectKind(WoodenTableComponent)
    Quantity(Object0)
    Object0 :: WoodPortion

    Object(Object1)
    Object1 :: WoodenTableComponent

  given w1:
    Ex(Object0)
  given w2:
    Ex(Object0)
    Ex(Object1)
    ConstitutedBy(Object1, Object0)
    ConstitutedBy(Object0, Object1)
  derive_relations
  certify
