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
    WoodPortion : QuantityKind

    WoodenTableComponent : ObjectKind

    Object0 : Quantity
    Object0 :: WoodPortion

    Object1 : Object
    Object1 :: WoodenTableComponent

  given w1:
    Object0 : Ex

  given w2:
    Object0 : Ex
    Object1 : Ex
    Object1 ConstitutedBy Object0
    Object0 ConstitutedBy Object1

  derive_relations
  certify
