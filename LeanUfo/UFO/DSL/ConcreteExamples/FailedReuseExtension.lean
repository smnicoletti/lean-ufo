import LeanUfo.UFO.DSL.Syntax

/-!
# Failed reuse extension example

This diagnostic example shows a certifying base model followed by an invalid
extension.  `ValidVehicleBaseExample` certifies.  The child extension adds
`Perdurant(Car)`, which conflicts with the inherited `Object(Car)` taxonomy:
objects are endurants, and ax13 disallows endurant/perdurant overlap.

This file is intentionally not imported by `LeanUfo.UFO.DSL.Examples`, because
it is expected to fail.  Open it directly in VS Code to inspect the failed
extension diagnostics.
-/

open LeanUfo.UFO.DSL

ufo_model ValidVehicleBaseExample : UFO where
  worlds actual
  things PhysicalObject Car

  given actual:
    ObjectKind(PhysicalObject)
    Object(Car)
    Car :: PhysicalObject

  derive_relations
  certify

ufo_model InvalidVehicleExtensionExample : UFO extends ValidVehicleBaseExample : UFO where
  given actual:
    Perdurant(Car)

  derive_relations
  certify
