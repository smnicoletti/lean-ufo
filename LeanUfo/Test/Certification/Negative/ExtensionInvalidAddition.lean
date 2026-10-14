import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure extension fixture.

The parent model certifies.  The child extension then adds `Perdurant(Car)`,
which conflicts with the inherited `Object(Car)` classification because objects
are endurants and ax13 disallows an individual from being both an endurant and a
perdurant.
-/

open LeanUfo.UFO.DSL

ufo_model ValidVehicleBase : UFO where
  worlds actual
  things PhysicalObject Car

  given actual:
    ObjectKind(PhysicalObject)
    Object(Car)
    Car :: PhysicalObject

  derive_relations
  certify

ufo_model InvalidVehicleExtension : UFO extends ValidVehicleBase : UFO where
  given actual:
    Perdurant(Car)

  derive_relations
  certify
