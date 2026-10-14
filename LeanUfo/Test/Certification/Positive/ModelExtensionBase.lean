import LeanUfo.UFO.DSL.Syntax

open LeanUfo.UFO.DSL

ufo_model TestCrossModuleBase : UFO where
  worlds actual
  things PhysicalObject Car
  given actual:
    Car :: PhysicalObject
    Object(Car)
    ObjectKind(PhysicalObject)
  derive_relations
  certify

export_certificate TestCrossModuleBase
