import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax18 fixture.

`T` is an instantiated endurant type, so rigidity is required by ax18, but no
rigidity fact is asserted.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx18AntiRigidKind : UFO where
  worlds actual
  things T I

  given actual:
    EndurantType(T)
    Object(I)
    I :: T

  derive_relations
  certify
