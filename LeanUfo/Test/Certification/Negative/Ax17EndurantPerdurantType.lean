import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax17 fixture.

`T` has an instance, so it behaves as a type, but it is classified as both an
endurant type and a perdurant type.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx17EndurantPerdurantType : UFO where
  worlds actual
  things T I
  given actual:
    I :: T
    Object(I)
    EndurantType(T)
    PerdurantType(T)
  derive_relations
  certify
