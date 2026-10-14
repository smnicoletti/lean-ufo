import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax24 candidate.

`K` is an object kind, hence a sortal endurant type, but it is also asserted as
non-sortal.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx24NonSortalSortal : UFO where
  worlds actual
  things K I
  given actual:
    ObjectKind(K)
    NonSortal(K)
    Object(I)
    I :: K
  derive_relations
  certify
