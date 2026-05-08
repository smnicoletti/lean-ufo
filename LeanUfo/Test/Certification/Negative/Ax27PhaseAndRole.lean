import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax27 candidate.

`T` is classified as both a phase and a role.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx27PhaseAndRole : UFO where
  worlds actual future
  things K T I
  given everywhere:
    ObjectKind(K)
    ObjectType(T)
    Phase(T)
    Role(T)
    T ⊑ K
    Object(I)
    I :: K
  given actual:
    I :: T
  derive_relations
  certify
