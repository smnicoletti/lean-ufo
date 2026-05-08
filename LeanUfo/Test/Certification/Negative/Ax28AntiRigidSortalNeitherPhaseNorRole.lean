import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax28 candidate.

`T` is an anti-rigid sortal under kind `K`, but is not classified as either a
phase or a role.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx28AntiRigidSortalNeitherPhaseNorRole : UFO where
  worlds actual future
  things K T I
  given everywhere:
    ObjectKind(K)
    ObjectType(T)
    AntiRigid(T)
    Sortal(T)
    T ⊑ K
    Object(I)
    I :: K
  given actual:
    I :: T
  derive_relations
  certify
