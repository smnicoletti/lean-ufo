import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax26 candidate.

`T` is made a rigid sortal under kind `K`, but is not classified as either a
kind or a subkind.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx26RigidSortalNeitherKindNorSubKind : UFO where
  worlds actual
  things K T I
  given actual:
    ObjectKind(K)
    ObjectType(T)
    Rigid(T)
    Sortal(T)
    T ⊑ K
    Object(I)
    I :: T
    I :: K
  derive_relations
  certify
