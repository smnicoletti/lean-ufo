import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax45 fixture.

`K` is both a kind and an object type, so the right-hand side of the
`ObjectKind` definition holds, but `ObjectKind(K)` itself is not asserted or
derived.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx45ObjectTypeKindNotObjectKind : UFO where
  worlds actual
  things K I
  given actual:
    Kind(K)
    ObjectType(K)
    Object(I)
    I :: K
  derive_relations
  certify
