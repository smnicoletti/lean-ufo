import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax50 fixture.

`A` and `B` are asserted to overlap, but the finite part table contains no
common part for them.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx50OverlapWithoutCommonPart : UFO where
  worlds actual
  things K A B
  given actual:
    ObjectKind(K)
    Object(A)
    Object(B)
    A :: K
    B :: K
    Overlap(A, B)
  derive_relations
  certify
