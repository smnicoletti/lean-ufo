import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax52 fixture.

`A` is asserted as a proper part of `B` without the corresponding parthood
fact.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx52ProperPartWithoutPart : UFO where
  worlds actual
  things K A B
  given actual:
    ObjectKind(K)
    Object(A)
    Object(B)
    A :: K
    B :: K
    ProperPart(A, B)
  derive_relations
  certify
