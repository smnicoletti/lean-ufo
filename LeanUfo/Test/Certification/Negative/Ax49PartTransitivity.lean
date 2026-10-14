import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax49 fixture.

`A` is part of `B` and `B` is part of `C`, but `A` is not part of `C`.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx49PartTransitivity : UFO where
  worlds actual
  things K A B C
  given actual:
    ObjectKind(K)
    Object(A)
    Object(B)
    Object(C)
    A :: K
    B :: K
    C :: K
    Part(A, B)
    Part(B, C)
  derive_relations
  certify
