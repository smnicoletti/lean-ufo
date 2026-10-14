import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax48 fixture.

Two distinct things are asserted as parts of one another.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx48PartAntisymmetry : UFO where
  worlds actual
  things K A B
  given actual:
    ObjectKind(K)
    Object(A)
    Object(B)
    A :: K
    B :: K
    Part(A, B)
    Part(B, A)
  derive_relations
  certify
