import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax25 candidate.

`K` is classified as both a kind and a subkind.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx25KindAndSubKind : UFO where
  worlds actual
  things K I
  given actual:
    Object(I)
    I :: K
    Kind(K)
    SubKind(K)
    ObjectType(K)
  derive_relations
  certify
