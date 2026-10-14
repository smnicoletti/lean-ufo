import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax51 fixture.

`Y` is not part of `X`, but every available part of `Y` overlaps `X`.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx51StrongSupplementation : UFO where
  worlds actual
  things K X Y Z
  given actual:
    ObjectKind(K)
    Object(X)
    Object(Y)
    Object(Z)
    X :: K
    Y :: K
    Z :: K
    Part(Z, Y)
    Part(Z, X)
    Overlap(X, Y)
    Overlap(X, Z)
    Overlap(Y, X)
    Overlap(Y, Z)
    Overlap(Z, X)
    Overlap(Z, Y)
  derive_relations
  certify
