import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax104 fixture.

`Meet(X,Y)` is asserted while `X` and `Y` are objects, not perdurants.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx104MeetWrongTypes : UFO where
  worlds actual
  things K X Y
  given actual:
    ObjectKind(K)
    Object(X)
    Object(Y)
    X :: K
    Y :: K
    Meet(X, Y)
  derive_relations
  certify
