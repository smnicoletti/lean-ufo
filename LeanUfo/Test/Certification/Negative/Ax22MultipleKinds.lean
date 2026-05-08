import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax22 fixture.

`X` instantiates two distinct kinds.  This was first discovered while attempting
to isolate ax6; the useful first failure is ax22, so the fixture is kept here.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx22MultipleKinds : UFO where
  worlds actual
  things T1 T2 X
  given actual:
    ObjectKind(T1)
    ObjectKind(T2)
    Object(X)
    X :: T1
    X :: T2
  derive_relations
  certify
