import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax61 fixture.

Two objects of different kinds are asserted to constitute each other at the
same world, violating constitution asymmetry.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx61SymmetricConstitution : UFO where
  worlds actual
  things KX KY X Y

  given actual:
    ObjectKind(KX)
    ObjectKind(KY)
    Object(X)
    Object(Y)
    X :: KX
    Y :: KY
    ConstitutedBy(X, Y)
    ConstitutedBy(Y, X)
  derive_relations
  certify
