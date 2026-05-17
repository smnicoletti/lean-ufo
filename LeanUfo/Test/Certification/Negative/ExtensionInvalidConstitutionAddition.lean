import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure extension fixture.

The parent model certifies.  The child extension adds symmetric constitution
facts, so many early checker fields can complete before certification fails at
ax61.
-/

open LeanUfo.UFO.DSL

ufo_model ValidConstitutionExtensionBase : UFO where
  worlds actual
  things KX KY X Y

  given actual:
    ObjectKind(KX)
    ObjectKind(KY)
    Object(X)
    Object(Y)
    X :: KX
    Y :: KY

  derive_relations
  certify

ufo_model InvalidConstitutionExtension : UFO extends ValidConstitutionExtensionBase : UFO where
  given actual:
    ConstitutedBy(X, Y)
    ConstitutedBy(Y, X)

  derive_relations
  certify
