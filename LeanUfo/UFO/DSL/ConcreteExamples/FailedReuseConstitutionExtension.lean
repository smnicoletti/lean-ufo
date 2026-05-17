import LeanUfo.UFO.DSL.Syntax

/-!
# Failed reuse constitution extension example

This diagnostic example shows a base model that certifies, followed by an
extension that reuses many early certificate fields before failing later at
`ax61`.

The base model introduces two objects of different kinds.  The child extension
adds symmetric `ConstitutedBy` facts.  This violates the constitution
asymmetry/non-reflexivity constraints while leaving many earlier taxonomy and
classification checks reusable from the parent.

This file is intentionally not imported by `LeanUfo.UFO.DSL.Examples`, because
it is expected to fail.  Open it directly in VS Code to inspect both the reuse
summary and the later failed certificate field.
-/

open LeanUfo.UFO.DSL

ufo_model ValidConstitutionBaseExample : UFO where
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

ufo_model InvalidSymmetricConstitutionExtensionExample : UFO extends ValidConstitutionBaseExample : UFO where
  given actual:
    ConstitutedBy(X, Y)
    ConstitutedBy(Y, X)

  derive_relations
  certify
