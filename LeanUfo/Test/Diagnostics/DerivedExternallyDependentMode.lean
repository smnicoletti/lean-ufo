import LeanUfo.UFO.DSL.Syntax

/-!
Diagnostic fixture for a failing user-written derived assertion.

The model asserts `ExternallyDependentMode(M)`, but the finite computed
semantics has no modal `Ex` variation that can witness external dependence.
-/

open LeanUfo.UFO.DSL

ufo_model FailedDerivedExternallyDependentMode : UFO where
  worlds actual
  things ModeKind1 ObjectKind1 M B

  given actual:
    ModeKind(ModeKind1)
    ObjectKind(ObjectKind1)
    Mode(M)
    Object(B)
    M :: ModeKind1
    B :: ObjectKind1
    InheresIn(M, B)
    ExternallyDependentMode(M)

  derive_relations
  certify
