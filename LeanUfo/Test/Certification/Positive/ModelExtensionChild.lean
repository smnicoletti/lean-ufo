import LeanUfo.Test.Certification.Positive.ModelExtensionBase

open LeanUfo.UFO.DSL

ufo_model TestCrossModuleAlias : UFO extends TestCrossModuleBase : UFO where
  derive_relations
  certify

example : TestCrossModuleAlias.certificateManifest.fields[0]!.status =
    CertificateReuseStatus.reused := by
  rfl

example : TestCrossModuleAlias.certificateManifest.fields[0]!.reusedFrom =
    some "TestCrossModuleBase.checked_ax1" := by
  rfl

example : Checker.checkAx1 TestCrossModuleAlias.data = true :=
  TestCrossModuleAlias.checked_ax1
