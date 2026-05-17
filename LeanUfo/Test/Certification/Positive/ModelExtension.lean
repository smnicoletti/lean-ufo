import LeanUfo.UFO.DSL.Syntax

/-!
Positive fixtures for incremental certificate artifacts and conservative
certificate reuse.
-/

open LeanUfo.UFO.DSL

def manifestFieldStatus? (manifest : CertificateManifest) (field : String) :
    Option CertificateReuseStatus :=
  manifest.fields.findSome? fun row =>
    if row.field == field then some row.status else none

ufo_model TestExtensionBase : UFO where
  worlds actual
  things PhysicalObject Car
  given actual:
    Car :: PhysicalObject
    Object(Car)
    ObjectKind(PhysicalObject)
  derive_relations
  certify

ufo_model TestExtensionAlias : UFO extends TestExtensionBase : UFO where
  derive_relations
  certify

ufo_model TestExtensionAliasFresh : UFO extends TestExtensionBase : UFO where
  derive_relations
  certify_fresh

ufo_model TestExtensionGrowth : UFO extends TestExtensionBase : UFO where
  things Window Body
  given actual:
    Window :: PhysicalObject
    Body :: PhysicalObject
    Object(Window)
    Object(Body)
    Part(PhysicalObject, PhysicalObject)
    Part(Car, Car)
    Part(Window, Window)
    Part(Body, Body)
    Part(Window, Car)
    Part(Body, Car)
    Overlap(PhysicalObject, PhysicalObject)
    Overlap(Car, Car)
    Overlap(Window, Window)
    Overlap(Body, Body)
    Overlap(Window, Car)
    Overlap(Car, Window)
    Overlap(Body, Car)
    Overlap(Car, Body)
    ProperPart(Window, Car)
    ProperPart(Body, Car)
  derive_relations
  certify

example : TestExtensionAlias.certificateManifest.fields[0]!.status =
    CertificateReuseStatus.reused := by
  rfl

example : TestExtensionAlias.certificateManifest.fields[0]!.reusedFrom =
    some "TestExtensionBase.checked_ax1" := by
  rfl

example : TestExtensionAliasFresh.certificateManifest.fields[0]!.status =
    CertificateReuseStatus.fresh := by
  rfl

example : TestExtensionGrowth.certificateManifest.fields[0]!.status =
    CertificateReuseStatus.fresh := by
  rfl

example : manifestFieldStatus? TestExtensionGrowth.certificateManifest "ax13" =
    some CertificateReuseStatus.fresh := by
  native_decide

example : manifestFieldStatus? TestExtensionGrowth.certificateManifest "ax61" =
    some CertificateReuseStatus.reused := by
  native_decide

example : manifestFieldStatus? TestExtensionGrowth.certificateManifest "ax68" =
    some CertificateReuseStatus.reused := by
  native_decide

example : manifestFieldStatus? TestExtensionGrowth.certificateManifest "ax101" =
    some CertificateReuseStatus.reused := by
  native_decide

example : manifestFieldStatus? TestExtensionGrowth.certificateManifest "ax47" =
    some CertificateReuseStatus.fresh := by
  native_decide

example : manifestFieldStatus? TestExtensionGrowth.certificateManifest "ax52" =
    some CertificateReuseStatus.fresh := by
  native_decide

example : manifestFieldStatus? TestExtensionGrowth.certificateManifest "ax100" =
    some CertificateReuseStatus.reused := by
  native_decide

example : manifestFieldStatus? TestExtensionAliasFresh.certificateManifest "ax61" =
    some CertificateReuseStatus.fresh := by
  native_decide

example : Checker.checkAx1 TestExtensionAlias.data = true :=
  TestExtensionAlias.checked_ax1

example : UFOAxioms4 TestExtensionGrowth.sig :=
  TestExtensionGrowth.certified

example : Lean.Json :=
  TestExtensionGrowth.certificateManifest.toJson

ufo_model TestEverywhereExtensionBase : UFO where
  worlds actual future
  things Person Alice

  given everywhere:
    ObjectKind(Person)
    Object(Alice)
    Alice :: Person

  derive_relations
  certify

ufo_model TestEverywhereExtensionChild : UFO extends TestEverywhereExtensionBase : UFO where
  things Bob

  given everywhere:
    Object(Bob)
    Bob :: Person

  derive_relations
  certify

example : TestEverywhereExtensionChild.data.object
    (⟨1, by decide⟩ : Fin TestEverywhereExtensionChild.data.thingCount)
    (⟨0, by decide⟩ : Fin TestEverywhereExtensionChild.data.worldCount) = true := by
  native_decide

example : TestEverywhereExtensionChild.data.object
    (⟨1, by decide⟩ : Fin TestEverywhereExtensionChild.data.thingCount)
    (⟨1, by decide⟩ : Fin TestEverywhereExtensionChild.data.worldCount) = true := by
  native_decide

example : TestEverywhereExtensionChild.data.inst
    (⟨1, by decide⟩ : Fin TestEverywhereExtensionChild.data.thingCount)
    (⟨0, by decide⟩ : Fin TestEverywhereExtensionChild.data.thingCount)
    (⟨0, by decide⟩ : Fin TestEverywhereExtensionChild.data.worldCount) = true := by
  native_decide

example : TestEverywhereExtensionChild.data.inst
    (⟨1, by decide⟩ : Fin TestEverywhereExtensionChild.data.thingCount)
    (⟨0, by decide⟩ : Fin TestEverywhereExtensionChild.data.thingCount)
    (⟨1, by decide⟩ : Fin TestEverywhereExtensionChild.data.worldCount) = true := by
  native_decide
