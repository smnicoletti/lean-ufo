import LeanUfo.UFO.DSL.ConcreteExamples.ReuseModelExtension

/-!
# Marked export-discovery fixture

The exporter must use compiled declarations, not text that resembles DSL
commands. This module defines two namespaced manifest owners and marks one.
Imported manifests belong to another module and must not enter the result.
-/

open LeanUfo.UFO.DSL

namespace ExportDiscoveryFixture

ufo_model Base : UFO where
  worlds actual
  things K I
  given actual:
    I :: K
    Object(I)
    ObjectKind(K)
  derive_relations
  certify

ufo_model Selected : UFO extends Base : UFO where
  derive_relations
  certify

export_certificate Selected

namespace Unselected

def source := CarWithWindow.source
def tables := CarWithWindow.tables
def certificateManifest : CertificateManifest :=
  { CarWithWindow.certificateManifest with modelName := "ExportDiscoveryFixture.Unselected" }

end Unselected

-- export_certificate Unselected
/-
ufo_model CommentedModel : UFO where
  worlds w
  things x
  derive_relations
  certify
-/

end ExportDiscoveryFixture
