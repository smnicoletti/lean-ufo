import LeanUfo.UFO.DSL.ConcreteExamples.ReuseModelExtension

/-!
# Unmarked export-discovery fixture

With no export marker, the exporter selects every manifest owner declared by
this module. Module ownership still excludes manifests from imported modules.
-/

open LeanUfo.UFO.DSL

namespace ExportFallbackFixture

/-
ufo_model CarBase : UFO where
  worlds ignored
  things ignored
  derive_relations
  certify
-/

namespace First

def source := CarBase.source
def tables := CarBase.tables
def certificateManifest : CertificateManifest :=
  { CarBase.certificateManifest with modelName := "ExportFallbackFixture.First" }

end First

namespace Second

def source := CarWithWindow.source
def tables := CarWithWindow.tables
def certificateManifest : CertificateManifest :=
  { CarWithWindow.certificateManifest with modelName := "ExportFallbackFixture.Second" }

end Second

end ExportFallbackFixture
