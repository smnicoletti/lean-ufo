import LeanUfo.Test.Certificates.ExportDiscoveryMarked

/-!
# Parent lookup across namespaces and modules

A cached root model must not hide a nearer parent imported into the current
namespace. The two parents have different world names, so the source assertion
detects selection of the wrong parent even when both models certify.
-/

open LeanUfo.UFO.DSL

ufo_model Base : UFO where
  worlds other
  things K I
  given other:
    I :: K
    Object(I)
    ObjectKind(K)
  derive_relations
  certify

namespace ExportDiscoveryFixture

ufo_model ImportedChild : UFO extends Base : UFO where
  derive_relations
  certify

example : ImportedChild.source.worlds = #["actual"] := by decide

end ExportDiscoveryFixture
