import LeanUfo.Test.Coverage.AxiomManifest

/-!
Importable coverage marker.

The executable test runner compares this manifest against the command
frontend's certificate registry by reading both source files.  Keeping this as
a Lean module ensures the manifest itself remains syntactically checked.
-/

example : axiomCoverageManifest.size = 116 := by
  native_decide
