import LeanUfo.Test.Coverage.AxiomManifest
import LeanUfo.UFO.DSL.Certificate.Reuse

/-!
Importable coverage marker.

The executable test runner compares this manifest against the command
frontend's certificate registry by reading both source files.  Keeping this as
a Lean module ensures the manifest itself remains syntactically checked.
-/

example : axiomCoverageManifest.size = 116 := by
  native_decide

example :
    (LeanUfo.UFO.DSL.reusableFieldFootprint? "ax73").map
      (fun footprint => footprint.binary.contains "part") = some true := by
  native_decide

example :
    (LeanUfo.UFO.DSL.reusableFieldFootprint? "ax73").map
      (fun footprint => footprint.binary.contains "overlap") = some false := by
  native_decide
