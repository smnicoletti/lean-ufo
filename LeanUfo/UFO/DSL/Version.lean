/-!
# DSL artifact version metadata

This module centralizes version strings used in generated certificate
manifests. The release manifest workflow rewrites `artifactVersion` in its
runner workspace before exporting published manifests. Generated Lean
certificates remain authoritative independently of these metadata strings.
-/

namespace LeanUfo.UFO.DSL

def artifactName : String :=
  "Lean UFO Formalization"

def artifactVersion : String :=
  "0.0.0-dev"

def checkerName : String :=
  "LeanUfo.UFO.DSL.Checker.checkAxioms4"

def checkerVersion : String :=
  artifactVersion

def axiomPackageName : String :=
  "UFOAxioms4"

end LeanUfo.UFO.DSL
