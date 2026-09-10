import LeanUfo.UFO.DSL.Diagnostic.AxiomAnalysis
import LeanUfo.UFO.DSL.Diagnostic.DerivedAssertions

/-!
# Source-level diagnostic entry points

`AxiomAnalysis` explains failed registered axioms. `DerivedAssertions` checks
user-written derived facts and explains their failures before certification.
This aggregate preserves one import for the command elaborator and clients.
-/
