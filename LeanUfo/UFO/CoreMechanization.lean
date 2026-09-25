-- The final section imports the cumulative signatures and axiom packages.
import LeanUfo.UFO.Core.Section4
-- These results isolate consequences of the selected S5 semantics.
import LeanUfo.UFO.Core.S5_Derived

-- The sparse witnesses establish joint satisfiability for each cumulative section.
import LeanUfo.UFO.FormalAnalysis.Satisfiability.Consistency
-- The relator witnesses exercise the repaired relator axioms with nonempty relators.
import LeanUfo.UFO.FormalAnalysis.Satisfiability.Relator.Model3_10

-- These modules record assumption dependencies, countermodels and anti-vacuity checks.
import LeanUfo.UFO.FormalAnalysis.StructuralAssumptions
import LeanUfo.UFO.FormalAnalysis.Historical.GuardedOverlapCountermodel
import LeanUfo.UFO.FormalAnalysis.AntiVacuity.AntiVacuity

/-!
# Lean UFO Core mechanization

This module is the public import for the paper artifact. It collects the modal
semantics, the cumulative UFO axiom packages, their derived theorems, the
concrete satisfiability witnesses and the analyses discussed in the paper.
-/
