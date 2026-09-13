import LeanUfo.UFO.DSL.ConcreteExamples.FlowerPropertyChange
import Lean.Util.CollectAxioms

/-!
# Finite derived-assertion reduction

The two-world flower example exercises quantified partition assertions on a
compiled cached model. Its import must certify at the example's existing
limits. The assertion proof must use only standard Lean axioms, even though
the separate registered-axiom certificates use native checks.

Reusing the public example keeps this regression test aligned with the model
that exposed excessive simplification of the counted model constructors.
-/

run_cmd do
  let axioms ← Lean.collectAxioms ``FlowerPropertyChangeExample.assertedDerivedFacts
  for axiomName in axioms do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "derived-assertion reduction uses unexpected axiom {axiomName}"
