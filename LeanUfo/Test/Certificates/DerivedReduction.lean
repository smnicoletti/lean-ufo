import LeanUfo.UFO.DSL.ConcreteExamples.FlowerPropertyChange
import LeanUfo.UFO.DSL.ConcreteExamples.RedirectedWalk
import LeanUfo.UFO.DSL.ConcreteExamples.WoodenTable
import Lean.Util.CollectAxioms

/-!
# Finite derived-assertion reduction

The two-world walk example exercises quantified partition assertions on a
compiled cached model. All three public examples must certify at their existing
limits. The partition proof must use only standard Lean axioms, even though
the separate registered-axiom certificates use native checks.

Auditing the walk's partition keeps this test sensitive to finite quantified
reduction. The flower example separately exercises quality-space certification.
-/

run_cmd do
  let axioms ← Lean.collectAxioms ``RedirectedWalkExample.assertedDerivedFacts
  for axiomName in axioms do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "derived-assertion reduction uses unexpected axiom {axiomName}"

-- Coordinates follow the declaration order in the public examples. These
-- checks prevent a certifiable but less faithful model from losing the
-- quality-value change, the walk's bearer, or the wood's continued existence.
namespace FlowerChangeRegression
private def summer : Fin FlowerPropertyChangeExample.data.worldCount := ⟨0, by decide⟩
private def autumn : Fin FlowerPropertyChangeExample.data.worldCount := ⟨1, by decide⟩
private def rose : Fin FlowerPropertyChangeExample.data.thingCount := ⟨2, by decide⟩
private def color : Fin FlowerPropertyChangeExample.data.thingCount := ⟨3, by decide⟩
private def red : Fin FlowerPropertyChangeExample.data.thingCount := ⟨5, by decide⟩
private def brown : Fin FlowerPropertyChangeExample.data.thingCount := ⟨6, by decide⟩
example : FlowerPropertyChangeExample.data.hasValue color red summer = true ∧
    FlowerPropertyChangeExample.data.hasValue color red autumn = false ∧
    FlowerPropertyChangeExample.data.hasValue color brown autumn = true ∧
    FlowerPropertyChangeExample.data.inheresIn color rose summer = true ∧
    FlowerPropertyChangeExample.data.inheresIn color rose autumn = true := by native_decide
end FlowerChangeRegression

namespace WalkChangeRegression
private def beforeTurn : Fin RedirectedWalkExample.data.worldCount := ⟨0, by decide⟩
private def afterTurn : Fin RedirectedWalkExample.data.worldCount := ⟨1, by decide⟩
private def ongoing : Fin RedirectedWalkExample.data.thingCount := ⟨2, by decide⟩
private def redirected : Fin RedirectedWalkExample.data.thingCount := ⟨3, by decide⟩
private def paul : Fin RedirectedWalkExample.data.thingCount := ⟨4, by decide⟩
private def walk : Fin RedirectedWalkExample.data.thingCount := ⟨5, by decide⟩
example : RedirectedWalkExample.data.inst walk ongoing beforeTurn = true ∧
    RedirectedWalkExample.data.inst walk ongoing afterTurn = false ∧
    RedirectedWalkExample.data.inst walk redirected afterTurn = true ∧
    RedirectedWalkExample.data.inheresIn walk paul beforeTurn = true ∧
    RedirectedWalkExample.data.inheresIn walk paul afterTurn = true := by native_decide
end WalkChangeRegression

namespace WoodSurvivalRegression
private def rawWood : Fin WoodenTableExample.data.worldCount := ⟨0, by decide⟩
private def assembled : Fin WoodenTableExample.data.worldCount := ⟨1, by decide⟩
private def demolished : Fin WoodenTableExample.data.worldCount := ⟨2, by decide⟩
private def wood : Fin WoodenTableExample.data.thingCount := ⟨2, by decide⟩
private def component : Fin WoodenTableExample.data.thingCount := ⟨3, by decide⟩
example : WoodenTableExample.data.ex wood rawWood = true ∧
    WoodenTableExample.data.ex wood assembled = true ∧
    WoodenTableExample.data.ex wood demolished = true ∧
    WoodenTableExample.data.ex component rawWood = false ∧
    WoodenTableExample.data.ex component assembled = true ∧
    WoodenTableExample.data.ex component demolished = false ∧
    WoodenTableExample.data.constitutedBy component wood assembled = true := by native_decide
end WoodSurvivalRegression
