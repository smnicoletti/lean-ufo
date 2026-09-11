import LeanUfo.UFO.DSL.Complexity.Compiler
import LeanUfo.UFO.DSL.Diagnostic.DerivedAssertions

/-!
# Source-size bounds for derived-assertion diagnostics

Successful compilation bounds the stored proposition array used by diagnostic
queries. The precheck therefore costs at most `5570 N^5`, where `N` is the
explicit source input size. Selecting its saved report adds at most four
operations. The count includes fact/world selection, predicate queries, full
report construction, and copying the retained rows.

These are bounds on the existing diagnostic components, with the actual
compiler result as input. The final component sum also charges source
compilation and both frontend name arrays, giving `6091 N^5`. Lean proof
elaboration and the remaining frontend schedule are not covered. Composing
counters at those call boundaries follows the cost-aware semantics described
in `CostModel.lean`.
-/

namespace LeanUfo.UFO.DSL.Complexity

open private namedDerivedPredicateCostBound
  from LeanUfo.UFO.DSL.Diagnostic.DerivedAssertions
open private derivedLookupCostBound
  from LeanUfo.UFO.DSL.Diagnostic.AxiomAnalysis

-- All monomials in the predicate and report bounds have degree at most three.
-- Their coefficients sum to 1648 and 2103 respectively. Stored propositions
-- count separately from worlds and things until each is bounded by N.
private theorem derivedComponentBounds_le_cube (W T n : Nat) (tables : FactTables)
    (positive : 0 < n) (worlds : W ≤ n) (things : T ≤ n)
    (stored : tables.derivedProps.size ≤ n) :
    namedDerivedPredicateCostBound W T tables ≤ 1648 * n ^ 3 ∧
      derivedAssertionReportCostBound W T tables ≤ 2103 * n ^ 3 := by
  have linear : n ≤ n ^ 3 := by
    simpa using Nat.pow_le_pow_right positive (show 1 ≤ 3 by omega)
  have square : n ^ 2 ≤ n ^ 3 := Nat.pow_le_pow_right positive (by omega)
  have one : 1 ≤ n ^ 3 := by omega
  have w := worlds.trans linear
  have t := things.trans linear
  have d := stored.trans linear
  have tt := (Nat.pow_le_pow_left things 2).trans square
  have wt : W * T ≤ n ^ 3 := by
    have pair : W * T ≤ n ^ 2 := by
      simpa only [Nat.pow_two] using Nat.mul_le_mul worlds things
    exact pair.trans square
  have td : T * tables.derivedProps.size ≤ n ^ 3 := by
    have pair : T * tables.derivedProps.size ≤ n ^ 2 := by
      simpa only [Nat.pow_two] using Nat.mul_le_mul things stored
    exact pair.trans square
  have wtt : W * T ^ 2 ≤ n ^ 3 := by
    simpa [Nat.pow_succ, Nat.mul_comm] using
      Nat.mul_le_mul worlds (Nat.pow_le_pow_left things 2)
  constructor
  · dsimp [namedDerivedPredicateCostBound, derivedLookupCostBound]
    ring_nf at wt wtt tt ⊢
    omega
  · rw [derivedAssertionReportCostBound_eq]
    ring_nf at wt wtt tt td ⊢
    omega

private theorem derivedFailureBound_le_fifth (W T F E n : Nat) (tables : FactTables)
    (positive : 0 < n) (worlds : W ≤ n) (things : T ≤ n) (facts : F ≤ n)
    (stored : tables.derivedProps.size ≤ n) (rows : E ≤ 9) :
    derivedAssertionFailureCostBound W T F E tables ≤ 5570 * n ^ 5 := by
  obtain ⟨predicate, report⟩ := derivedComponentBounds_le_cube W T n tables
    positive worlds things stored
  have linear : n ≤ n ^ 3 := by
    simpa using Nat.pow_le_pow_right positive (show 1 ≤ 3 by omega)
  have t := things.trans linear
  have extra : namedDerivedPredicateCostBound W T tables + 36 * T + 24 ≤
      1708 * n ^ 3 := by omega
  have visits := Nat.mul_le_mul (show W + 1 ≤ 2 * n by omega) extra
  have visitsBound : (W + 1) *
      (namedDerivedPredicateCostBound W T tables + 36 * T + 24) ≤ 3416 * n ^ 4 := by
    convert visits using 1
    ring
  have oneFourth : 1 ≤ n ^ 4 := by
    have := Nat.pow_le_pow_right positive (show 0 ≤ 4 by omega)
    simpa using this
  have perFact : 10 + (W + 1) *
      (namedDerivedPredicateCostBound W T tables + 36 * T + 24) ≤ 3426 * n ^ 4 := by
    omega
  have selection := Nat.mul_le_mul facts perFact
  have selectionBound : F * (10 + (W + 1) *
      (namedDerivedPredicateCostBound W T tables + 36 * T + 24)) ≤ 3426 * n ^ 5 := by
    convert selection using 1
    ring
  have cube : n ^ 3 ≤ n ^ 5 := Nat.pow_le_pow_right positive (by omega)
  have reportBound := report.trans (Nat.mul_le_mul_left 2103 cube)
  have oneFifth : 1 ≤ n ^ 5 := by omega
  unfold derivedAssertionFailureCostBound
  omega

/-- The production precheck on the actual compiler output has a source-only
bound. Empty domains are allowed here, because assertion diagnostics accept
them even though successful finite-model certification requires nonempty ones.
The name-array expressions describe the supplied arguments, not their cost. -/
theorem source_derivedAssertionFailure_cost_bound
    (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled) :
    (derivedAssertionFailureCosted (source.worlds.map Lean.Name.mkSimple)
      (source.things.map Lean.Name.mkSimple) source.facts compiled.scopedFacts compiled.tables).cost ≤
      5570 * (sourceMetrics source).inputSize ^ 5 := by
  have bound := derivedAssertionFailureCosted_cost_le
    (source.worlds.map Lean.Name.mkSimple) (source.things.map Lean.Name.mkSimple)
    source.facts compiled.scopedFacts compiled.tables
  have rows := derivedAssertionFailureBudgetedCosted_size_le 9
    (source.worlds.map Lean.Name.mkSimple) (source.things.map Lean.Name.mkSimple)
    source.facts compiled.scopedFacts compiled.tables
  simp only [Array.size_map] at bound
  apply bound.trans
  apply derivedFailureBound_le_fifth
  · exact sourceMetrics_inputSize_pos source
  · simp only [SourceMetrics.inputSize, sourceMetrics]; omega
  · simp only [SourceMetrics.inputSize, sourceMetrics]; omega
  · simp only [SourceMetrics.inputSize, sourceMetrics]; omega
  · have stored := compiledDerivedPropCount_le_sourceMetrics source compiled success
    unfold SourceMetrics.inputSize
    omega
  · exact rows

/-- If semantic proof elaboration fails, the frontend selects the saved
precheck report. One scan and that selection cost at most `5574 N^5`.
Successful elaboration skips selection. Its own proof work is excluded. -/
theorem source_derivedAssertionAnalysis_cost_bound
    (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled) :
    (derivedAssertionAnalysisCosted (source.worlds.map Lean.Name.mkSimple)
      (source.things.map Lean.Name.mkSimple) source.facts compiled.scopedFacts compiled.tables).cost ≤
      5574 * (sourceMetrics source).inputSize ^ 5 := by
  have bound := source_derivedAssertionFailure_cost_bound source compiled success
  have selection := derivedAssertionAnalysisCosted_cost_le
    (source.worlds.map Lean.Name.mkSimple) (source.things.map Lean.Name.mkSimple)
    source.facts compiled.scopedFacts compiled.tables
  have positive := sourceMetrics_inputSize_pos source
  have one : 1 ≤ (sourceMetrics source).inputSize ^ 5 := by
    have := Nat.pow_le_pow_right positive (show 0 ≤ 5 by omega)
    simpa using this
  omega

/-- Both frontend name arrays have an exact linear construction cost. Their
combined length is already included in the source input size. The fixed two
operations initialize the world and thing arrays even when either is empty. -/
theorem sourceNameConversion_cost_bound (source : ModelSource) :
    (namesFromStringsCosted source.worlds).cost +
      (namesFromStringsCosted source.things).cost ≤ 6 * (sourceMetrics source).inputSize := by
  rw [namesFromStringsCosted_cost, namesFromStringsCosted_cost]
  simp only [SourceMetrics.inputSize, sourceMetrics]
  omega

/-- Bound the source compiler, both name conversions, and one derived-assertion
scan followed by saved-report selection. All diagnostic inputs come from this
compiler result. Names and propositions are not independently sized inputs.

The frontend can separate these pure calls with declaration elaboration. This
sum does not include generated declarations, axiom checks, widgets, or other
diagnostic branches. It is a component bound, not a full command bound. -/
theorem source_derivedAssertion_component_bound
    (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled) :
    compilerOperationalCost source +
      (namesFromStringsCosted source.worlds).cost +
      (namesFromStringsCosted source.things).cost +
      (derivedAssertionAnalysisCosted (namesFromStrings source.worlds)
        (namesFromStrings source.things) source.facts compiled.scopedFacts compiled.tables).cost ≤
      6091 * (sourceMetrics source).inputSize ^ 5 := by
  have compiler := compilerOperationalCost_le_inputSize_pow4 source
  have names := sourceNameConversion_cost_bound source
  have diagnostics := source_derivedAssertionAnalysis_cost_bound source compiled success
  have positive := sourceMetrics_inputSize_pos source
  have linear : (sourceMetrics source).inputSize ≤ (sourceMetrics source).inputSize ^ 5 := by
    simpa using Nat.pow_le_pow_right positive (show 1 ≤ 5 by omega)
  have fourth : (sourceMetrics source).inputSize ^ 4 ≤ (sourceMetrics source).inputSize ^ 5 :=
    Nat.pow_le_pow_right positive (by omega)
  have compilerBound := compiler.trans (Nat.mul_le_mul_left 511 fourth)
  have nameBound := names.trans (Nat.mul_le_mul_left 6 linear)
  simp only [namesFromStrings, namesFromStringsCosted_value]
  omega

end LeanUfo.UFO.DSL.Complexity
