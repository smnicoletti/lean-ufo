import LeanUfo.UFO.DSL.Complexity.Metrics

/-!
# Counted compiler stages

The source compiler exported here is the production counted computation from
`DSL.Compiler`. Ordinary compilation is its `value` projection. Duplicate
names, unresolved references, arity failures, and projection conflicts stop
later stages and their charges. This connects the measured computation to its
returned result, following Forster et al.'s concrete-machine discipline
(ITP 2021). Name-map, edge-query, and derived-string operations retain the
interfaces stated in `docs/dsl/complexity.md`.

The proof layout takes practical inspiration from de Moura's RadixExperiment:
each executable compiler pass has a preservation proof. Their source-to-model
composition remains a separate obligation. RadixExperiment supplies an
engineering precedent, not an asymptotic theorem about this DSL.
-/

namespace LeanUfo.UFO.DSL.Complexity

/--
The multivariate compiler polynomial obtained by adding the charged production
stages.  Its terms respectively cover name indexing, fact and product-family
resolution, scope expansion, taxonomy materialization, reflexive
specialization, projection validation, explicit fact insertion, deterministic
dense-table initialization, and Warshall closure construction. The final eight
units cover four stage-result tests and two final tests in each name index.

`compilerOperationalCost_le` proves this bound using the cost of each stage
and the correspondence between its intermediate arrays and `SourceMetrics`.
-/
def sourceCompilerPolynomial (m : SourceMetrics) : Nat :=
  6 * m.worlds + 6 * m.things + 24 * m.facts +
    m.productFamilies * (6 * m.productFamilySlots + 14) +
    m.resolvedCompilerCostBound + 8

/-- Increasing any size used by the compiler bound cannot lower that bound.
This concerns the upper bound, not the observed count: additional facts can
make a short-circuiting computation stop earlier. The other source metrics
only enlarge the scalar input size and do not occur in this formula. -/
theorem sourceCompilerPolynomial_mono {small large : SourceMetrics}
    (hWorlds : small.worlds ≤ large.worlds)
    (hThings : small.things ≤ large.things)
    (hFacts : small.facts ≤ large.facts)
    (hExpanded : small.expandedFacts ≤ large.expandedFacts)
    (hTaxonomy : small.taxonomyFacts ≤ large.taxonomyFacts)
    (hSpecialization : small.specializationFactsUpper ≤ large.specializationFactsUpper)
    (hFamilies : small.productFamilies ≤ large.productFamilies)
    (hSlots : small.productFamilySlots ≤ large.productFamilySlots)
    (hRelations : small.relationCells ≤ large.relationCells)
    (hProjections : small.projectionCells ≤ large.projectionCells) :
    sourceCompilerPolynomial small ≤ sourceCompilerPolynomial large := by
  unfold sourceCompilerPolynomial SourceMetrics.resolvedCompilerCostBound
  repeat' first
    | assumption
    | exact Nat.le_refl _
    | apply Nat.add_le_add
    | apply Nat.mul_le_mul

/-- Scalar corollary for the complete source-compiler formula. Every factor is
an explicit component of `inputSize`; Warshall construction contributes the
quartic term when both world and thing counts grow. -/
theorem sourceCompilerPolynomial_le_inputSize_pow4 (m : SourceMetrics) :
    sourceCompilerPolynomial m ≤ 463 * m.inputSize ^ 4 := by
  let n := m.inputSize
  have hn : 1 ≤ n := by
    simp only [n, SourceMetrics.inputSize]
    omega
  have hworlds : m.worlds ≤ n := by
    simp only [n, SourceMetrics.inputSize]
    omega
  have hthings : m.things ≤ n := by
    simp only [n, SourceMetrics.inputSize]
    omega
  have hfacts : m.facts ≤ n := by
    simp only [n, SourceMetrics.inputSize]
    omega
  have hfamilies : m.productFamilies ≤ n := by
    simp only [n, SourceMetrics.inputSize]
    omega
  have hslots : m.productFamilySlots ≤ n := by
    simp only [n, SourceMetrics.inputSize]
    omega
  have hn2 : n ≤ n ^ 2 := by
    calc
      n = n * 1 := by omega
      _ ≤ n * n := Nat.mul_le_mul_left n hn
      _ = n ^ 2 := by simp [Nat.pow_succ]
  have hn3 : n ^ 2 ≤ n ^ 3 := by
    calc
      n ^ 2 = n ^ 2 * 1 := by omega
      _ ≤ n ^ 2 * n := Nat.mul_le_mul_left (n ^ 2) hn
      _ = n ^ 3 := by simp [Nat.pow_succ, Nat.mul_comm]
  have hn4 : n ^ 3 ≤ n ^ 4 := by
    calc
      n ^ 3 = n ^ 3 * 1 := by omega
      _ ≤ n ^ 3 * n := Nat.mul_le_mul_left (n ^ 3) hn
      _ = n ^ 4 := by simp [Nat.pow_succ, Nat.mul_comm]
  have hnPow4 : n ≤ n ^ 4 := hn2.trans (hn3.trans hn4)
  have hn2Pow4 : n ^ 2 ≤ n ^ 4 := hn3.trans hn4
  have hFamilyProduct :
      m.productFamilies * (6 * m.productFamilySlots + 14) ≤
        6 * n ^ 2 + 14 * n := by
    calc
      m.productFamilies * (6 * m.productFamilySlots + 14) ≤
          n * (6 * n + 14) := by
        exact Nat.mul_le_mul hfamilies
          (Nat.add_le_add (Nat.mul_le_mul_left 6 hslots) (le_refl 14))
      _ = 6 * n ^ 2 + 14 * n := by
        simp [Nat.mul_add, Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm]
  have hResolved := m.resolvedCompilerCostBound_le_inputSize_pow4
  unfold sourceCompilerPolynomial
  dsimp only [n] at *
  omega

/-- Public counted source compiler. -/
def compileSourceCosted (source : ModelSource) :
    Costed (Except ResolveError CompiledModelSource) :=
  compileModelSourceCosted source

/-- Public ordinary compiler obtained only by erasing operational cost. -/
def compileSource (source : ModelSource) : Except ResolveError CompiledModelSource :=
  (compileSourceCosted source).value

@[simp] theorem compileSourceCosted_value (source : ModelSource) :
    (compileSourceCosted source).value = compileSource source := rfl

theorem compileSource_eq_production (source : ModelSource) :
    compileSource source = compileModelSource source := rfl

/-- The observed cost is the counter accumulated by production execution. -/
def compilerOperationalCost (source : ModelSource) : Nat :=
  (compileSourceCosted source).cost

@[simp] theorem compilerOperationalCost_eq (source : ModelSource) :
    compilerOperationalCost source = (compileModelSourceCosted source).cost := rfl

/-- World indexing costs at most six units per name plus two result tests. -/
theorem worldNameIndexCost_le (source : ModelSource) :
    (buildWorldNameIndexCosted source).cost ≤
      6 * (sourceMetrics source).worlds + 2 := by
  have bound := buildNameIndexCosted_cost_le source.worlds
  simp only [buildWorldNameIndexCosted, Costed.charge_cost, Costed.map_cost,
    sourceMetrics]
  omega

/-- Thing indexing costs at most six units per name plus two result tests. -/
theorem thingNameIndexCost_le (source : ModelSource) :
    (buildThingNameIndexCosted source).cost ≤
      6 * (sourceMetrics source).things + 2 := by
  have bound := buildNameIndexCosted_cost_le source.things
  simp only [buildThingNameIndexCosted, Costed.charge_cost, Costed.map_cost,
    sourceMetrics]
  omega

/-- Indexed fact resolution charges at most 24 operations per source fact. -/
theorem factResolutionCost_le (source : ModelSource)
    (worlds things : NameIndex) :
    (resolveSourceFactsCosted source worlds things).cost ≤
      24 * (sourceMetrics source).facts := by
  simpa [resolveSourceFactsCosted, sourceMetrics] using
    resolveNamedFactsIndexedCosted_cost_le worlds things source.facts

/-- Product-family resolution exposes both registry and witness-slot inputs. -/
theorem productFamilyResolutionCost_le (source : ModelSource)
    (things : NameIndex) :
    (resolveSourceProductFamiliesCosted source things).cost ≤
      (sourceMetrics source).productFamilies *
        (6 * (sourceMetrics source).productFamilySlots + 14) :=
  productFamilyResolutionCost_le_sourceMetrics source things

/-- Total operational compiler bound, including all short-circuiting errors. -/
theorem compilerOperationalCost_le (source : ModelSource) :
    compilerOperationalCost source ≤
      sourceCompilerPolynomial (sourceMetrics source) := by
  cases hWorld : (buildWorldNameIndexCosted source).value with
  | error worldError =>
      simp [compilerOperationalCost, compileSourceCosted,
        compileModelSourceCosted, exceptBindCosted, hWorld]
      have worldCost := worldNameIndexCost_le source
      unfold sourceCompilerPolynomial
      omega
  | ok worldIndex =>
      cases hThing : (buildThingNameIndexCosted source).value with
      | error thingError =>
          simp [compilerOperationalCost, compileSourceCosted,
            compileModelSourceCosted, exceptBindCosted, hWorld, hThing]
          have worldCost := worldNameIndexCost_le source
          have thingCost := thingNameIndexCost_le source
          unfold sourceCompilerPolynomial
          omega
      | ok thingIndex =>
          cases hFacts : (resolveSourceFactsCosted
            source worldIndex thingIndex).value with
          | error factError =>
              simp [compilerOperationalCost, compileSourceCosted,
                compileModelSourceCosted, exceptBindCosted,
                hWorld, hThing, hFacts]
              have worldCost := worldNameIndexCost_le source
              have thingCost := thingNameIndexCost_le source
              have factCost := factResolutionCost_le source worldIndex thingIndex
              unfold sourceCompilerPolynomial
              omega
          | ok resolved =>
              cases hFamilies : (resolveSourceProductFamiliesCosted
                source thingIndex).value with
              | error familyError =>
                  simp [compilerOperationalCost, compileSourceCosted,
                    compileModelSourceCosted, exceptBindCosted,
                    hWorld, hThing, hFacts, hFamilies]
                  have worldCost := worldNameIndexCost_le source
                  have thingCost := thingNameIndexCost_le source
                  have factCost := factResolutionCost_le
                    source worldIndex thingIndex
                  have familyCost := productFamilyResolutionCost_le
                    source thingIndex
                  unfold sourceCompilerPolynomial
                  omega
              | ok productFamilies =>
                  simp [compilerOperationalCost, compileSourceCosted,
                    compileModelSourceCosted, exceptBindCosted,
                    hWorld, hThing, hFacts, hFamilies]
                  have worldCost := worldNameIndexCost_le source
                  have thingCost := thingNameIndexCost_le source
                  have factCost := factResolutionCost_le
                    source worldIndex thingIndex
                  have familyCost := productFamilyResolutionCost_le
                    source thingIndex
                  have resolvedCost :=
                    compileResolvedSourceCosted_cost_le_sourceMetrics
                      source worldIndex thingIndex resolved productFamilies
                      hFacts hFamilies
                  unfold sourceCompilerPolynomial
                  omega

/-- One-variable polynomial corollary for production source compilation. -/
theorem compilerOperationalCost_le_inputSize_pow4 (source : ModelSource) :
    compilerOperationalCost source ≤
      463 * (sourceMetrics source).inputSize ^ 4 :=
  (compilerOperationalCost_le source).trans
    (sourceCompilerPolynomial_le_inputSize_pow4 (sourceMetrics source))

end LeanUfo.UFO.DSL.Complexity
