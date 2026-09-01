import LeanUfo.UFO.DSL.Complexity.Metrics

/-!
# Counted compiler stages

The source compiler exported here is the production counted computation from
`DSL.Compiler`; ordinary compilation is its `value` projection. Costs therefore
short-circuit with duplicate names, unresolved references, arity failures, and
projection conflicts instead of being assigned after an unrelated evaluation.
This guards against the implementation-correspondence gap discussed by Forster
et al. (ITP 2021).

The planned proof layout also takes practical inspiration from de Moura's
RadixExperiment: each executable compiler pass gets its own preservation proof,
and the final pipeline theorem is their composition.  RadixExperiment is used
as engineering precedent, not as authority for an asymptotic claim.
-/

namespace LeanUfo.UFO.DSL.Complexity

/-- Exact charged work for building all per-world inherence matrices. -/
def inherenceClosureBuildCost (worlds things : Nat) : Nat :=
  worlds * (13 * things ^ 3 + 9 * things ^ 2 + 1)

theorem inherenceClosureBuildCost_eq (worlds things : Nat) :
    inherenceClosureBuildCost worlds things =
      worlds * (13 * things ^ 3 + 9 * things ^ 2 + 1) := by
  rfl

/--
The multivariate compiler polynomial obtained by adding the charged production
stages.  Its terms respectively cover name indexing, fact and product-family
resolution, scope expansion, taxonomy materialization, reflexive
specialization, projection validation, explicit fact insertion, deterministic
dense-table initialization, and Warshall closure construction.

This definition is not itself a proof: `compilerOperationalCost_le` is exported
only after each intermediate-size correspondence has been established.  That
separation prevents a named polynomial from becoming another unconnected
envelope.
-/
def sourceCompilerPolynomial (m : SourceMetrics) : Nat :=
  2 * m.worlds + 2 * m.things + 6 * m.facts +
    m.productFamilies * (2 * m.productFamilySlots + 4) +
    m.resolvedCompilerCostBound

/-- Scalar corollary for the complete source-compiler formula. Every factor is
an explicit component of `inputSize`; the quartic degree comes from concrete
Warshall construction rather than an externally assigned envelope. -/
theorem sourceCompilerPolynomial_le_inputSize_pow4 (m : SourceMetrics) :
    sourceCompilerPolynomial m ≤ 80 * m.inputSize ^ 4 := by
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
      m.productFamilies * (2 * m.productFamilySlots + 4) ≤
        2 * n ^ 2 + 4 * n := by
    calc
      m.productFamilies * (2 * m.productFamilySlots + 4) ≤
          n * (2 * n + 4) := by
        exact Nat.mul_le_mul hfamilies
          (Nat.add_le_add (Nat.mul_le_mul_left 2 hslots) (le_refl 4))
      _ = 2 * n ^ 2 + 4 * n := by
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

/-- Duplicate-aware world indexing never exceeds two charged operations/name. -/
theorem worldNameIndexCost_le (source : ModelSource) :
    (buildWorldNameIndexCosted source).cost ≤
      2 * (sourceMetrics source).worlds := by
  simpa [buildWorldNameIndexCosted, sourceMetrics] using
    buildNameIndexCosted_cost_le source.worlds

/-- Duplicate-aware thing indexing never exceeds two charged operations/name. -/
theorem thingNameIndexCost_le (source : ModelSource) :
    (buildThingNameIndexCosted source).cost ≤
      2 * (sourceMetrics source).things := by
  simpa [buildThingNameIndexCosted, sourceMetrics] using
    buildNameIndexCosted_cost_le source.things

/-- Indexed fact resolution charges at most six operations per source fact. -/
theorem factResolutionCost_le (source : ModelSource)
    (worlds things : NameIndex) :
    (resolveSourceFactsCosted source worlds things).cost ≤
      6 * (sourceMetrics source).facts := by
  simpa [resolveSourceFactsCosted, sourceMetrics] using
    resolveNamedFactsIndexedCosted_cost_le worlds things source.facts

/-- Product-family resolution exposes both registry and witness-slot inputs. -/
theorem productFamilyResolutionCost_le (source : ModelSource)
    (things : NameIndex) :
    (resolveSourceProductFamiliesCosted source things).cost ≤
      (sourceMetrics source).productFamilies *
        (2 * (sourceMetrics source).productFamilySlots + 4) :=
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
      80 * (sourceMetrics source).inputSize ^ 4 :=
  (compilerOperationalCost_le source).trans
    (sourceCompilerPolynomial_le_inputSize_pow4 (sourceMetrics source))

end LeanUfo.UFO.DSL.Complexity
