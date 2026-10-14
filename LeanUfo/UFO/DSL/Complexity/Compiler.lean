import LeanUfo.UFO.DSL.Complexity.Metrics
import LeanUfo.UFO.DSL.Compiler.VerifiedModel

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
each executable compiler pass has a preservation proof. Composition with
checker and diagnostic execution remains open. RadixExperiment supplies an
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
    sourceCompilerPolynomial m ≤ 511 * m.inputSize ^ 4 := by
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
      511 * (sourceMetrics source).inputSize ^ 4 :=
  (compilerOperationalCost_le source).trans
    (sourceCompilerPolynomial_le_inputSize_pow4 (sourceMetrics source))

/-- Model construction has a monotone bound in worlds, family records, and
total witness slots. Exact costs can decrease when validation fails earlier. -/
theorem finiteModelConstruction_bound_mono
    {W W' F F' S S' : Nat} (worlds : W ≤ W') (families : F ≤ F') (slots : S ≤ S') :
    4 + W * (7 * S + 20 * F) + 2 * F ≤
      4 + W' * (7 * S' + 20 * F') + 2 * F' := by
  repeat' first
    | assumption
    | exact Nat.le_refl _
    | apply Nat.add_le_add
    | apply Nat.mul_le_mul

/-- Each source family becomes one finite witness per world. Both witness
arrays retain their lengths, so the checker sees `W * F` family records and
`W * S` slots. Here `F` and `S` count source families and source slots, including
duplicates. The bound permits arbitrary finite witness arity. -/
theorem finiteModelFamilyMetrics_eq_sourceMetrics
    (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled)
    (hw : 0 < source.worlds.size) (ht : 0 < source.things.size) :
    let M := compiled.tables.toFiniteModel4Cached source.worlds.size source.things.size hw ht
      (compileModelSource_ok_lookups_agree source compiled success)
      (compileModelSource_ok_inherenceCacheValid source compiled success)
      (compileModelSource_ok_tableDimensions source compiled success).1
      (compileModelSource_ok_tableDimensions source compiled success).2
    M.productFamilies.size = (sourceMetrics source).worlds * (sourceMetrics source).productFamilies ∧
      checkerProductFamilySlots M =
        (sourceMetrics source).worlds * (sourceMetrics source).productFamilySlots := by
  have readback := compileModelSource_ok_modelFamilies_readback source compiled success hw ht
  obtain ⟨families, slots⟩ := compileModelSource_ok_familySizes source compiled success
  constructor
  · have count := congrArg Array.size readback
    simpa [List.length_flatMap, List.map_map, List.map_const', families,
      sourceMetrics, Nat.mul_comm] using count
  · have weight := congrArg (fun entries : Array (ProductFamilySpec × Nat) =>
        (entries.toList.map (fun entry =>
          entry.1.dimensionThings.size + entry.1.typeThings.size)).sum) readback
    have expanded (items : List ProductFamilySpec) :
        ((items.flatMap (fun family => (List.range source.worlds.size).map
          (fun world => (family, world)))).map (fun entry =>
            entry.1.dimensionThings.size + entry.1.typeThings.size)).sum =
          source.worlds.size * (items.map (fun family =>
            family.dimensionThings.size + family.typeThings.size)).sum := by
      induction items with
      | nil => simp
      | cons family items ih =>
        simp only [List.flatMap_cons, List.map_append, List.sum_append, ih]
        simp [List.map_map, Function.comp_def, List.map_const', Nat.mul_add]
    simp only [Array.toList_map, List.map_map, ProductFamilyWitness.toSpec,
      Array.size_map, Function.comp_def] at weight
    rw [expanded, slots] at weight
    simpa only [checkerProductFamilySlots, sourceMetrics] using weight

open private exceptBindCosted_ok_iff from LeanUfo.UFO.DSL.Compiler.VerifiedModel

private theorem explicitCompilation_cost_le_resolved
    (source : ModelSource) (facts : Array ScopedCompiledFact) (families : Array ProductFamilySpec)
    (compiled : CompiledModelSource)
    (success : (compileResolvedSourceCosted source facts families).value = .ok compiled) :
    (compileExplicitModelASTCosted compiled.ast).cost ≤
      (compileResolvedSourceCosted source facts families).cost := by
  unfold compileResolvedSourceCosted at success
  rw [exceptBindCosted_ok_iff] at success
  obtain ⟨expanded, expandedOk, success⟩ := success
  rw [exceptBindCosted_ok_iff] at success
  obtain ⟨validated, validatedOk, success⟩ := success
  simp only [Costed.map_value, Except.ok.injEq] at success
  rw [← success]
  simp only [compileResolvedSourceCosted, exceptBindCosted, expandedOk, validatedOk, Costed.map_cost]
  omega

/-- Rebuilding the returned AST's tables repeats a stage already reached by
successful source compilation. Its actual counted cost is at most that run's
total cost. This bounds each later reconstruction without charging name
resolution as executed work in that reconstruction. -/
theorem explicitCompilation_cost_le_source
    (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled) :
    (compileExplicitModelASTCosted compiled.ast).cost ≤ compilerOperationalCost source := by
  unfold compileModelSource compileModelSourceCosted at success
  rw [exceptBindCosted_ok_iff] at success
  obtain ⟨worlds, worldsOk, success⟩ := success
  rw [exceptBindCosted_ok_iff] at success
  obtain ⟨things, thingsOk, success⟩ := success
  rw [exceptBindCosted_ok_iff] at success
  obtain ⟨facts, factsOk, success⟩ := success
  rw [exceptBindCosted_ok_iff] at success
  obtain ⟨families, familiesOk, success⟩ := success
  have tailCost := explicitCompilation_cost_le_resolved source facts families compiled success
  simp only [compilerOperationalCost, compileSourceCosted, compileModelSourceCosted,
    exceptBindCosted, worldsOk, thingsOk, factsOk, familiesOk]
  omega

/-- Each reconstruction of the generated tables costs at most `511N⁴` for
the source's complete input size `N`. Repeated calls need repeated charges;
this per-call bound does not assert that the frontend constructs tables once. -/
theorem explicitCompilation_source_scalar_bound
    (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled) :
    (compileExplicitModelASTCosted compiled.ast).cost ≤ 511 * (sourceMetrics source).inputSize ^ 4 :=
  (explicitCompilation_cost_le_source source compiled success).trans
    (compilerOperationalCost_le_inputSize_pow4 source)

/-- The actual returned AST contains no more facts than the scope, taxonomy,
and reflexive-specialization metric permits. Success links the resolver used
in the size proof to the resolver that supplied this compiler result. -/
theorem compiledFactCount_le_sourceMetrics
    (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled) :
    compiled.ast.facts.size ≤ (sourceMetrics source).specializationFactsUpper := by
  unfold compileModelSource compileModelSourceCosted at success
  rw [exceptBindCosted_ok_iff] at success
  obtain ⟨worlds, _, success⟩ := success
  rw [exceptBindCosted_ok_iff] at success
  obtain ⟨things, _, success⟩ := success
  rw [exceptBindCosted_ok_iff] at success
  obtain ⟨resolved, resolvedOk, success⟩ := success
  rw [exceptBindCosted_ok_iff] at success
  obtain ⟨families, _, success⟩ := success
  rw [compileResolvedSourceCosted_ok_result source resolved families compiled success]
  exact resolved_specialization_size_le_sourceMetrics source worlds things resolved resolvedOk

/-- Every ordered metadata row array in the returned compiler tables is
bounded by the source's materialized-fact metric. This connects reuse scans
to the actual source compilation, including taxonomy and world expansion. -/
theorem compiledRowSizes_le_sourceMetrics
    (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled) :
    compiled.tables.RowSizesBoundedBy (sourceMetrics source).specializationFactsUpper := by
  have invariant := compileModelSource_ok_constructionInvariant source compiled success
  rw [invariant.tables]
  rcases compileExplicitModelAST_rowSizes compiled.ast with ⟨hu, hb, ht, hp⟩
  have hf := compiledFactCount_le_sourceMetrics source compiled success
  exact ⟨fun f => (hu f).trans hf, fun f => (hb f).trans hf,
    fun f => (ht f).trans hf, hp.trans hf⟩

/-- Diagnostics scan the stored derived propositions. Their number is bounded
by the source metric for materialized facts, including repeated assertions and
world expansion. No finite-model or registry size is supplied independently. -/
theorem compiledDerivedPropCount_le_sourceMetrics
    (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled) :
    compiled.tables.derivedProps.size ≤ (sourceMetrics source).specializationFactsUpper := by
  have invariant := compileModelSource_ok_constructionInvariant source compiled success
  rw [invariant.tables]
  exact (compileExplicitModelAST_derivedProps_size_le compiled.ast).trans
    (compiledFactCount_le_sourceMetrics source compiled success)

/-- A source-produced cache contains exactly W world slots and W·T² cells.
The sized Warshall matrices establish this storage bound without inspecting
their Boolean contents or assuming that every possible edge is present. -/
theorem finiteModelCacheSize_eq_sourceMetrics
    (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled)
    (hw : 0 < source.worlds.size) (ht : 0 < source.things.size) :
    let M := compiled.tables.toFiniteModel4Cached source.worlds.size source.things.size hw ht
      (compileModelSource_ok_lookups_agree source compiled success)
      (compileModelSource_ok_inherenceCacheValid source compiled success)
      (compileModelSource_ok_tableDimensions source compiled success).1
      (compileModelSource_ok_tableDimensions source compiled success).2
    checkerCacheSize M = (sourceMetrics source).worlds +
      (sourceMetrics source).worlds * (sourceMetrics source).things ^ 2 := by
  change compiled.tables.inherenceClosures.size +
    (compiled.tables.inherenceClosures.toList.map Array.size).sum = _
  rw [(compileModelSource_ok_inherenceCacheValid source compiled success).1]
  obtain ⟨worlds, things⟩ := compileModelSource_ok_tableDimensions source compiled success
  simp [List.map_map, Function.comp_def, List.map_const', worlds, things, sourceMetrics, Nat.pow_two]

/-- The scalar size of the cached production model is at most three times
the square of the source size. Family replication contributes at most N².
The base model and cache storage each contribute at most N, hence at most N².
The source-workflow theorem substitutes this size into the checker bounds. -/
theorem finiteModelInputSize_le_sourceInputSize_sq
    (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled)
    (hw : 0 < source.worlds.size) (ht : 0 < source.things.size) :
    checkerInputSize (compiled.tables.toFiniteModel4Cached
      source.worlds.size source.things.size hw ht
      (compileModelSource_ok_lookups_agree source compiled success)
      (compileModelSource_ok_inherenceCacheValid source compiled success)
      (compileModelSource_ok_tableDimensions source compiled success).1
      (compileModelSource_ok_tableDimensions source compiled success).2) ≤
      3 * (sourceMetrics source).inputSize ^ 2 := by
  let M := compiled.tables.toFiniteModel4Cached source.worlds.size source.things.size hw ht
    (compileModelSource_ok_lookups_agree source compiled success)
    (compileModelSource_ok_inherenceCacheValid source compiled success)
    (compileModelSource_ok_tableDimensions source compiled success).1
    (compileModelSource_ok_tableDimensions source compiled success).2
  have worlds : M.worldCount = (sourceMetrics source).worlds := rfl
  have things : M.thingCount = (sourceMetrics source).things := rfl
  have cells : checkerRelationCells M = (sourceMetrics source).relationCells := rfl
  obtain ⟨families, slots⟩ := finiteModelFamilyMetrics_eq_sourceMetrics source compiled success hw ht
  have cache := finiteModelCacheSize_eq_sourceMetrics source compiled success hw ht
  change checkerInputSize M ≤ _
  change M.productFamilies.size = _ at families
  change checkerProductFamilySlots M = _ at slots
  change checkerCacheSize M = _ at cache
  rw [checkerInputSize, families, slots, cells, worlds, things, cache]
  let m := sourceMetrics source
  have worldBound : m.worlds ≤ m.inputSize := by unfold SourceMetrics.inputSize; omega
  have slotBound : m.productFamilies + m.productFamilySlots ≤ m.inputSize := by
    unfold SourceMetrics.inputSize; omega
  have baseBound : m.worlds + m.things + m.relationCells + 1 ≤ m.inputSize := by
    unfold SourceMetrics.inputSize; omega
  have positive : 1 ≤ m.inputSize := by unfold SourceMetrics.inputSize; omega
  have cacheCells : m.worlds * m.things ^ 2 ≤ m.relationCells := by
    -- One dense binary field already has a cell for every cached pair/world.
    -- The source metric includes all such fields, so it bounds the cache cells.
    have coefficient : 1 ≤ BinaryField.count := by decide
    have h := Nat.mul_le_mul_right m.worlds
      (Nat.mul_le_mul_right (m.things ^ 2) coefficient)
    simp only [Nat.one_mul] at h
    rw [Nat.mul_comm m.worlds]
    change _ ≤ UnaryField.count * m.things * m.worlds +
      BinaryField.count * m.things ^ 2 * m.worlds +
      TernaryField.count * m.things ^ 3 * m.worlds
    omega
  have cacheBound : m.worlds + m.worlds * m.things ^ 2 ≤ m.inputSize := by
    unfold SourceMetrics.inputSize
    omega
  have productBound := Nat.mul_le_mul worldBound slotBound
  have linearBound := Nat.mul_le_mul_left m.inputSize positive
  simp only [Nat.mul_add, ← Nat.pow_two] at productBound
  simp only [Nat.mul_one, ← Nat.pow_two] at linearBound
  change m.worlds + m.things + m.relationCells + m.worlds * m.productFamilies +
    m.worlds * m.productFamilySlots + (m.worlds + m.worlds * m.things ^ 2) + 1 ≤
      3 * m.inputSize ^ 2
  omega

/-- Construction of the cached production model is bounded by source
metrics alone. Successful name resolution preserves family and slot counts,
and the compiler stores that exact registry in the tables. This charges the
constructor only. Source compilation and later relation queries are separate
calls whose costs must also be included by their consumers. -/
theorem finiteModelConstructionCost_le_sourceMetrics
    (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled)
    (hw : 0 < source.worlds.size) (ht : 0 < source.things.size) :
    (compiled.tables.toFiniteModel4CachedCosted source.worlds.size source.things.size hw ht
      (compileModelSource_ok_lookups_agree source compiled success)
      (compileModelSource_ok_inherenceCacheValid source compiled success)
      (compileModelSource_ok_tableDimensions source compiled success).1
      (compileModelSource_ok_tableDimensions source compiled success).2).cost ≤
      4 + (sourceMetrics source).worlds *
        (7 * (sourceMetrics source).productFamilySlots +
          20 * (sourceMetrics source).productFamilies) +
        2 * (sourceMetrics source).productFamilies := by
  have bound := FactTables.toFiniteModel4CachedCosted_cost_le compiled.tables
    source.worlds.size source.things.size hw ht
    (compileModelSource_ok_lookups_agree source compiled success)
    (compileModelSource_ok_inherenceCacheValid source compiled success)
    (compileModelSource_ok_tableDimensions source compiled success).1
    (compileModelSource_ok_tableDimensions source compiled success).2
  rw [compileModelSource_ok_tableFamilies source compiled success] at bound
  obtain ⟨families, slots⟩ := compileModelSource_ok_familySizes source compiled success
  simpa only [families, slots, sourceMetrics] using bound

/-- The cached constructor costs at most 26N² for source size N. Family
records and both witness arrays share one source-size budget, so their
world-replicated conversion costs at most 20N². -/
theorem finiteModelConstructionCost_le_sourceInputSize_sq
    (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled)
    (hw : 0 < source.worlds.size) (ht : 0 < source.things.size) :
    (compiled.tables.toFiniteModel4CachedCosted source.worlds.size source.things.size hw ht
      (compileModelSource_ok_lookups_agree source compiled success)
      (compileModelSource_ok_inherenceCacheValid source compiled success)
      (compileModelSource_ok_tableDimensions source compiled success).1
      (compileModelSource_ok_tableDimensions source compiled success).2).cost ≤
      26 * (sourceMetrics source).inputSize ^ 2 := by
  apply (finiteModelConstructionCost_le_sourceMetrics source compiled success hw ht).trans
  let m := sourceMetrics source
  have worldBound : m.worlds ≤ m.inputSize := by unfold SourceMetrics.inputSize; omega
  have familyBound : m.productFamilies ≤ m.inputSize := by unfold SourceMetrics.inputSize; omega
  have slotsBound : m.productFamilies + m.productFamilySlots ≤ m.inputSize := by
    unfold SourceMetrics.inputSize; omega
  have positive : 1 ≤ m.inputSize := by unfold SourceMetrics.inputSize; omega
  have visits : m.worlds * (m.productFamilies + m.productFamilySlots) ≤ m.inputSize ^ 2 := by
    simpa only [Nat.pow_two] using Nat.mul_le_mul worldBound slotsBound
  have linear : m.inputSize ≤ m.inputSize ^ 2 := by
    simpa only [Nat.mul_one, ← Nat.pow_two] using Nat.mul_le_mul_left m.inputSize positive
  have weighted : m.worlds * (7 * m.productFamilySlots + 20 * m.productFamilies) ≤
      20 * m.inputSize ^ 2 := by
    calc
      _ ≤ m.worlds * (20 * (m.productFamilies + m.productFamilySlots)) :=
        Nat.mul_le_mul_left _ (by omega)
      _ = 20 * (m.worlds * (m.productFamilies + m.productFamilySlots)) := by ac_rfl
      _ ≤ _ := Nat.mul_le_mul_left 20 visits
  change 4 + m.worlds * (7 * m.productFamilySlots + 20 * m.productFamilies) +
    2 * m.productFamilies ≤ 26 * m.inputSize ^ 2
  omega

/-- One concrete reconstruction of a successfully compiled source costs at
most `537N⁴`: table rebuilding costs at most `511N⁴`, and finite-model
construction costs at most `26N²`. Both stages use the returned AST's tables.
Repeated invocations need separate accounting; runtime sharing can skip them. -/
theorem compileVerifiedModelCosted_source_bound
    (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled)
    (hw : 0 < compiled.ast.worldCount) (ht : 0 < compiled.ast.thingCount) :
    (compileVerifiedModelCosted compiled.ast hw ht
      (compileModelSource_ok_wellBounded source compiled success)).cost ≤
      537 * (sourceMetrics source).inputSize ^ 4 := by
  have invariant := compileModelSource_ok_constructionInvariant source compiled success
  have hwSource : 0 < source.worlds.size := by simpa only [invariant.worldCount] using hw
  have htSource : 0 < source.things.size := by simpa only [invariant.thingCount] using ht
  have tables := explicitCompilation_source_scalar_bound source compiled success
  have model := finiteModelConstructionCost_le_sourceInputSize_sq
    source compiled success hwSource htSource
  have positive := sourceMetrics_inputSize_pos source
  have square : (sourceMetrics source).inputSize ^ 2 ≤ (sourceMetrics source).inputSize ^ 4 :=
    Nat.pow_le_pow_right positive (by omega)
  have modelBound := model.trans (Nat.mul_le_mul_left 26 square)
  rw [compileVerifiedModelCosted_cost]
  simp only [← invariant.tables, invariant.worldCount, invariant.thingCount]
  omega

/-- Reconstructing the returned AST yields the same source-sized model used
by the successful-compilation bound. No unrelated model is supplied. -/
theorem compileVerifiedModel_source_inputSize_bound
    (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled)
    (hw : 0 < compiled.ast.worldCount) (ht : 0 < compiled.ast.thingCount) :
    checkerInputSize (compileVerifiedModel compiled.ast hw ht
      (compileModelSource_ok_wellBounded source compiled success)) ≤
      3 * (sourceMetrics source).inputSize ^ 2 := by
  have invariant := compileModelSource_ok_constructionInvariant source compiled success
  have hwSource : 0 < source.worlds.size := by simpa only [invariant.worldCount] using hw
  have htSource : 0 < source.things.size := by simpa only [invariant.thingCount] using ht
  have bound := finiteModelInputSize_le_sourceInputSize_sq source compiled success hwSource htSource
  simpa only [compileVerifiedModel, ← invariant.tables, invariant.worldCount, invariant.thingCount]
    using bound

end LeanUfo.UFO.DSL.Complexity
