import LeanUfo.UFO.DSL.Compiler

/-!
# Explicit input metrics for DSL complexity results

The separation between `SourceMetrics` and `ModelMetrics`, and between a fixed
axiom registry and a registry supplied as input, is the data-complexity versus
combined-complexity distinction used in finite-model checking; see Vardi's
overview and Madelaine--Martin.  Counting every explicitly stored fact and
witness slot also rules out silently treating a succinct/oracular relation as
a constant-size input.  Bibliographic links are in `docs/dsl/complexity.md`.
-/

namespace LeanUfo.UFO.DSL.Complexity

def NamedDerivedFact.referenceCount : NamedDerivedFact → Nat
  | .unary .. => 1
  | .binary .. => 2
  | .ternary .. => 3
  | .quaternary .. => 4

def NamedScopedFact.referenceCount : NamedScopedFact → Nat
  | .unary .. => 1
  | .binary .. => 2
  | .ternary .. => 3
  | .tupleProjection .. => 2
  | .derived fact _ => NamedDerivedFact.referenceCount fact

structure SourceMetrics where
  worlds : Nat
  things : Nat
  facts : Nat
  nameReferences : Nat
  expandedFacts : Nat
  taxonomyFacts : Nat
  specializationFactsUpper : Nat
  productFamilies : Nat
  productFamilySlots : Nat
  tupleProjections : Nat
  maxProjectionArity : Nat
  relationCells : Nat
  projectionCells : Nat
deriving Repr, Inhabited, DecidableEq

def sourceMetrics (source : ModelSource) : SourceMetrics :=
  let familySlots :=
    (source.productFamilies.toList.map NamedProductFamily.slotCount).sum
  let maxArity := source.productFamilies.foldl
    (fun n pf => max n pf.dimensionThings.size) 0
  let projectionArity := source.facts.foldl
    (fun n fact => max n fact.projectionArity) maxArity
  let worlds := source.worlds.size
  let things := source.things.size
  let expandedFacts :=
    (source.facts.toList.map (NamedScopedFact.expansionWeight worlds)).sum
  let taxonomyFacts :=
    (source.facts.toList.map (NamedScopedFact.taxonomyWeight worlds)).sum
  { worlds := source.worlds.size
    things := source.things.size
    facts := source.facts.size
    nameReferences := source.facts.foldl
      (fun n fact => n + NamedScopedFact.referenceCount fact) 0
    expandedFacts := expandedFacts
    taxonomyFacts := taxonomyFacts
    specializationFactsUpper := taxonomyFacts * (worlds + 1)
    productFamilies := source.productFamilies.size
    productFamilySlots := familySlots
    tupleProjections := source.facts.foldl
      (fun n fact => match fact with | .tupleProjection .. => n + 1 | _ => n) 0
    maxProjectionArity := projectionArity
    relationCells :=
      UnaryField.count * things * worlds +
      BinaryField.count * things ^ 2 * worlds +
      TernaryField.count * things ^ 3 * worlds
    projectionCells := things * projectionArity * worlds }

structure ModelMetrics where
  worlds : Nat
  things : Nat
  unaryFacts : Nat
  binaryFacts : Nat
  ternaryFacts : Nat
  tupleProjections : Nat
  productFamilies : Nat
  productFamilySlots : Nat
  unaryCells : Nat
  binaryCells : Nat
  ternaryCells : Nat
  projectionCells : Nat
  closureCells : Nat
  nextHopCells : Nat
deriving Repr, Inhabited, DecidableEq

private def tableEntryCount {α : Type} (tables : Std.HashMap String (Array α)) : Nat :=
  tables.fold (fun n _ entries => n + entries.size) 0

def modelMetrics (worldCount thingCount : Nat) (tables : FactTables) : ModelMetrics :=
  { worlds := worldCount
    things := thingCount
    unaryFacts := tableEntryCount tables.unary
    binaryFacts := tableEntryCount tables.binary
    ternaryFacts := tableEntryCount tables.ternary
    tupleProjections := tables.tupleProjection.size
    productFamilies := tables.productFamilies.size
    productFamilySlots := tables.productFamilies.foldl
      (fun n pf => n + pf.dimensionThings.size + pf.typeThings.size) 0
    unaryCells := tables.unaryCells.size
    binaryCells := tables.binaryCells.size
    ternaryCells := tables.ternaryCells.size
    projectionCells := tables.projectionCells.size
    closureCells := tables.inherenceClosures.foldl (fun n cells => n + cells.size) 0
    nextHopCells := tables.inherenceNextHops.foldl (fun n cells => n + cells.size) 0 }

/-- Scalar size of the complete explicit source representation. -/
def SourceMetrics.inputSize (m : SourceMetrics) : Nat :=
  m.worlds + m.things + m.facts + m.nameReferences + m.expandedFacts +
    m.taxonomyFacts + m.specializationFactsUpper + m.productFamilies +
    m.productFamilySlots + m.tupleProjections + m.maxProjectionArity +
    m.relationCells + m.projectionCells + 1

/-- Sum of charged stages after successful name/reference resolution. -/
def SourceMetrics.resolvedCompilerCostBound (m : SourceMetrics) : Nat :=
  (m.expandedFacts + m.facts) +
    (m.expandedFacts + m.taxonomyFacts) +
    m.taxonomyFacts * (m.worlds + 2) +
    (m.projectionCells + m.specializationFactsUpper) +
    (4 * m.specializationFactsUpper + m.productFamilies +
      m.relationCells + m.projectionCells +
      m.worlds * (13 * m.things ^ 3 + 9 * m.things ^ 2 + 1))

/-!
The scalar corollary comes after the multivariate formula: it is obtained by
bounding each independently sized component by the explicit encoded input
size. This is not used as the executable bound, since the
multivariate expression above remains substantially more informative.
-/

/-- The concrete resolved-compiler formula is bounded by a quartic polynomial
in the complete explicit source size. -/
theorem SourceMetrics.resolvedCompilerCostBound_le_inputSize_pow4
    (m : SourceMetrics) :
    m.resolvedCompilerCostBound ≤ 64 * m.inputSize ^ 4 := by
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
  have hexpanded : m.expandedFacts ≤ n := by
    simp only [n, SourceMetrics.inputSize]
    omega
  have htaxonomy : m.taxonomyFacts ≤ n := by
    simp only [n, SourceMetrics.inputSize]
    omega
  have hspecialization : m.specializationFactsUpper ≤ n := by
    simp only [n, SourceMetrics.inputSize]
    omega
  have hfamilies : m.productFamilies ≤ n := by
    simp only [n, SourceMetrics.inputSize]
    omega
  have hrelation : m.relationCells ≤ n := by
    simp only [n, SourceMetrics.inputSize]
    omega
  have hprojection : m.projectionCells ≤ n := by
    simp only [n, SourceMetrics.inputSize]
    omega
  have hTaxonomyProduct :
      m.taxonomyFacts * (m.worlds + 2) ≤ n * (n + 2) := by
    exact Nat.mul_le_mul htaxonomy (Nat.add_le_add_right hworlds 2)
  have hClosure :
      m.worlds * (13 * m.things ^ 3 + 9 * m.things ^ 2 + 1) ≤
        n * (13 * n ^ 3 + 9 * n ^ 2 + 1) := by
    apply Nat.mul_le_mul hworlds
    apply Nat.add_le_add
    · apply Nat.add_le_add
      · exact Nat.mul_le_mul_left 13 (Nat.pow_le_pow_left hthings 3)
      · exact Nat.mul_le_mul_left 9 (Nat.pow_le_pow_left hthings 2)
    · rfl
  unfold SourceMetrics.resolvedCompilerCostBound
  change _ ≤ 64 * n ^ 4
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
  have hTaxonomyExpansion : n * (n + 2) = n ^ 2 + 2 * n := by
    simp [Nat.mul_add, Nat.pow_succ, Nat.mul_comm]
  have hTaxonomyScalar :
      m.taxonomyFacts * (m.worlds + 2) ≤ 3 * n ^ 2 := by
    apply hTaxonomyProduct.trans
    rw [hTaxonomyExpansion]
    omega
  have hClosureExpansion :
      n * (13 * n ^ 3 + 9 * n ^ 2 + 1) =
        13 * n ^ 4 + 9 * n ^ 3 + n := by
    simp [Nat.mul_add, Nat.pow_succ, Nat.mul_comm,
      Nat.mul_left_comm]
  have hClosureScalar :
      m.worlds * (13 * m.things ^ 3 + 9 * m.things ^ 2 + 1) ≤
        23 * n ^ 4 := by
    apply hClosure.trans
    rw [hClosureExpansion]
    omega
  omega

/-- Scalar size of primitive compiled facts and independently sized witnesses. -/
def ModelMetrics.inputSize (m : ModelMetrics) : Nat :=
  m.worlds + m.things + m.unaryFacts + m.binaryFacts + m.ternaryFacts +
    m.tupleProjections + m.productFamilies + m.productFamilySlots +
    m.unaryCells + m.binaryCells + m.ternaryCells + m.projectionCells +
    m.closureCells + m.nextHopCells + 1

/-!
## Checker-side explicit encoding size

The fixed-registry checker receives `FiniteModel4`, whose relations are
functions at the type boundary.  The production compiler realizes those
functions with dense finite tables, so a scalar checker theorem must charge
that explicit footprint rather than treating the functions as succinct
oracles. Product-family records and both of their witness arrays are included
independently because axiom 99 scans them.
-/

def checkerProductFamilySlots (M : FiniteModel4) : Nat :=
  (M.productFamilies.toList.map fun family =>
    family.dimensionThings.size + family.typeThings.size).sum

def checkerRelationCells (M : FiniteModel4) : Nat :=
  UnaryField.count * M.thingCount * M.worldCount +
    BinaryField.count * M.thingCount ^ 2 * M.worldCount +
    TernaryField.count * M.thingCount ^ 3 * M.worldCount

/-- Complete scalar size used by the fixed-registry data-complexity corollary.
The trailing one makes the size positive even for the empty finite model. -/
def checkerInputSize (M : FiniteModel4) : Nat :=
  M.worldCount + M.thingCount + checkerRelationCells M +
    M.productFamilies.size + checkerProductFamilySlots M + 1

theorem checkerInputSize_pos (M : FiniteModel4) : 0 < checkerInputSize M := by
  unfold checkerInputSize
  omega

theorem worldCount_le_checkerInputSize (M : FiniteModel4) :
    M.worldCount ≤ checkerInputSize M := by
  unfold checkerInputSize
  omega

theorem thingCount_le_checkerInputSize (M : FiniteModel4) :
    M.thingCount ≤ checkerInputSize M := by
  unfold checkerInputSize
  omega

theorem productFamilyCount_le_checkerInputSize (M : FiniteModel4) :
    M.productFamilies.size ≤ checkerInputSize M := by
  unfold checkerInputSize
  omega

theorem productFamilySlots_le_checkerInputSize (M : FiniteModel4) :
    checkerProductFamilySlots M ≤ checkerInputSize M := by
  unfold checkerInputSize
  omega

private theorem nat_le_list_sum_of_mem (n : Nat) (xs : List Nat)
    (h : n ∈ xs) : n ≤ xs.sum := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
      simp only [List.mem_cons] at h
      rcases h with h | h
      · subst x
        simp
      · have hle := ih h
        simp only [List.sum_cons]
        omega

theorem productFamilyEntrySlots_le_checkerProductFamilySlots
    (M : FiniteModel4) (i : Fin M.productFamilies.size) :
    M.productFamilies[i].dimensionThings.size +
        M.productFamilies[i].typeThings.size ≤ checkerProductFamilySlots M := by
  unfold checkerProductFamilySlots
  apply nat_le_list_sum_of_mem
  apply List.mem_map.mpr
  exact ⟨M.productFamilies[i], by simp, rfl⟩

theorem productFamilyDimension_le_checkerInputSize
    (M : FiniteModel4) (i : Fin M.productFamilies.size) :
    M.productFamilies[i].dimensionThings.size ≤ checkerInputSize M := by
  have hentry := productFamilyEntrySlots_le_checkerProductFamilySlots M i
  have hslots := productFamilySlots_le_checkerInputSize M
  omega

theorem sourceMetrics_inputSize_pos (source : ModelSource) :
    0 < (sourceMetrics source).inputSize := by
  unfold SourceMetrics.inputSize
  omega

/-- Source-metric form of the executable product-family resolution bound. -/
theorem productFamilyResolutionCost_le_sourceMetrics
    (source : ModelSource) (things : NameIndex) :
    (mapArrayExceptCosted source.productFamilies
      (resolveNamedProductFamilyIndexedCosted things)).cost ≤
      (sourceMetrics source).productFamilies *
        (2 * (sourceMetrics source).productFamilySlots + 4) := by
  simpa [sourceMetrics] using
    resolveNamedProductFamiliesIndexedCosted_cost_le things source.productFamilies

theorem namedProjectionArity_le_sourceMetrics (source : ModelSource) :
    projectionArityOfNamedFacts source.facts ≤
      (sourceMetrics source).maxProjectionArity := by
  let familyArity := source.productFamilies.foldl
    (fun n pf => max n pf.dimensionThings.size) 0
  have foldMonotone : ∀ (xs : List NamedScopedFact) (left right : Nat),
      left ≤ right →
      xs.foldl (fun n fact => max n fact.projectionArity) left ≤
        xs.foldl (fun n fact => max n fact.projectionArity) right := by
    intro xs
    induction xs with
    | nil => simp
    | cons fact facts ih =>
        intro left right h
        simp only [List.foldl_cons]
        apply ih
        exact max_le (le_trans h (le_max_left _ _)) (le_max_right _ _)
  unfold projectionArityOfNamedFacts
  rw [← Array.foldl_toList]
  have bound := foldMonotone source.facts.toList 0 familyArity (Nat.zero_le _)
  simpa [sourceMetrics, familyArity, Array.foldl_toList] using bound

/--
On successful batch resolution, the metric's scope-expanded fact count is the
size produced by the executable expansion pass.  This is the array-level
composition of the per-fact resolution invariant, not a parallel recurrence.
-/
theorem resolved_expansion_size_eq_sourceMetrics
    (source : ModelSource) (worlds things : NameIndex)
    (resolved : Array ScopedCompiledFact)
    (h : (mapArrayExceptCosted source.facts
      (resolveNamedFactIndexedCosted worlds things)).value = .ok resolved) :
    (expandScopedFactsCosted source.worlds.size resolved).value.size =
      (sourceMetrics source).expandedFacts := by
  rw [expandScopedFactsCosted_value_size]
  have weights := resolveNamedFactsIndexed_preserves_weights
    source.worlds.size worlds things source.facts resolved h
  simpa [sourceMetrics] using weights.1

/-- Exact source-metric charge of scope expansion after successful resolution. -/
theorem resolved_expansion_cost_eq_sourceMetrics
    (source : ModelSource) (worlds things : NameIndex)
    (resolved : Array ScopedCompiledFact)
    (h : (mapArrayExceptCosted source.facts
      (resolveNamedFactIndexedCosted worlds things)).value = .ok resolved) :
    (expandScopedFactsCosted source.worlds.size resolved).cost =
      (sourceMetrics source).expandedFacts + (sourceMetrics source).facts := by
  rw [expandScopedFactsCosted_cost]
  have charges : ∀ xs : List ScopedCompiledFact,
      (xs.map (ScopedCompiledFact.expansionCharge source.worlds.size)).sum =
        (xs.map (ScopedCompiledFact.expansionWeight source.worlds.size)).sum +
          xs.length := by
    intro xs
    induction xs with
    | nil => simp
    | cons fact facts ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        rw [ih]
        cases fact <;>
          simp [ScopedCompiledFact.expansionCharge,
            ScopedCompiledFact.expansionWeight, ScopedCompiledFact.scope]
        all_goals omega
  rw [charges]
  have weights := resolveNamedFactsIndexed_preserves_weights
    source.worlds.size worlds things source.facts resolved h
  have sizeEq : resolved.size = source.facts.size := by
    exact mapArrayExceptCosted_ok_size source.facts
      (resolveNamedFactIndexedCosted worlds things) resolved h
  rw [weights.1]
  simpa [sourceMetrics] using sizeEq

/--
On successful resolution, the source taxonomy metric is exactly the number of
facts emitted by the executable scope and taxonomy passes.  Thus the compiler
bound charges the concrete materialized representation, including duplicates
that dense-table insertion later treats idempotently.
-/
theorem resolved_taxonomy_size_eq_sourceMetrics
    (source : ModelSource) (worlds things : NameIndex)
    (resolved : Array ScopedCompiledFact)
    (h : (mapArrayExceptCosted source.facts
      (resolveNamedFactIndexedCosted worlds things)).value = .ok resolved) :
    (addTaxonomyFactsCosted
      (expandScopedFactsCosted source.worlds.size resolved).value).value.size =
      (sourceMetrics source).taxonomyFacts := by
  rw [addTaxonomyFactsCosted_value_size,
    expandScopedFactsCosted_taxonomyEmissionCount]
  have weights := resolveNamedFactsIndexed_preserves_weights
    source.worlds.size worlds things source.facts resolved h
  simpa [sourceMetrics] using weights.2

/-- Exact operational taxonomy charge in source metrics. -/
theorem resolved_taxonomy_cost_eq_sourceMetrics
    (source : ModelSource) (worlds things : NameIndex)
    (resolved : Array ScopedCompiledFact)
    (h : (mapArrayExceptCosted source.facts
      (resolveNamedFactIndexedCosted worlds things)).value = .ok resolved) :
    (addTaxonomyFactsCosted
      (expandScopedFactsCosted source.worlds.size resolved).value).cost =
      (sourceMetrics source).expandedFacts +
        (sourceMetrics source).taxonomyFacts := by
  rw [addTaxonomyFactsCosted_cost]
  rw [resolved_expansion_size_eq_sourceMetrics source worlds things resolved h]
  change (sourceMetrics source).expandedFacts +
    (addTaxonomyFactsCosted
      (expandScopedFactsCosted source.worlds.size resolved).value).value.size = _
  rw [resolved_taxonomy_size_eq_sourceMetrics source worlds things resolved h]

/--
Reflexive specialization is charged after taxonomy materialization, using the
actual materialized taxonomy count rather than the original source fact count.
-/
theorem resolved_specialization_cost_le_sourceMetrics
    (source : ModelSource) (worlds things : NameIndex)
    (resolved : Array ScopedCompiledFact)
    (h : (mapArrayExceptCosted source.facts
      (resolveNamedFactIndexedCosted worlds things)).value = .ok resolved) :
    let taxonomyFacts := (addTaxonomyFactsCosted
      (expandScopedFactsCosted source.worlds.size resolved).value).value
    (addReflexiveSpecializationFactsCosted source.worlds.size taxonomyFacts).cost ≤
      (sourceMetrics source).taxonomyFacts *
        ((sourceMetrics source).worlds + 2) := by
  dsimp
  have bound := addReflexiveSpecializationFactsCosted_cost_le
    source.worlds.size
    (addTaxonomyFactsCosted
      (expandScopedFactsCosted source.worlds.size resolved).value).value
  rw [resolved_taxonomy_size_eq_sourceMetrics source worlds things resolved h] at bound
  simpa [sourceMetrics] using bound

/-- Source metric bound for the size passed to validation and table building. -/
theorem resolved_specialization_size_le_sourceMetrics
    (source : ModelSource) (worlds things : NameIndex)
    (resolved : Array ScopedCompiledFact)
    (h : (mapArrayExceptCosted source.facts
      (resolveNamedFactIndexedCosted worlds things)).value = .ok resolved) :
    let taxonomyFacts := (addTaxonomyFactsCosted
      (expandScopedFactsCosted source.worlds.size resolved).value).value
    (addReflexiveSpecializationFactsCosted
      source.worlds.size taxonomyFacts).value.size ≤
      (sourceMetrics source).specializationFactsUpper := by
  dsimp
  have bound := addReflexiveSpecializationFactsCosted_value_size_le
    source.worlds.size
    (addTaxonomyFactsCosted
      (expandScopedFactsCosted source.worlds.size resolved).value).value
  rw [resolved_taxonomy_size_eq_sourceMetrics source worlds things resolved h] at bound
  simpa [sourceMetrics] using bound

/--
No compiler-generated fact can increase tuple-projection arity.  Consequently
both projection validation and dense projection-table initialization use a
dimension bounded by the explicit source metric.
-/
theorem resolved_specialization_projectionArity_le_sourceMetrics
    (source : ModelSource) (worlds things : NameIndex)
    (resolved : Array ScopedCompiledFact)
    (h : (mapArrayExceptCosted source.facts
      (resolveNamedFactIndexedCosted worlds things)).value = .ok resolved) :
    let expanded := (expandScopedFactsCosted source.worlds.size resolved).value
    let taxonomy := (addTaxonomyFactsCosted expanded).value
    let specialized :=
      (addReflexiveSpecializationFactsCosted source.worlds.size taxonomy).value
    projectionArityOfFacts specialized ≤
      (sourceMetrics source).maxProjectionArity := by
  dsimp
  apply le_trans (addReflexiveSpecializationFactsCosted_projectionArity_le
    source.worlds.size _)
  apply le_trans (addTaxonomyFactsCosted_projectionArity_le _)
  apply le_trans (expandScopedFactsCosted_projectionArity_le
    source.worlds.size resolved)
  rw [resolveNamedFactsIndexed_preserves_projectionArity worlds things
    source.facts resolved h]
  exact namedProjectionArity_le_sourceMetrics source

theorem resolved_projectionValidationCost_le_sourceMetrics
    (source : ModelSource) (worlds things : NameIndex)
    (resolved : Array ScopedCompiledFact)
    (h : (mapArrayExceptCosted source.facts
      (resolveNamedFactIndexedCosted worlds things)).value = .ok resolved) :
    let expanded := (expandScopedFactsCosted source.worlds.size resolved).value
    let taxonomy := (addTaxonomyFactsCosted expanded).value
    let specialized :=
      (addReflexiveSpecializationFactsCosted source.worlds.size taxonomy).value
    (validateTupleProjectionsCosted source.worlds.size source.things.size
      specialized).cost ≤
      (sourceMetrics source).projectionCells +
        (sourceMetrics source).specializationFactsUpper := by
  dsimp
  have arity := resolved_specialization_projectionArity_le_sourceMetrics
    source worlds things resolved h
  have size := resolved_specialization_size_le_sourceMetrics
    source worlds things resolved h
  dsimp at arity size
  have cells := Nat.mul_le_mul_right source.worlds.size
    (Nat.mul_le_mul_left source.things.size arity)
  calc
    source.things.size * projectionArityOfFacts
          (addReflexiveSpecializationFacts source.worlds.size
            (addTaxonomyFacts (expandScopedFacts source.worlds.size resolved))) *
        source.worlds.size +
        (addReflexiveSpecializationFacts source.worlds.size
          (addTaxonomyFacts (expandScopedFacts source.worlds.size resolved))).size ≤
      source.things.size * (sourceMetrics source).maxProjectionArity *
          source.worlds.size +
        (sourceMetrics source).specializationFactsUpper :=
      Nat.add_le_add cells size
    _ = (sourceMetrics source).projectionCells +
        (sourceMetrics source).specializationFactsUpper := by
      simp [sourceMetrics]

theorem resolved_explicitCompilationCost_le_sourceMetrics
    (source : ModelSource) (worlds things : NameIndex)
    (resolved : Array ScopedCompiledFact)
    (productFamilies : Array ProductFamilySpec)
    (hFacts : (mapArrayExceptCosted source.facts
      (resolveNamedFactIndexedCosted worlds things)).value = .ok resolved)
    (hFamilies : (mapArrayExceptCosted source.productFamilies
      (resolveNamedProductFamilyIndexedCosted things)).value =
        .ok productFamilies) :
    let expanded := (expandScopedFactsCosted source.worlds.size resolved).value
    let taxonomy := (addTaxonomyFactsCosted expanded).value
    let specialized :=
      (addReflexiveSpecializationFactsCosted source.worlds.size taxonomy).value
    let ast : ModelAST :=
      { worldCount := source.worlds.size
        thingCount := source.things.size
        facts := specialized
        productFamilies := productFamilies }
    (compileExplicitModelASTCosted ast).cost ≤
      4 * (sourceMetrics source).specializationFactsUpper +
        (sourceMetrics source).productFamilies +
        (sourceMetrics source).relationCells +
        (sourceMetrics source).projectionCells +
        source.worlds.size *
          (13 * source.things.size ^ 3 + 9 * source.things.size ^ 2 + 1) := by
  dsimp
  rw [compileExplicitModelASTCosted_cost_polynomial]
  have size := resolved_specialization_size_le_sourceMetrics
    source worlds things resolved hFacts
  have arity := resolved_specialization_projectionArity_le_sourceMetrics
    source worlds things resolved hFacts
  dsimp at size arity
  have familySize := mapArrayExceptCosted_ok_size source.productFamilies
    (resolveNamedProductFamilyIndexedCosted things) productFamilies hFamilies
  have fourSize := Nat.mul_le_mul_left 4 size
  have projectionCells := Nat.mul_le_mul_right source.worlds.size
    (Nat.mul_le_mul_left source.things.size arity)
  calc
    4 *
          (addReflexiveSpecializationFacts source.worlds.size
            (addTaxonomyFacts (expandScopedFacts source.worlds.size resolved))).size +
        productFamilies.size +
        UnaryField.count * source.things.size * source.worlds.size +
        BinaryField.count * source.things.size * source.things.size * source.worlds.size +
        TernaryField.count * source.things.size * source.things.size *
          source.things.size * source.worlds.size +
        source.things.size *
          projectionArityOfFacts
            (addReflexiveSpecializationFacts source.worlds.size
              (addTaxonomyFacts (expandScopedFacts source.worlds.size resolved))) *
          source.worlds.size +
        source.worlds.size *
          (13 * source.things.size ^ 3 + 9 * source.things.size ^ 2 + 1) ≤
      4 * (sourceMetrics source).specializationFactsUpper +
        source.productFamilies.size +
        UnaryField.count * source.things.size * source.worlds.size +
        BinaryField.count * source.things.size * source.things.size * source.worlds.size +
        TernaryField.count * source.things.size * source.things.size *
          source.things.size * source.worlds.size +
        source.things.size * (sourceMetrics source).maxProjectionArity *
          source.worlds.size +
        source.worlds.size *
          (13 * source.things.size ^ 3 + 9 * source.things.size ^ 2 + 1) := by
      omega
    _ = 4 * (sourceMetrics source).specializationFactsUpper +
        (sourceMetrics source).productFamilies +
        (sourceMetrics source).relationCells +
        (sourceMetrics source).projectionCells +
        source.worlds.size *
          (13 * source.things.size ^ 3 + 9 * source.things.size ^ 2 + 1) := by
      simp [sourceMetrics, Nat.pow_succ, Nat.mul_assoc, Nat.add_assoc]

theorem materializeResolvedFactsCosted_cost_le_sourceMetrics
    (source : ModelSource) (worlds things : NameIndex)
    (resolved : Array ScopedCompiledFact)
    (hFacts : (resolveSourceFactsCosted source worlds things).value = .ok resolved)
    : (materializeResolvedFactsCosted source resolved).cost ≤
      (sourceMetrics source).expandedFacts + (sourceMetrics source).facts +
      ((sourceMetrics source).expandedFacts + (sourceMetrics source).taxonomyFacts) +
      (sourceMetrics source).taxonomyFacts * ((sourceMetrics source).worlds + 2) := by
  rw [materializeResolvedFactsCosted_cost]
  have scopeCost := resolved_expansion_cost_eq_sourceMetrics
    source worlds things resolved hFacts
  have taxonomyCost := resolved_taxonomy_cost_eq_sourceMetrics
    source worlds things resolved hFacts
  have specializationCost := resolved_specialization_cost_le_sourceMetrics
    source worlds things resolved hFacts
  omega

/--
Operational bound for the named production tail.  The proof splits only on the
real validation result; materialization is total and validation retains the
production short-circuit order.
-/
theorem compileResolvedSourceCosted_cost_le_sourceMetrics
    (source : ModelSource) (worlds things : NameIndex)
    (resolved : Array ScopedCompiledFact)
    (productFamilies : Array ProductFamilySpec)
    (hFacts : (resolveSourceFactsCosted source worlds things).value = .ok resolved)
    (hFamilies : (resolveSourceProductFamiliesCosted source things).value =
      .ok productFamilies) :
    (compileResolvedSourceCosted source resolved productFamilies).cost ≤
      (sourceMetrics source).resolvedCompilerCostBound := by
  cases hValidation : (validateTupleProjectionsCosted
    source.worlds.size source.things.size
      (materializeResolvedFactsCosted source resolved).value).value with
  | error validationError =>
      have hValidation' : validateTupleProjections source.worlds.size
          source.things.size
            (addReflexiveSpecializationFacts source.worlds.size
              (addTaxonomyFacts (expandScopedFacts source.worlds.size resolved))) =
          .error validationError := by
        simpa using hValidation
      simp [compileResolvedSourceCosted,
        exceptBindCosted, exceptOkCosted]
      rw [hValidation']
      simp only
      have materializeCost := materializeResolvedFactsCosted_cost_le_sourceMetrics
        source worlds things resolved hFacts
      have validationCost := resolved_projectionValidationCost_le_sourceMetrics
        source worlds things resolved hFacts
      dsimp [materializeResolvedFactsCosted] at validationCost
      unfold SourceMetrics.resolvedCompilerCostBound
      omega
  | ok validationResult =>
      have hValidation' : validateTupleProjections source.worlds.size
          source.things.size
            (addReflexiveSpecializationFacts source.worlds.size
              (addTaxonomyFacts (expandScopedFacts source.worlds.size resolved))) =
          .ok validationResult := by
        simpa using hValidation
      simp [compileResolvedSourceCosted,
        exceptBindCosted, exceptOkCosted]
      rw [hValidation']
      simp only
      have materializeCost := materializeResolvedFactsCosted_cost_le_sourceMetrics
        source worlds things resolved hFacts
      have validationCost := resolved_projectionValidationCost_le_sourceMetrics
        source worlds things resolved hFacts
      have explicitCost := resolved_explicitCompilationCost_le_sourceMetrics
        source worlds things resolved productFamilies hFacts hFamilies
      dsimp [materializeResolvedFactsCosted] at validationCost
      dsimp [materializeResolvedFactsCosted] at explicitCost
      have closureEq : source.worlds.size *
            (13 * source.things.size ^ 3 + 9 * source.things.size ^ 2 + 1) =
          (sourceMetrics source).worlds *
            (13 * (sourceMetrics source).things ^ 3 +
              9 * (sourceMetrics source).things ^ 2 + 1) := by
        simp [sourceMetrics]
      rw [closureEq] at explicitCost
      unfold SourceMetrics.resolvedCompilerCostBound
      omega

end LeanUfo.UFO.DSL.Complexity
