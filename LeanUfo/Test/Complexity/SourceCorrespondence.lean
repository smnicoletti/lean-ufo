import LeanUfo.UFO.DSL.Complexity

/-!
# Successful source-result correspondence

General examples exercise the proof boundary without assuming native equality
of function-valued tables. Concrete tests cover empty input, scope expansion,
taxonomy, family storage, and source rejection. Successful compilation supplies
coordinate bounds as well as construction consistency. Cost-composition tests
use the returned tables and charge model construction before one aggregate
checker call. Separate tests charge table reconstruction for each selected
registry entry. Later applications cover prepared checked and semantic proofs.
`Test/Complexity/Certification.lean` tests their workflow composition.
-/

namespace LeanUfo.Test.Complexity.SourceCorrespondence

open LeanUfo.UFO.DSL
open private checkedAxiomProofScript from LeanUfo.UFO.DSL.Certificate.Generation

private def cheapFailure : Complexity.BoundedCheck :=
  .of (fun _ => Complexity.Costed.tick false 1) (bound := 1) (by decide)

private def expensiveLater : Complexity.BoundedCheck :=
  .of (fun _ => Complexity.Costed.tick true 100) (bound := 100) (by decide)

private def earlyExitRegistry := #[cheapFailure, expensiveLater]

-- Synthetic callbacks charge one and 100. Early exit costs four, but a
-- separate call to the later entry costs 100.
-- Its valid upper bound is the registry budget 107, not the first run's cost.
example : (Complexity.checkBoundedRegistryCosted earlyExitRegistry).cost = 4 := by decide
example : (expensiveLater.run ()).cost = 100 := rfl
example : Complexity.boundedRegistryCostBound earlyExitRegistry = 107 := by decide
example : (expensiveLater.run ()).cost ≤
    Complexity.boundedRegistryCostBound earlyExitRegistry :=
  Complexity.boundedCheck_cost_le_registryBound _ _ (by simp [earlyExitRegistry])

example (source : ModelSource) :
    match compileModelSource source with
    | .error _ => True
    | .ok compiled => compiled.ConstructionInvariant source := by
  cases success : compileModelSource source with
  | error _ => trivial
  | ok compiled => exact compileModelSource_ok_constructionInvariant source compiled success

example (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled) :
    compiled.tables = compileExplicitModelAST compiled.ast :=
  (compileModelSource_ok_constructionInvariant source compiled success).tables

-- A caller cannot substitute a record with a different world count.
example (source : ModelSource) (compiled : CompiledModelSource)
    (different : compiled.ast.worldCount ≠ source.worlds.size) :
    compileModelSource source ≠ .ok compiled := by
  intro success
  exact different (compileModelSource_ok_constructionInvariant source compiled success).worldCount

example (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled) :
    compiled.tables.sparseLookups source.worlds.size source.things.size =
      compiled.tables.denseLookups source.worlds.size source.things.size :=
  compileModelSource_ok_lookups_agree source compiled success

example (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled) :
    Complexity.Production.explicitModelWellBounded compiled.ast :=
  compileModelSource_ok_wellBounded source compiled success

example (names : Array String) (index : NameIndex)
    (success : buildNameIndex names = .ok index) (name : String) (coordinate : Nat)
    (found : index.find? name = some coordinate) : coordinate < names.size :=
  buildNameIndex_ok_inBounds names index success name coordinate found

-- Arbitrary maps do not inherit the invariant of the production index builder.
private def malformedIndex : NameIndex :=
  { entries := ({} : Std.HashMap String Nat).insert "x" 99 }

example : ¬ malformedIndex.InBounds 1 := by
  intro bounded
  have impossible := bounded "x" 99 (by native_decide)
  omega

-- Source compilation accepts empty domains. Positivity belongs to finite-model
-- construction and must not be silently inferred from compiler success.
example :
    (match compileModelSource { worlds := #[], things := #[] } with
    | .error _ => false
    | .ok compiled => compiled.ast.worldCount == 0 && compiled.ast.thingCount == 0) = true := by
  native_decide

private def source : ModelSource :=
  { worlds := #["w0", "w1"]
    things := #["object", "kind"]
    facts := #[.unary .object "object" .everywhere,
      .binary .inst "object" "kind" (.at "w1")]
    productFamilies := #[⟨"object", "kind", #["object"], #["kind"]⟩] }

example :
    (match compileModelSource source with
    | .error _ => false
    | .ok compiled =>
        compiled.ast.worldCount == 2 && compiled.ast.thingCount == 2 &&
        compiled.ast.productFamilies.size == 1 &&
        compiled.tables.productFamilies.size == 1 &&
        compiled.tables.unaryLookup "object" 0 0 &&
        compiled.tables.unaryLookup "object" 0 1 &&
        compiled.tables.unaryLookup "endurant" 0 0 &&
        compiled.tables.binaryLookup "inst" 0 1 1 &&
        !compiled.tables.binaryLookup "inst" 0 1 0 &&
        compiled.tables.binaryLookup "sub" 1 1 0 &&
        compiled.tables.binaryLookup "sub" 1 1 1) = true := by
  native_decide

example :
    (match compileModelSource { source with worlds := #["w", "w"] } with
    | .error (.duplicateWorld "w") => true
    | _ => false) = true := by
  native_decide

-- All fact constructors use both scopes and the first/last source coordinates.
-- Slot 7 is valid with only two things: tuple slots have an independent size.
private def allFactSource : ModelSource :=
  { worlds := #["w0", "w1"]
    things := #["x", "y"]
    facts := #[
      .unary .object "x" .everywhere,
      .unary .object "y" (.at "w1"),
      .binary .inst "x" "y" .everywhere,
      .binary .inst "y" "x" (.at "w0"),
      .ternary .distance "x" "y" "x" .everywhere,
      .ternary .distanceSum "y" "x" "y" (.at "w1"),
      .tupleProjection "x" 7 "y" .everywhere,
      .tupleProjection "y" 0 "x" (.at "w0"),
      .derived (.unary "NonEmptySet" "x") .everywhere,
      .derived (.quaternary "relation" "x" "y" "x" "y") (.at "w1")] }

example :
    (match compileModelSource allFactSource with
    | .error _ => false
    | .ok compiled =>
        decide (Complexity.Production.explicitModelWellBounded compiled.ast) &&
        compiled.tables.ternaryLookup "distance" 0 1 0 0 &&
        compiled.tables.ternaryLookup "distance" 0 1 0 1 &&
        compiled.tables.tupleProjectionResult? 0 7 0 == some 1 &&
        compiled.tables.tupleProjectionResult? 0 7 1 == some 1) = true := by
  native_decide

-- An everywhere scope has no instances in an empty world domain. An explicit
-- world name must still resolve, even when no worlds are declared.
example :
    (match compileModelSource { allFactSource with
      worlds := #[]
      facts := #[.unary .object "x" .everywhere,
        .derived (.unary "NonEmptySet" "x") .everywhere] } with
    | .error _ => false
    | .ok compiled => compiled.ast.facts.isEmpty) = true := by
  native_decide

example :
    (match compileModelSource { allFactSource with
      worlds := #[]
      facts := #[.unary .object "x" (.at "w0")] } with
    | .error (.unknownWorld "w0") => true
    | _ => false) = true := by
  native_decide

example (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled) :
    ∀ family ∈ compiled.productFamilies, family.WellFormed source.things.size :=
  compileModelSource_ok_families_wellFormed source compiled success

example (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled) :
    compiled.tables.productFamilies = compiled.productFamilies :=
  compileModelSource_ok_tableFamilies source compiled success

example (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled)
    (hw : 0 < source.worlds.size) (ht : 0 < source.things.size) :
    ((compiled.tables.toFiniteModel4Cached source.worlds.size source.things.size hw ht
      (compileModelSource_ok_lookups_agree source compiled success)
      (compileModelSource_ok_inherenceCacheValid source compiled success)
      (compileModelSource_ok_tableDimensions source compiled success).1
      (compileModelSource_ok_tableDimensions source compiled success).2).productFamilies.map
        (fun witness => (witness.toSpec, witness.world.val))) =
      (compiled.productFamilies.toList.flatMap (fun family =>
        (List.range source.worlds.size).map (fun world => (family, world)))).toArray :=
  compileModelSource_ok_modelFamilies_readback source compiled success hw ht

example (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled)
    (hw : 0 < source.worlds.size) (ht : 0 < source.things.size)
    (x t : Fin source.things.size) (w : Fin source.worlds.size) :
    let M := compiled.tables.toFiniteModel4Cached source.worlds.size source.things.size hw ht
      (compileModelSource_ok_lookups_agree source compiled success)
      (compileModelSource_ok_inherenceCacheValid source compiled success)
      (compileModelSource_ok_tableDimensions source compiled success).1
      (compileModelSource_ok_tableDimensions source compiled success).2
    (Complexity.productFamiliesDiagnosticCosted source.worlds.size source.things.size
      compiled.tables x.val t.val w.val).value =
      (Checker.productFamilySearchCosted M x t w).value :=
  Complexity.productFamiliesDiagnosticCosted_eq_checker_of_compile
    source compiled success hw ht x t w

-- Both searches use the actual compiler result. The first family lacks its
-- required association. A later empty family is valid because these tables
-- contain no members or characterization targets.
private def familySearchOutcomes (families : Array NamedProductFamily)
    (domain qualityType : Fin 2) : Array (Bool × Bool) :=
  let source : ModelSource :=
    { worlds := #["w0", "w1"], things := #["A", "Q"], productFamilies := families }
  match success : compileModelSource source with
  | .error _ => #[]
  | .ok compiled =>
    let M := compiled.tables.toFiniteModel4Cached 2 2 (by decide) (by decide)
      (compileModelSource_ok_lookups_agree source compiled success)
      (compileModelSource_ok_inherenceCacheValid source compiled success)
      (compileModelSource_ok_tableDimensions source compiled success).1
      (compileModelSource_ok_tableDimensions source compiled success).2
    (List.finRange 2).toArray.map fun w =>
      ((Complexity.productFamiliesDiagnosticCosted 2 2 compiled.tables
        domain.val qualityType.val w.val).value,
       (Checker.productFamilySearchCosted M domain qualityType w).value)

example : familySearchOutcomes
    #[⟨"A", "Q", #["A"], #["Q"]⟩, ⟨"A", "Q", #[], #[]⟩] 0 1 =
      #[(true, true), (true, true)] := by native_decide

example : familySearchOutcomes #[⟨"A", "Q", #["A"], #["Q"]⟩] 0 1 =
    #[(false, false), (false, false)] := by native_decide

example : familySearchOutcomes #[] 0 1 =
    #[(false, false), (false, false)] := by native_decide

example : familySearchOutcomes #[⟨"A", "Q", #[], #[]⟩] 1 1 =
    #[(false, false), (false, false)] := by native_decide

example : familySearchOutcomes #[⟨"A", "Q", #[], #[]⟩] 0 0 =
    #[(false, false), (false, false)] := by native_decide

example : familySearchOutcomes
    #[⟨"A", "Q", #[], #[]⟩, ⟨"A", "Q", #[], #[]⟩] 0 1 =
      #[(true, true), (true, true)] := by native_decide

-- Name order differs from field order. Repeated slots and repeated families
-- must survive resolution, storage, and finite-model construction unchanged.
private def familySource : ModelSource :=
  { worlds := #["w0", "w1"]
    things := #["B", "A", "Q"]
    productFamilies := #[
      ⟨"A", "Q", #["B", "A", "B"], #["Q", "Q", "A"]⟩,
      ⟨"A", "Q", #["B", "A", "B"], #["Q", "Q", "A"]⟩] }

private def resolvedFamily : ProductFamilySpec := ⟨1, 2, #[0, 1, 0], #[2, 2, 1]⟩

example :
    (match compileModelSource familySource with
    | .error _ => false
    | .ok compiled =>
        decide (((compiled.tables.toFiniteModel4 2 3 (by decide) (by decide)).productFamilies.map
          (fun witness => (witness.toSpec, witness.world.val))) =
            #[(resolvedFamily, 0), (resolvedFamily, 1), (resolvedFamily, 0), (resolvedFamily, 1)])) =
      true := by
  native_decide

example :
    (match compileModelSource { familySource with worlds := #[] } with
    | .error _ => false
    | .ok compiled =>
        compiled.tables.productFamilies.size == 2 &&
        (FactTables.productFamilyWitnesses 0 3 compiled.tables.productFamilies).isEmpty) = true := by
  native_decide

example :
    (match compileModelSource { familySource with
      productFamilies := #[⟨"A", "Q", #["B"], #[]⟩] } with
    | .error (.productFamilyArityMismatch "A" "Q" 1 0) => true
    | _ => false) = true := by
  native_decide

example :
    (match compileModelSource { familySource with
      productFamilies := #[⟨"A", "Q", #["missing"], #["Q"]⟩] } with
    | .error (.unknownThing "missing") => true
    | _ => false) = true := by
  native_decide

-- These public theorems derive metrics from compiler success. Callers do not
-- supply a separate family registry or assume a fixed witness arity.
example (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled) :
    compiled.productFamilies.size = source.productFamilies.size ∧
      (compiled.productFamilies.toList.map (fun family =>
        family.dimensionThings.size + family.typeThings.size)).sum =
      (source.productFamilies.toList.map NamedProductFamily.slotCount).sum :=
  compileModelSource_ok_familySizes source compiled success

example (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled)
    (hw : 0 < source.worlds.size) (ht : 0 < source.things.size) :
    let M := compiled.tables.toFiniteModel4Cached source.worlds.size source.things.size hw ht
      (compileModelSource_ok_lookups_agree source compiled success)
      (compileModelSource_ok_inherenceCacheValid source compiled success)
      (compileModelSource_ok_tableDimensions source compiled success).1
      (compileModelSource_ok_tableDimensions source compiled success).2
    M.productFamilies.size = source.worlds.size * source.productFamilies.size ∧
      Complexity.checkerProductFamilySlots M = source.worlds.size *
        (source.productFamilies.toList.map NamedProductFamily.slotCount).sum :=
  Complexity.finiteModelFamilyMetrics_eq_sourceMetrics source compiled success hw ht

example (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled)
    (hw : 0 < source.worlds.size) (ht : 0 < source.things.size) :
    Complexity.checkerInputSize (compiled.tables.toFiniteModel4Cached
      source.worlds.size source.things.size hw ht
      (compileModelSource_ok_lookups_agree source compiled success)
      (compileModelSource_ok_inherenceCacheValid source compiled success)
      (compileModelSource_ok_tableDimensions source compiled success).1
      (compileModelSource_ok_tableDimensions source compiled success).2) ≤
      3 * (Complexity.sourceMetrics source).inputSize ^ 2 :=
  Complexity.finiteModelInputSize_le_sourceInputSize_sq source compiled success hw ht

example (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled)
    (hw : 0 < source.worlds.size) (ht : 0 < source.things.size) :
    (compiled.tables.toFiniteModel4CachedCosted source.worlds.size source.things.size hw ht
      (compileModelSource_ok_lookups_agree source compiled success)
      (compileModelSource_ok_inherenceCacheValid source compiled success)
      (compileModelSource_ok_tableDimensions source compiled success).1
      (compileModelSource_ok_tableDimensions source compiled success).2).cost ≤
      4 + source.worlds.size *
        (7 * (Complexity.sourceMetrics source).productFamilySlots +
          20 * source.productFamilies.size) + 2 * source.productFamilies.size :=
  Complexity.finiteModelConstructionCost_le_sourceMetrics source compiled success hw ht

example (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled)
    (hw : 0 < source.worlds.size) (ht : 0 < source.things.size) :
    let M := compiled.tables.toFiniteModel4Cached source.worlds.size source.things.size hw ht
      (compileModelSource_ok_lookups_agree source compiled success)
      (compileModelSource_ok_inherenceCacheValid source compiled success)
      (compileModelSource_ok_tableDimensions source compiled success).1
      (compileModelSource_ok_tableDimensions source compiled success).2
    Complexity.checkerCacheSize M = source.worlds.size +
      source.worlds.size * source.things.size ^ 2 :=
  Complexity.finiteModelCacheSize_eq_sourceMetrics source compiled success hw ht

example {W W' F F' S S' : Nat} (worlds : W ≤ W') (families : F ≤ F') (slots : S ≤ S') :
    4 + W * (7 * S + 20 * F) + 2 * F ≤
      4 + W' * (7 * S' + 20 * F') + 2 * F' :=
  Complexity.finiteModelConstruction_bound_mono worlds families slots

example (tables : FactTables) (W T : Nat) (hw : 0 < W) (ht : 0 < T)
    (agreement valid worlds things) :
    (tables.toFiniteModel4Cached W T hw ht agreement valid worlds things).productFamilies =
      (tables.toFiniteModel4Verified W T hw ht agreement).productFamilies :=
  tables.toFiniteModel4Cached_productFamilies W T hw ht agreement valid worlds things

-- Two six-slot families at two worlds produce four witnesses and 24 slots.
-- Each world/family conversion costs 61 operations. Four world iterations,
-- four outer traversal/read operations, and four setup/record operations
-- give 4 * 61 + 4 + 4 + 4 = 256, including cache installation.
example :
    (match success : compileModelSource familySource with
    | .error _ => false
    | .ok compiled =>
        let result := compiled.tables.toFiniteModel4CachedCosted 2 3 (by decide) (by decide)
          (compileModelSource_ok_lookups_agree familySource compiled success)
          (compileModelSource_ok_inherenceCacheValid familySource compiled success)
          (compileModelSource_ok_tableDimensions familySource compiled success).1
          (compileModelSource_ok_tableDimensions familySource compiled success).2
        compiled.productFamilies.size == 2 &&
        (Complexity.sourceMetrics familySource).productFamilySlots == 12 &&
        result.value.productFamilies.size == 4 &&
        Complexity.checkerProductFamilySlots result.value == 24 &&
        Complexity.checkerCacheSize result.value == 20 &&
        result.cost == 256) = true := by
  native_decide

example :
    (match success : compileModelSource { familySource with productFamilies := #[] } with
    | .error _ => false
    | .ok compiled =>
        let result := compiled.tables.toFiniteModel4CachedCosted 2 3 (by decide) (by decide)
          (compileModelSource_ok_lookups_agree _ compiled success)
          (compileModelSource_ok_inherenceCacheValid _ compiled success)
          (compileModelSource_ok_tableDimensions _ compiled success).1
          (compileModelSource_ok_tableDimensions _ compiled success).2
        result.value.productFamilies.isEmpty &&
        Complexity.checkerProductFamilySlots result.value == 0 &&
        Complexity.checkerCacheSize result.value == 20 && result.cost == 4) = true := by
  native_decide

-- Checker-side closure construction counts each world's matrix execution.
-- These raw-model tests check the source counter's eleven-unit edge interface.
-- The query module separately connects it to verified dense model construction.
example :
    let M := ({} : FactTables).toFiniteModel4 1 1 (by decide) (by decide)
    (Checker.inherenceMatricesCosted M).cost = 16 := by native_decide

example :
    let M := ({} : FactTables).toFiniteModel4 1 2 (by decide) (by decide)
    (Checker.inherenceMatricesCosted M).cost = 110 ∧
      (Checker.checkAx68Costed M).cost = 139 := by native_decide

example :
    let M := ({} : FactTables).toFiniteModel4 2 2 (by decide) (by decide)
    (Checker.inherenceMatricesCosted M).cost = 220 := by native_decide

example :
    let tables := compileExplicitModelAST
      { worldCount := 1, thingCount := 2,
        facts := #[.binary .inheresIn 0 1 0, .binary .inheresIn 1 0 0] }
    let M := tables.toFiniteModel4 1 2 (by decide) (by decide)
    (Checker.inherenceMatricesCosted M).cost = 94 ∧
      (Checker.checkAx68Costed M).cost = 123 ∧
      ((Checker.inherenceMatricesCosted M).value[0].get (0 : Fin 2) (1 : Fin 2)) = true := by native_decide

example (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled) :
    compiled.tables.InherenceCacheValid :=
  compileModelSource_ok_inherenceCacheValid source compiled success

example (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled)
    (hw : 0 < source.worlds.size) (ht : 0 < source.things.size)
    (start target : Fin source.things.size) (world : Fin source.worlds.size) :
    let M := compiled.tables.toFiniteModel4Cached source.worlds.size source.things.size hw ht
      (compileModelSource_ok_lookups_agree source compiled success)
      (compileModelSource_ok_inherenceCacheValid source compiled success)
      (compileModelSource_ok_tableDimensions source compiled success).1
      (compileModelSource_ok_tableDimensions source compiled success).2
    (compiled.tables.inherenceClosureTableCosted start target world).value =
      Complexity.reachableVia (fun x y => M.inheresIn x y world)
        (List.finRange source.things.size) start target := by
  rw [FactTables.inherenceClosureTableCosted_value]
  exact compileModelSource_ok_modelClosure_lookup source compiled success hw ht start target world

private def cacheAst : ModelAST :=
  { worldCount := 2, thingCount := 2, facts := #[.binary .inheresIn 0 1 0] }

private def cachedTables : FactTables := compileExplicitModelAST cacheAst

-- The nested checker representation reads world, row, and cell, including
-- for a false answer. These tests distinguish worlds and edge directions.
example :
    let M := cachedTables.toFiniteModel4 2 2 (by decide) (by decide)
    let closures := Checker.inherenceMatrices M
    Checker.reachableInheresInWarshallCosted M closures
        (0 : Fin 2) (1 : Fin 2) (0 : Fin 2) = ⟨true, 3⟩ ∧
      Checker.reachableInheresInWarshallCosted M closures
        (1 : Fin 2) (0 : Fin 2) (0 : Fin 2) = ⟨false, 3⟩ ∧
      Checker.reachableInheresInWarshallCosted M closures
        (0 : Fin 2) (1 : Fin 2) (1 : Fin 2) = ⟨false, 3⟩ := by
  native_decide

example (M : FiniteModel4) (closures)
    (m b : Fin M.thingCount) (w : Fin M.worldCount) :
    (Checker.reachableInheresInWarshallCosted M closures m b w).value =
        Checker.reachableInheresInWarshallB M closures m b w ∧
      (Checker.reachableInheresInWarshallCosted M closures m b w).cost = 3 :=
  ⟨Checker.reachableInheresInWarshallCosted_value M closures m b w,
    Checker.reachableInheresInWarshallCosted_cost M closures m b w⟩

-- The eight-unit moment read, negation, branch, and three closure reads cost
-- thirteen. A true moment test stops at ten, without any closure read.
example :
    let M := cachedTables.toFiniteModel4 2 2 (by decide) (by decide)
    let closures := Checker.inherenceMatrices M
    Checker.ultimateBearerOfCosted M (Checker.reachableInheresInWarshallCosted M closures)
        (1 : Fin 2) (0 : Fin 2) (0 : Fin 2) = ⟨true, 13⟩ ∧
      Checker.ultimateBearerOfCosted M (Checker.reachableInheresInWarshallCosted M closures)
        (1 : Fin 2) (0 : Fin 2) (1 : Fin 2) = ⟨false, 13⟩ ∧
      Checker.ultimateBearerOfCosted { M with moment := fun _ _ => true }
        (Checker.reachableInheresInWarshallCosted M closures)
        (1 : Fin 2) (0 : Fin 2) (0 : Fin 2) = ⟨false, 10⟩ := by native_decide

-- One moment inheres in its only non-moment bearer. Candidate selection must
-- include the reads from both witness discovery and uniqueness checking.
-- Four thing/world pairs add 4 * 12 operations for the moment query, negation,
-- implication branch, and world loop. The thing loop adds four more: 61 + 52.
example :
    let M := cachedTables.toFiniteModel4 2 2 (by decide) (by decide)
    let M := { M with moment := fun x w => x.val == 0 && w.val == 0 }
    let closures := Checker.inherenceMatrices M
    Checker.existsUniqueUltimateBearerCosted M (Checker.reachableInheresInWarshallCosted M closures)
        (0 : Fin 2) (0 : Fin 2) = ⟨true, 61⟩ ∧
      (Checker.inherenceMatricesCosted M).cost = 212 ∧
      Checker.checkAx68WithReachabilityCosted M
        (Checker.reachableInheresInWarshallCosted M closures) = ⟨true, 113⟩ ∧
      Checker.checkAx68Costed M = ⟨true, 326⟩ := by
  native_decide

example : cachedTables.InherenceCacheValid := compileExplicitModelAST_inherenceCacheValid cacheAst

private def cachedModel : FiniteModel4 :=
  compileVerifiedModel cacheAst (by decide) (by decide) (by decide)

-- Generated models retain the compiler's arrays. A cache with two world
-- slots and eight cells contributes ten units to the explicit checker size.
example : cachedModel.inherenceCache.map Subtype.val = some cachedTables.inherenceClosures ∧
    Complexity.checkerCacheSize cachedModel = 10 ∧
    Checker.checkAx68Costed cachedModel = ⟨true, 53⟩ := by native_decide

-- Direct flat queries cost six each. The bearer search evaluates two of
-- them, so it adds six operations compared with nested queries, but avoids
-- all 212 closure-construction operations. Cache selection adds one.
example :
    let M := { cachedModel with moment := fun x w => x.val == 0 && w.val == 0 }
    Checker.checkAx68Costed M = ⟨true, 120⟩ ∧
      Checker.checkAx68 M = Checker.checkAx68Warshall M := by native_decide

example :
    (cachedTables.toFiniteModel4CachedCosted 2 2 (by decide) (by decide)
      (compiledLookups_agree cacheAst (by decide))
      (compileExplicitModelAST_inherenceCacheValid cacheAst)
      (compileExplicitModelAST_tableDimensions cacheAst).1
      (compileExplicitModelAST_tableDimensions cacheAst).2).cost = 4 := by native_decide

example (M : FiniteModel4) (cache) (cached : M.inherenceCache = some cache) :
    (Checker.checkAx68Costed M).cost ≤ Checker.checkAx68EvaluationBound M 6 + 1 :=
  Checker.checkAx68Costed_cost_le_of_cached M cache cached

-- The edge belongs only to world zero. Rows and deterministic hops must not
-- be exchanged when the per-world results are appended to the cache.
example : cachedTables.inherenceClosures =
    #[#[true, true, false, true], #[true, false, false, true]] ∧
    cachedTables.inherenceNextHops =
    #[#[some 0, some 1, none, some 1], #[some 0, none, none, some 1]] := by native_decide

private def swappedCache : FactTables :=
  { cachedTables with inherenceClosures :=
    #[#[true, false, false, true], #[true, true, false, true]] }

-- Primitive lookup agreement survives this forgery and therefore cannot
-- serve as the cache-validity proof.
example : swappedCache.sparseLookups 2 2 = swappedCache.denseLookups 2 2 := by
  have unchanged (tables : FactTables) (rows : Array (Array Bool)) :
      ({ tables with inherenceClosures := rows }).sparseLookups 2 2 =
          tables.sparseLookups 2 2 ∧
      ({ tables with inherenceClosures := rows }).denseLookups 2 2 =
          tables.denseLookups 2 2 := ⟨rfl, rfl⟩
  unfold swappedCache
  rw [(unchanged cachedTables _).1, (unchanged cachedTables _).2]
  exact compiledLookups_agree cacheAst (by decide)

example : ¬ swappedCache.InherenceCacheValid := by
  intro valid
  have row := valid.reachableAt swappedCache ⟨0, by native_decide⟩
  have wrong : swappedCache.inherenceClosures[0]? ≠ some
      (Complexity.warshallState swappedCache.denseThingCount
        (swappedCache.inherenceEdgeAt 0)).reachable.flatten.toArray := by native_decide
  exact wrong row

-- Correct reachability alone cannot justify arbitrary first-hop evidence.
private def wrongHops : FactTables :=
  { cachedTables with inherenceNextHops := #[#[none, none, none, none], #[]] }

example : ¬ wrongHops.InherenceCacheValid := by
  intro valid
  have row := valid.nextHopAt wrongHops ⟨0, by native_decide⟩
  have wrong : wrongHops.inherenceNextHops[0]? ≠ some
      ((Complexity.warshallState wrongHops.denseThingCount
        (wrongHops.inherenceEdgeAt 0)).nextHop.flatten.toArray.map (Option.map Fin.val)) := by
    native_decide
  exact wrong row

-- Materialization discards even a malformed incoming cache and proves the
-- replacement against the resulting dense graph.
example : (wrongHops.withDenseFacts 2 2 cacheAst.facts).InherenceCacheValid :=
  FactTables.withDenseFacts_inherenceCacheValid _ _ _ _

example : (compileExplicitModelAST { worldCount := 0, thingCount := 0 }).InherenceCacheValid :=
  compileExplicitModelAST_inherenceCacheValid _

/-! ## Source-linked component bounds

No independent model argument appears in these applications. The counted
constructor consumes the successful compiler's returned tables and proofs.
-/

example (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled)
    (hw : 0 < source.worlds.size) (ht : 0 < source.things.size) :
    let construction := compiled.tables.toFiniteModel4CachedCosted
      source.worlds.size source.things.size hw ht
      (compileModelSource_ok_lookups_agree source compiled success)
      (compileModelSource_ok_inherenceCacheValid source compiled success)
      (compileModelSource_ok_tableDimensions source compiled success).1
      (compileModelSource_ok_tableDimensions source compiled success).2
    construction.cost ≤ 26 * (Complexity.sourceMetrics source).inputSize ^ 2 :=
  Complexity.finiteModelConstructionCost_le_sourceInputSize_sq source compiled success hw ht

example (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled)
    (hw : 0 < source.worlds.size) (ht : 0 < source.things.size) :
    let construction := compiled.tables.toFiniteModel4CachedCosted
      source.worlds.size source.things.size hw ht
      (compileModelSource_ok_lookups_agree source compiled success)
      (compileModelSource_ok_inherenceCacheValid source compiled success)
      (compileModelSource_ok_tableDimensions source compiled success).1
      (compileModelSource_ok_tableDimensions source compiled success).2
    let m := Complexity.sourceMetrics source
    Complexity.compilerOperationalCost source + construction.cost +
      (Checker.checkAxioms4Costed construction.value).cost ≤
      Complexity.sourceCompilerPolynomial m +
        (4 + m.worlds * (7 * m.productFamilySlots + 20 * m.productFamilies) +
          2 * m.productFamilies) + 8367 * (3 * m.inputSize ^ 2) ^ 8 :=
  Complexity.source_linked_component_bound source compiled success hw ht

example (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled)
    (hw : 0 < source.worlds.size) (ht : 0 < source.things.size) :
    let construction := compiled.tables.toFiniteModel4CachedCosted
      source.worlds.size source.things.size hw ht
      (compileModelSource_ok_lookups_agree source compiled success)
      (compileModelSource_ok_inherenceCacheValid source compiled success)
      (compileModelSource_ok_tableDimensions source compiled success).1
      (compileModelSource_ok_tableDimensions source compiled success).2
    Complexity.compilerOperationalCost source + construction.cost +
      (Checker.checkAxioms4Costed construction.value).cost ≤
      54896424 * (Complexity.sourceMetrics source).inputSize ^ 16 :=
  Complexity.source_linked_component_scalar_bound source compiled success hw ht

-- This test driver evaluates the source compiler once, then constructs and
-- checks its returned model. Its domain guards enforce the theorem's premises.
-- Diagnostic sizes come from the returned tables, including duplicate
-- assertions and world expansion. These checks allow empty domains, unlike
-- the finite-model construction tests below.
example (ast : ModelAST) :
    (compileExplicitModelAST ast).derivedProps.size ≤ ast.facts.size :=
  compileExplicitModelAST_derivedProps_size_le ast

example (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled) :
    compiled.ast.facts.size ≤ (Complexity.sourceMetrics source).specializationFactsUpper :=
  Complexity.compiledFactCount_le_sourceMetrics source compiled success

example (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled) :
    compiled.tables.derivedProps.size ≤ (Complexity.sourceMetrics source).specializationFactsUpper :=
  Complexity.compiledDerivedPropCount_le_sourceMetrics source compiled success

example (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled) :
    (derivedAssertionFailureCosted (source.worlds.map Lean.Name.mkSimple)
      (source.things.map Lean.Name.mkSimple) source.facts compiled.scopedFacts compiled.tables).cost ≤
      5608 * (Complexity.sourceMetrics source).inputSize ^ 5 :=
  Complexity.source_derivedAssertionFailure_cost_bound source compiled success

example (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled) :
    (derivedAssertionAnalysisCosted (source.worlds.map Lean.Name.mkSimple)
      (source.things.map Lean.Name.mkSimple) source.facts compiled.scopedFacts compiled.tables).cost ≤
      5612 * (Complexity.sourceMetrics source).inputSize ^ 5 :=
  Complexity.source_derivedAssertionAnalysis_cost_bound source compiled success

example : (compileExplicitModelAST
    { worldCount := 0, thingCount := 0, facts := #[.derived "same", .derived "same"] }).derivedProps =
      #["same", "same"] := by native_decide

private def repeatedDerivedSource : ModelSource :=
  { worlds := #["w0", "w1"]
    things := #["x", "y"]
    facts := #[.derived (.unary "NonEmptySet" "x") .everywhere,
      .derived (.unary "NonEmptySet" "x") .everywhere]
    productFamilies := #[⟨"x", "y", #["x"], #["y"]⟩] }

example : (match compileModelSource repeatedDerivedSource with
    | .error _ => false
    | .ok compiled => compiled.tables.derivedProps.size == 4 &&
        compiled.tables.productFamilies.size == 1) = true := by native_decide

-- Name conversion preserves strings as one component: it does not parse a
-- dot as a namespace separator or discard empty strings and duplicates.
example : namesFromStringsCosted #[] = ⟨#[], 1⟩ := by decide
example : (namesFromStringsCosted #["x"]).cost = 5 := by decide
example : (namesFromStringsCosted #["x", "y", "x"]).cost = 13 := by decide
example : namesFromStrings #["a.b", "", "α", "a.b"] =
    #[Lean.Name.str .anonymous "a.b", Lean.Name.str .anonymous "",
      Lean.Name.str .anonymous "α", Lean.Name.str .anonymous "a.b"] := by decide
example : namesFromStrings #["a.b"] ≠
    #[Lean.Name.str (Lean.Name.str .anonymous "a") "b"] := by decide

example (names : Array String) :
    (namesFromStringsCosted names).value = names.map Lean.Name.mkSimple :=
  namesFromStringsCosted_value names
example (xs ys : Array String) (larger : xs.size ≤ ys.size) :
    (namesFromStringsCosted xs).cost ≤ (namesFromStringsCosted ys).cost := by
  simp only [namesFromStringsCosted_cost]
  omega

-- This checks the original traversal size, including the forward cost
-- accumulator, without turning the scan into a recursive callback chain.
example : (namesFromStringsCosted (Array.replicate 100000 "x")).cost = 400001 :=
  by native_decide
example : (namesFromStrings (Array.replicate 100000 "x")).size = 100000 :=
  by native_decide

example (source : ModelSource) :
    (namesFromStringsCosted source.worlds).cost +
      (namesFromStringsCosted source.things).cost ≤ 6 * (Complexity.sourceMetrics source).inputSize :=
  Complexity.sourceNameConversion_cost_bound source

example (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled) :
    Complexity.compilerOperationalCost source +
      (namesFromStringsCosted source.worlds).cost +
      (namesFromStringsCosted source.things).cost +
      (derivedAssertionAnalysisCosted (namesFromStrings source.worlds)
        (namesFromStrings source.things) source.facts compiled.scopedFacts compiled.tables).cost ≤
      6129 * (Complexity.sourceMetrics source).inputSize ^ 5 :=
  Complexity.source_derivedAssertion_component_bound source compiled success

private def diagnosticBoundHolds (source : ModelSource) : Bool :=
  let compilation := compileModelSourceCosted source
  match compilation.value with
  | .error _ => false
  | .ok compiled =>
      let worlds := namesFromStringsCosted source.worlds
      let things := namesFromStringsCosted source.things
      let precheck := derivedAssertionFailureCosted worlds.value things.value source.facts
        compiled.scopedFacts compiled.tables
      let report := derivedAssertionFailureReportCosted precheck.value
      let n := (Complexity.sourceMetrics source).inputSize
      decide (precheck.cost ≤ 5608 * n ^ 5) &&
        decide (precheck.cost + report.cost ≤ 5612 * n ^ 5) &&
        decide (compilation.cost + worlds.cost + things.cost + precheck.cost + report.cost ≤
          6129 * n ^ 5)

example : diagnosticBoundHolds repeatedDerivedSource = true := by native_decide
example : diagnosticBoundHolds allFactSource = true := by native_decide
example : diagnosticBoundHolds { repeatedDerivedSource with worlds := #[] } = true :=
  by native_decide
example : diagnosticBoundHolds { worlds := #[], things := #[] } = true := by native_decide
example : diagnosticBoundHolds { repeatedDerivedSource with worlds := #["w", "w"] } = false :=
  by native_decide

private def componentBoundHolds (source : ModelSource) : Bool :=
  let compilation := compileModelSourceCosted source
  match success : compilation.value with
  | .error _ => false
  | .ok compiled =>
    if hw : 0 < source.worlds.size then
      if ht : 0 < source.things.size then
        let construction := compiled.tables.toFiniteModel4CachedCosted
          source.worlds.size source.things.size hw ht
          (compileModelSource_ok_lookups_agree source compiled success)
          (compileModelSource_ok_inherenceCacheValid source compiled success)
          (compileModelSource_ok_tableDimensions source compiled success).1
          (compileModelSource_ok_tableDimensions source compiled success).2
        let checked := Checker.checkAxioms4Costed construction.value
        let rebuilt := compileExplicitModelASTCosted compiled.ast
        let invariant := compileModelSource_ok_constructionInvariant source compiled success
        let reconstruction := compileVerifiedModelCosted compiled.ast
          (by simpa only [invariant.worldCount] using hw)
          (by simpa only [invariant.thingCount] using ht)
          (compileModelSource_ok_wellBounded source compiled success)
        let sourcePower := (Complexity.sourceMetrics source).inputSize ^ 16
        decide (compilation.cost + construction.cost + checked.cost ≤
          54896424 * sourcePower) &&
          decide (rebuilt.cost ≤ compilation.cost) &&
          decide (reconstruction.cost = rebuilt.cost + construction.cost) &&
          decide (reconstruction.cost ≤ 537 * (Complexity.sourceMetrics source).inputSize ^ 4) &&
          (Checker.checkAxioms4BoundedRegistry construction.value).all
            (fun entry => decide ((entry.run ()).cost ≤ 54895887 * sourcePower) &&
              decide (rebuilt.cost + construction.cost + (entry.run ()).cost ≤
                54896424 * sourcePower))
      else false
    else false

example : componentBoundHolds source = true := by native_decide
example : componentBoundHolds familySource = true := by native_decide
example : componentBoundHolds { worlds := #[], things := #[] } = false := by native_decide
example : componentBoundHolds { source with worlds := #["w0", "w0"] } = false := by native_decide

example (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled) :
    (compileExplicitModelASTCosted compiled.ast).cost ≤
      Complexity.compilerOperationalCost source :=
  Complexity.explicitCompilation_cost_le_source source compiled success

example (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled) :
    (compileExplicitModelASTCosted compiled.ast).cost ≤
      511 * (Complexity.sourceMetrics source).inputSize ^ 4 :=
  Complexity.explicitCompilation_source_scalar_bound source compiled success

-- The precheck's domain-size bound also covers rejected and empty sources:
-- no compiler-success premise or unrelated finite model is supplied.
example (source : ModelSource) (tables : FactTables) (field : String) :
    (certificationFieldPrecheckCosted source.worlds.size source.things.size tables field).cost ≤
      124 * (Complexity.sourceMetrics source).inputSize ^ 4 :=
  Complexity.source_field_precheck_scalar_bound source tables field

example (ast : ModelAST) (hw : 0 < ast.worldCount) (ht : 0 < ast.thingCount)
    (bounded : Complexity.Production.explicitModelWellBounded ast) :
    (compileVerifiedModelCosted ast hw ht bounded).value =
      compileVerifiedModel ast hw ht bounded :=
  compileVerifiedModelCosted_value ast hw ht bounded

-- The prerequisite used by the axiom-73 proof is a concrete registered
-- computation. The witness identifies its full counted result, not just true.
example (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled)
    (hw : 0 < compiled.ast.worldCount) (ht : 0 < compiled.ast.thingCount) :
    (Complexity.reconstructedCheckCosted compiled.ast hw ht
      (compileModelSource_ok_wellBounded source compiled success) Checker.checkAx75Costed).cost ≤
      54896424 * (Complexity.sourceMetrics source).inputSize ^ 16 := by
  let M := compileVerifiedModel compiled.ast hw ht
    (compileModelSource_ok_wellBounded source compiled success)
  apply Complexity.reconstructedCheck_source_bound source compiled success hw ht
    Checker.checkAx75Costed
  refine ⟨.of (fun _ => Checker.checkAx75Costed M) (Checker.checkAx75Costed_cost_le M), ?_, rfl⟩
  simp [M, Checker.checkAxioms4BoundedRegistry]

example (ast : ModelAST) (hw : 0 < ast.worldCount) (ht : 0 < ast.thingCount)
    (bounded : Complexity.Production.explicitModelWellBounded ast)
    (parent : Unit → Complexity.Costed Bool) :
    (Complexity.nativeRequestCosted (.expect "ax75" true)
      (fun _ => Complexity.reconstructedCheckCosted ast hw ht bounded Checker.checkAx75Costed)
      parent).value =
      CertificateChecking.resultsAgree (Checker.checkAx75 (compileVerifiedModel ast hw ht bounded))
        true := by
  rw [Complexity.nativeRequest_erasure]
  simp only [Complexity.reconstructedCheck_erasure, Checker.checkAx75]

-- Distinct ASTs prevent the reuse test from proving only self-comparison.
-- Both operands include their own construction before the Boolean comparison.
example (child parent : ModelAST)
    (cw : 0 < child.worldCount) (ct : 0 < child.thingCount)
    (pw : 0 < parent.worldCount) (pt : 0 < parent.thingCount)
    (childBounded : Complexity.Production.explicitModelWellBounded child)
    (parentBounded : Complexity.Production.explicitModelWellBounded parent) :
    (Complexity.nativeRequestCosted (.agree "ax75" `Parent)
      (fun _ => Complexity.reconstructedCheckCosted child cw ct childBounded Checker.checkAx75Costed)
      (fun _ => Complexity.reconstructedCheckCosted parent pw pt parentBounded Checker.checkAx75Costed)).value =
      CertificateChecking.resultsAgree
        (Checker.checkAx75 (compileVerifiedModel child cw ct childBounded))
        (Checker.checkAx75 (compileVerifiedModel parent pw pt parentBounded)) := by
  rw [Complexity.nativeRequest_erasure]
  simp only [Complexity.reconstructedCheck_erasure, Checker.checkAx75]

example (child parent : ModelAST)
    (cw : 0 < child.worldCount) (ct : 0 < child.thingCount)
    (pw : 0 < parent.worldCount) (pt : 0 < parent.thingCount)
    (childBounded : Complexity.Production.explicitModelWellBounded child)
    (parentBounded : Complexity.Production.explicitModelWellBounded parent) :
    (Complexity.nativeRequestCosted (.agree "ax75" `Parent)
      (fun _ => Complexity.reconstructedCheckCosted child cw ct childBounded Checker.checkAx75Costed)
      (fun _ => Complexity.reconstructedCheckCosted parent pw pt parentBounded Checker.checkAx75Costed)).cost =
      (compileVerifiedModelCosted child cw ct childBounded).cost +
        (Checker.checkAx75Costed (compileVerifiedModel child cw ct childBounded)).cost +
        ((compileVerifiedModelCosted parent pw pt parentBounded).cost +
          (Checker.checkAx75Costed (compileVerifiedModel parent pw pt parentBounded)).cost) + 1 := by
  rw [Complexity.nativeRequest_cost]
  simp only [Complexity.reconstructedCheck_cost]

-- Instantiate the prefix bound with an actual generated checked script.
-- Both fresh and reused forms resolve to axiom 75, whose registry membership
-- is proved below. The same source can serve as the child's reuse parent.
example (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled)
    (hw : 0 < compiled.ast.worldCount) (ht : 0 < compiled.ast.thingCount)
    (reuse : Option Lean.Name) (limit : Nat) :
    let script := checkedAxiomProofScript ⟨"ax75", "True"⟩ reuse
    let operand := fun _ : Unit => Complexity.reconstructedCheckCosted compiled.ast hw ht
      (compileModelSource_ok_wellBounded source compiled success) Checker.checkAx75Costed
    ((script.nativeCalls.take limit).map (fun request =>
      (Complexity.nativeRequestCosted request operand operand).cost)).sum ≤
      (if reuse.isSome then 2 else 1) *
        (54896424 * (Complexity.sourceMetrics source).inputSize ^ 16) + 1 := by
  let M := compileVerifiedModel compiled.ast hw ht
    (compileModelSource_ok_wellBounded source compiled success)
  have registered : ∃ entry : Complexity.BoundedCheck,
      entry ∈ (Checker.checkAxioms4BoundedRegistry M).toList ∧
        Checker.checkAx75Costed M = entry.run () := by
    refine ⟨.of (fun _ => Checker.checkAx75Costed M) (Checker.checkAx75Costed_cost_le M), ?_, rfl⟩
    simp [Checker.checkAxioms4BoundedRegistry]
  have bound := Complexity.nativeScript_prefix_source_bound source source compiled compiled
    success success hw ht hw ht (checkedAxiomProofScript ⟨"ax75", "True"⟩ reuse) limit
    (fun _ => Checker.checkAx75Costed) (fun _ _ => registered)
    (by
      intro request _
      cases request with
      | expect field answer => trivial
      | agree field name => exact registered)
  simpa only [Nat.max_self, Complexity.checkedScript_checkerCalls,
    Complexity.checkedScript_nativeCalls, List.length_singleton] using bound

-- This is the script supplied to the production executor, with its concrete
-- reconstruction/check operands. Arbitrary excluded proof errors may stop
-- preparation, but cannot increase the source-derived algorithm bound.
example (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled)
    (hw : 0 < compiled.ast.worldCount) (ht : 0 < compiled.ast.thingCount)
    (reuse : Option Lean.Name)
    (proofResult : CertificateChecking.NativeCall → Bool → Except Unit String) :
    let script := (checkedAxiomProofCheck ⟨"ax75", "True"⟩ reuse).script
    let operand := fun _ : Unit => Complexity.reconstructedCheckCosted compiled.ast hw ht
      (compileModelSource_ok_wellBounded source compiled success) Checker.checkAx75Costed
    (script.prepareCosted (fun request => Complexity.Costed.map (proofResult request)
      (Complexity.nativeRequestCosted request operand operand))).cost ≤
      (if reuse.isSome then 2 else 1) *
        (54896424 * (Complexity.sourceMetrics source).inputSize ^ 16) + 5 := by
  let M := compileVerifiedModel compiled.ast hw ht
    (compileModelSource_ok_wellBounded source compiled success)
  have registered : ∃ entry : Complexity.BoundedCheck,
      entry ∈ (Checker.checkAxioms4BoundedRegistry M).toList ∧
        Checker.checkAx75Costed M = entry.run () := by
    refine ⟨.of (fun _ => Checker.checkAx75Costed M) (Checker.checkAx75Costed_cost_le M), ?_, rfl⟩
    simp [Checker.checkAxioms4BoundedRegistry]
  have bound := Complexity.nativeScript_prepare_source_bound source source compiled compiled
    success success hw ht hw ht (checkedAxiomProofScript ⟨"ax75", "True"⟩ reuse)
    (fun _ => Checker.checkAx75Costed) proofResult (fun _ _ => registered)
    (by
      intro request _
      cases request with
      | expect field answer => trivial
      | agree field name => exact registered)
  simpa only [checkedAxiomProofCheck, Nat.max_self, Complexity.checkedScript_checkerCalls,
    Complexity.checkedScript_nativeCalls, List.length_singleton] using bound

-- Instantiate the complete checked-attempt bound with a real registry entry
-- on independently supplied child and parent sources, not a synthetic budget.
example (childSource parentSource : ModelSource) (child parent : CompiledModelSource)
    (childSuccess : compileModelSource childSource = .ok child)
    (parentSuccess : compileModelSource parentSource = .ok parent)
    (cw : 0 < child.ast.worldCount) (ct : 0 < child.ast.thingCount)
    (pw : 0 < parent.ast.worldCount) (pt : 0 < parent.ast.thingCount)
    (fresh : Bool)
    (proofResult : Bool → Option Lean.Name → CertificateChecking.NativeCall → Bool → Except Unit String)
    (proofFailed : Bool → Option Lean.Name → Bool) :
    let plan := fun _ : Unit => certificateReuseSourceCosted `Parent parentSource
      childSource parent.tables child.tables fresh "ax75"
    let native := fun declaration reuse request => Complexity.Costed.map
      (proofResult declaration reuse request) (Complexity.nativeRequestCosted request
        (fun _ => Complexity.reconstructedCheckCosted child.ast cw ct
          (compileModelSource_ok_wellBounded childSource child childSuccess) Checker.checkAx75Costed)
        (fun _ => Complexity.reconstructedCheckCosted parent.ast pw pt
          (compileModelSource_ok_wellBounded parentSource parent parentSuccess) Checker.checkAx75Costed))
    (Complexity.preparedCheckedAttemptsCosted ⟨"ax75", "True"⟩ plan native proofFailed).cost ≤
      18 * (Complexity.sourceMetrics childSource).inputSize +
        11023 * (Complexity.sourceMetrics parentSource).inputSize +
        6 * (54896424 * (max (Complexity.sourceMetrics childSource).inputSize
          (Complexity.sourceMetrics parentSource).inputSize) ^ 16) + 25 := by
  have registered (M : FiniteModel4) : ∃ entry : Complexity.BoundedCheck,
      entry ∈ (Checker.checkAxioms4BoundedRegistry M).toList ∧
        Checker.checkAx75Costed M = entry.run () := by
    refine ⟨.of (fun _ => Checker.checkAx75Costed M) (Checker.checkAx75Costed_cost_le M), ?_, rfl⟩
    simp [Checker.checkAxioms4BoundedRegistry]
  exact Complexity.source_prepared_checked_bound childSource parentSource child parent
    childSuccess parentSuccess cw ct pw pt `Parent fresh ⟨"ax75", "True"⟩
    Checker.checkAx75Costed proofResult proofFailed (registered _) (registered _)

-- Axiom 73's semantic proof checks its future axiom-75 prerequisite. Both
-- trial and declaration use this source-derived bound, even if proof work fails.
example (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled)
    (hw : 0 < compiled.ast.worldCount) (ht : 0 < compiled.ast.thingCount)
    (declaration proofFailed : Bool)
    (proofResult : CertificateChecking.NativeCall → Bool → Except Unit String) :
    let proofSource := if declaration then
      certAxiomTheorem compiled.ast.worldCount compiled.ast.thingCount compiled.tables ⟨"ax73", "True"⟩
      else certAxiomProofCheck compiled.ast.worldCount compiled.ast.thingCount compiled.tables ⟨"ax73", "True"⟩
    let operand := fun _ : Unit => Complexity.reconstructedCheckCosted compiled.ast hw ht
      (compileModelSource_ok_wellBounded source compiled success) Checker.checkAx75Costed
    (Complexity.preparedProofAttemptCosted proofSource
      (fun request => Complexity.Costed.map (proofResult request)
        (Complexity.nativeRequestCosted request operand operand)) proofFailed).cost ≤
      54896424 * (Complexity.sourceMetrics source).inputSize ^ 16 + 5 := by
  apply Complexity.source_prepared_semantic_bound source compiled success hw ht
    ⟨"ax73", "True"⟩ declaration (fun _ => Checker.checkAx75Costed) proofResult proofFailed
  intro request _
  refine ⟨.of (fun _ => Checker.checkAx75Costed _)
    (Checker.checkAx75Costed_cost_le _), ?_, rfl⟩
  simp [Checker.checkAxioms4BoundedRegistry]

private def counterexample73Check (request : CertificateChecking.NativeCall)
    (M : FiniteModel4) : Complexity.Costed Bool :=
  let field := match request with | .expect field _ => field | .agree field _ => field
  if field == "ax75" then Checker.checkAx75Costed M else Checker.checkAx73Costed M

-- The counterexample script checks axiom 75 first, then axiom 73. The bound
-- permits either native proof production or later proof work to fail.
example (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled)
    (hw : 0 < compiled.ast.worldCount) (ht : 0 < compiled.ast.thingCount)
    (proofFailed : Bool)
    (proofResult : CertificateChecking.NativeCall → Bool → Except Unit String) :
    let operand := fun request (_ : Unit) => Complexity.reconstructedCheckCosted compiled.ast hw ht
      (compileModelSource_ok_wellBounded source compiled success) (counterexample73Check request)
    (Complexity.preparedProofAttemptCosted (certAxiomCounterexampleCheck ⟨"ax73", "True"⟩)
      (fun request => Complexity.Costed.map (proofResult request)
        (Complexity.nativeRequestCosted request (operand request) (operand request))) proofFailed).cost ≤
      2 * (54896424 * (Complexity.sourceMetrics source).inputSize ^ 16) + 9 := by
  apply Complexity.source_prepared_counterexample_bound source compiled success hw ht
    ⟨"ax73", "True"⟩ counterexample73Check proofResult proofFailed
  intro request _
  cases request <;> dsimp only [counterexample73Check]
  all_goals
    split
    · refine ⟨.of (fun _ => Checker.checkAx75Costed _)
        (Checker.checkAx75Costed_cost_le _), ?_, rfl⟩
      simp [Checker.checkAxioms4BoundedRegistry]
    · refine ⟨.of (fun _ => Checker.checkAx73Costed _)
        (Checker.checkAx73Costed_cost_le _), ?_, rfl⟩
      simp [Checker.checkAxioms4BoundedRegistry]

end LeanUfo.Test.Complexity.SourceCorrespondence
