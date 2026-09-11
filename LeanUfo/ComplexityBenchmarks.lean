import LeanUfo.UFO.UFO

/-!
# Reproducible complexity scaling benchmarks

These generated families complement the proved unit-cost bounds with wall-clock
observations. They are deliberately not proof evidence: elapsed time depends
on Lean's native runtime, allocation, and the host machine. This separation
follows the implementation/machine-model discipline illustrated by Forster et
al. The generated families also follow the executable-test methodology used by
RadixExperiment.
-/

namespace LeanUfo.ComplexityBenchmarks

open LeanUfo.UFO.DSL

inductive Family where
  | sparse | dense | cyclic | product | projection
deriving Repr

def Family.name : Family → String
  | .sparse => "sparse"
  | .dense => "dense"
  | .cyclic => "cyclic"
  | .product => "product"
  | .projection => "projection"

private def sparseFacts (n : Nat) : Array CompiledFact :=
  (Array.range n).map fun i => .unary .endurant i 0

private def denseFacts (n : Nat) : Array CompiledFact := Id.run do
  let mut facts := #[]
  for i in [:n] do
    for j in [:n] do
      facts := facts.push (.binary .part i j 0)
  return facts

private def cyclicFacts (n : Nat) : Array CompiledFact :=
  (Array.range n).map fun i => .binary .inheresIn i ((i + 1) % n) 0

private def projectionFacts (n : Nat) : Array CompiledFact := Id.run do
  let mut facts := #[]
  for tuple in [:n] do
    for slot in [:n] do
      facts := facts.push (.tupleProjection tuple slot ((tuple + slot) % n) 0)
  return facts

private def productFamilies (n : Nat) : Array ProductFamilySpec :=
  (Array.range n).map fun i =>
    { domain := i
      qualityType := i
      dimensionThings := Array.range n
      typeThings := Array.range n }

private def ast (family : Family) (scale : Nat) : ModelAST :=
  let n := scale + 1
  { worldCount := 1
    thingCount := n
    facts := match family with
      | .sparse | .product => sparseFacts n
      | .dense => denseFacts n
      | .cyclic => cyclicFacts n
      | .projection => projectionFacts n
    productFamilies := if family matches .product then productFamilies n else #[] }

private structure Row where
  compilerCost : Nat
  probeCost : Nat

private structure Probe where
  name : String
  cost : Nat
  passed : Bool

/-- Exercise the intended operation directly, even when the aggregate checker
fails earlier. Fixture validation is benchmark bookkeeping, not part of the
reported production-operation cost. These models need not satisfy all axioms. -/
private def targetedProbe (family : Family) (tables : FactTables) (model : FiniteModel4) : Probe :=
  let world : Fin model.worldCount := ⟨0, model.worldPositive⟩
  match family with
  | .sparse =>
      let scan := Checker.allThingsEvalCosted model fun x =>
        tables.unaryTypedTableCosted .endurant x world
      ⟨"unary_scan", scan.cost, scan.value⟩
  | .dense =>
      let scan := Checker.allThingsEvalCosted model fun x =>
        Checker.allThingsEvalCosted model fun y => tables.binaryTypedTableCosted .part x y world
      ⟨"binary_scan", scan.cost, scan.value⟩
  | .cyclic =>
      let closure := tables.inherenceClosureAtCosted 0
      ⟨"closure_rebuild", closure.cost,
        closure.value.reachable.size == model.thingCount ^ 2 && closure.value.reachable.all id⟩
  | .product =>
      let last : Fin model.thingCount := ⟨model.thingCount - 1, by have := model.thingPositive; omega⟩
      let search := Checker.productFamilySearchCosted model last last world
      -- Only the last family's header matches. Missing association facts make
      -- it fail too, so the search must visit the complete family array.
      ⟨"family_search", search.cost,
        model.productFamilies.size == model.thingCount && !search.value⟩
  | .projection =>
      let scan := Checker.allThingsEvalCosted model fun tuple =>
        Checker.allFinEvalCosted model.thingCount fun slot => do
          let result ← model.tupleProjectionCosted tuple slot world
          -- Addition, remainder, and comparison validate each stored cell.
          Complexity.Costed.tick
            (result.val == (tuple.val + slot.val) % model.thingCount) 3
      ⟨"projection_scan", scan.cost, scan.value⟩

private def benchmark (family : Family) (scale : Nat) : IO Row := do
  let input := ast family scale
  if bounded : Complexity.Production.explicitModelWellBounded input then
    let start ← IO.monoMsNow
    let compiled := compileExplicitModelASTCosted input
    let compiledAt ← IO.monoMsNow
    have same : compiled.value = compileExplicitModelAST input := compileExplicitModelASTCosted_value input
    let construction := compiled.value.toFiniteModel4CachedCosted input.worldCount input.thingCount
      (by simp [input, ast]) (by simp [input, ast])
      (by rw [same]; exact compiledLookups_agree input bounded)
      (by rw [same]; exact compileExplicitModelAST_inherenceCacheValid input)
      (by rw [same]; exact (compileExplicitModelAST_tableDimensions input).1)
      (by rw [same]; exact (compileExplicitModelAST_tableDimensions input).2)
    let model := construction.value
    let constructedAt ← IO.monoMsNow
    let checked := Checker.checkAxioms4Costed model
    let checkedAt ← IO.monoMsNow
    let probe := targetedProbe family compiled.value model
    let stop ← IO.monoMsNow
    unless probe.passed do
      throw <| IO.userError s!"{family.name} scale {scale}: {probe.name} did not exercise its intended fixture"
    let metrics := Complexity.modelMetrics input.worldCount input.thingCount compiled.value
    let relationCells := metrics.unaryCells + metrics.binaryCells + metrics.ternaryCells
    IO.println s!"{family.name},{input.thingCount},{input.facts.size},\
      {metrics.productFamilySlots},{relationCells},{metrics.projectionCells},\
      {compiled.cost},{construction.cost},{checked.cost},{probe.name},{probe.cost},\
      {compiledAt - start},{constructedAt - compiledAt},{checkedAt - constructedAt},{stop - checkedAt},\
      {checked.value},{probe.passed}"
    return ⟨compiled.cost, probe.cost⟩
  else
    throw <| IO.userError s!"{family.name} scale {scale}: generated coordinates are out of bounds"

private def nondecreasing : List Nat → Bool
  | .nil => true
  | .cons _ .nil => true
  | .cons left (.cons right rest) =>
      decide (left ≤ right) && nondecreasing (.cons right rest)

private def requireNondecreasing (label : String) (costs : Array Nat) : IO Unit :=
  unless nondecreasing costs.toList do
    throw <| IO.userError s!"non-monotone {label} costs: {costs}"

private def compilerCost (input : ModelAST) : Nat :=
  (compileExplicitModelASTCosted input).cost

private def worldProbe (worldCount : Nat) : ModelAST :=
  { worldCount
    thingCount := 2
    facts := (Array.range worldCount).map fun world => .unary .endurant 0 world }

private def thingProbe (thingCount : Nat) : ModelAST :=
  { worldCount := 1
    thingCount
    facts := (Array.range thingCount).map fun thing => .unary .endurant thing 0 }

private def factProbe (factCount : Nat) : ModelAST :=
  { worldCount := 1
    thingCount := 9
    facts := (Array.range factCount).map fun thing => .unary .endurant thing 0 }

private def witnessProbe (slotCount : Nat) : ModelAST :=
  { worldCount := 1
    thingCount := 9
    facts := sparseFacts 9
    productFamilies := #[{
      domain := 0
      qualityType := 0
      dimensionThings := Array.range slotCount
      typeThings := Array.range slotCount }] }

/--
Check monotonicity only for controlled input families that preserve their
earlier prefix. Arbitrary checker executions need not be monotone because a new
fact can cause an earlier short-circuit. These probes test the scaling behavior
used by this benchmark, not a universal semantic theorem.
-/
private def checkMonotonicity : IO Unit := do
  let scales := #[1, 2, 4, 8]
  requireNondecreasing "world" <| scales.map fun n => compilerCost (worldProbe n)
  requireNondecreasing "thing" <| scales.map fun n => compilerCost (thingProbe n)
  requireNondecreasing "fact" <| scales.map fun n => compilerCost (factProbe n)
  requireNondecreasing "witness-slot" <| scales.map fun n => compilerCost (witnessProbe n)

def run : IO Unit := do
  checkMonotonicity
  IO.println "family,things,facts,product_family_slots,relation_cells,projection_cells,compiler_cost,model_cost,checker_cost,probe,probe_cost,compiler_ms,model_ms,checker_ms,probe_ms,result,probe_passed"
  for family in #[Family.sparse, .dense, .cyclic, .product, .projection] do
    let mut compilerCosts := #[]
    let mut probeCosts := #[]
    for scale in #[1, 2, 4, 8] do
      let row ← benchmark family scale
      compilerCosts := compilerCosts.push row.compilerCost
      probeCosts := probeCosts.push row.probeCost
    requireNondecreasing s!"{family.name} compiler" compilerCosts
    requireNondecreasing s!"{family.name} controlled probe" probeCosts

end LeanUfo.ComplexityBenchmarks

def main : IO Unit := LeanUfo.ComplexityBenchmarks.run
