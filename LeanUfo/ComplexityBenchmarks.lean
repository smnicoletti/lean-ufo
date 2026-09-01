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
  checkerCost : Nat

private def benchmark (family : Family) (scale : Nat) : IO Row := do
  let n := scale + 1
  let input := ast family scale
  let start ← IO.monoMsNow
  let compiled := compileExplicitModelASTCosted input
  let model := compiled.value.toFiniteModel4 1 n (by omega) (by omega)
  let checked := Checker.checkAxioms4Costed model
  let stop ← IO.monoMsNow
  let metrics := Complexity.modelMetrics input.worldCount input.thingCount compiled.value
  let relationCells := metrics.unaryCells + metrics.binaryCells + metrics.ternaryCells
  IO.println s!"{family.name},{input.thingCount},{input.facts.size},\
    {metrics.productFamilySlots},{relationCells},{metrics.projectionCells},\
    {compiled.cost},{checked.cost},{stop - start},{checked.value}"
  return ⟨compiled.cost, checked.cost⟩

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
  IO.println "family,things,facts,product_family_slots,relation_cells,projection_cells,compiler_cost,checker_cost,elapsed_ms,result"
  for family in #[Family.sparse, .dense, .cyclic, .product, .projection] do
    let mut compilerCosts := #[]
    let mut checkerCosts := #[]
    for scale in #[1, 2, 4, 8] do
      let row ← benchmark family scale
      compilerCosts := compilerCosts.push row.compilerCost
      checkerCosts := checkerCosts.push row.checkerCost
    requireNondecreasing s!"{family.name} compiler" compilerCosts
    requireNondecreasing s!"{family.name} checker" checkerCosts

end LeanUfo.ComplexityBenchmarks

def main : IO Unit := LeanUfo.ComplexityBenchmarks.run
