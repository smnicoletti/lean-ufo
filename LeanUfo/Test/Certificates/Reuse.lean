import LeanUfo.UFO.DSL.Complexity.Reuse

/-!
# Reuse planner regressions

The fixtures check ordered equality and exact counts, including work skipped
after a mismatch. They exercise production erasures, not a second planner.
The general equivalence and bound proofs are in `Complexity/Reuse.lean`.
Certification fixtures separately check that generated reuse proofs elaborate.
-/

namespace LeanUfo.Test.Certificates.Reuse
open LeanUfo.UFO.DSL LeanUfo.UFO.DSL.Complexity

private def eqNames (a b : Array String) : Costed Bool :=
  arrayEqCosted a b (fun x y => Costed.tick (x == y))

-- Two units test the lengths. Each visited pair adds five units: two reads,
-- one comparison, one loop step, and one Boolean test.
example : eqNames #[] #[] = ⟨true, 2⟩ := by native_decide
example : eqNames #["a"] #[] = ⟨false, 2⟩ := by native_decide
example : eqNames #["a", "b"] #["a", "b"] = ⟨true, 12⟩ := by native_decide
example : eqNames #["a", "b"] #["x", "b"] = ⟨false, 7⟩ := by native_decide
example : eqNames #["a", "b"] #["a", "x"] = ⟨false, 12⟩ := by native_decide
example : eqNames #["a", "b"] #["b", "a"] = ⟨false, 7⟩ := by native_decide
example : eqNames #["a", "a"] #["a"] = ⟨false, 2⟩ := by native_decide

private def emptySource : ModelSource := { worlds := #[], things := #[] }
private def namedSource : ModelSource := { worlds := #["w"], things := #["x", "y"] }
private def namedFamily : NamedProductFamily := ⟨"d", "q", #["x", "y"], #["t"]⟩

private def factCases : Array NamedScopedFact := #[
  .unary .endurant "x" .everywhere,
  .unary .perdurant "x" .everywhere,
  .unary .endurant "y" .everywhere,
  .unary .endurant "x" (.at "w"),
  .unary .endurant "x" (.at "v"),
  .binary .inheresIn "x" "y" .everywhere,
  .binary .part "x" "y" .everywhere,
  .binary .inheresIn "y" "x" (.at "w"),
  .ternary .distance "x" "y" "z" .everywhere,
  .ternary .distance "x" "y" "t" (.at "w"),
  .tupleProjection "x" 0 "y" .everywhere,
  .tupleProjection "x" 1 "y" (.at "w"),
  .derived (.unary "f" "x") .everywhere,
  .derived (.binary "f" "x" "y") .everywhere,
  .derived (.ternary "f" "x" "y" "z") (.at "w"),
  .derived (.quaternary "f" "x" "y" "z" "t") (.at "w"),
  .derived (.quaternary "f" "x" "y" "z" "u") (.at "w")]

private def sourceCases : Array ModelSource :=
  #[emptySource, namedSource,
    { namedSource with worlds := #["v"] },
    { namedSource with things := #["y", "x"] },
    { namedSource with deriveRelations := false },
    { namedSource with productFamilies := #[namedFamily] },
    { namedSource with productFamilies := #[{ namedFamily with domain := "e" }] },
    { namedSource with productFamilies := #[{ namedFamily with qualityType := "r" }] },
    { namedSource with productFamilies := #[{ namedFamily with dimensionThings := #["y", "x"] }] },
    { namedSource with productFamilies := #[{ namedFamily with typeThings := #["u"] }] },
    { namedSource with productFamilies := #[{ namedFamily with typeThings := #[] }] }] ++
    factCases.map (fun f => { namedSource with facts := #[f] })

-- All 28 × 28 pairs exercise both argument orders, including each fact form.
example : sourceCases.all (fun a => sourceCases.all (fun b =>
    (modelSourceEqCosted a b).value == (a == b))) = true := by native_decide
example : modelSourceEqCosted emptySource emptySource = ⟨true, 13⟩ := by native_decide
example : modelSourceEqCosted namedSource namedSource = ⟨true, 28⟩ := by native_decide
example : (modelSourceEqCosted namedSource emptySource).cost = 3 := by native_decide
example : (modelSourceEqCosted
    { emptySource with productFamilies := #[namedFamily] }
    { emptySource with productFamilies := #[namedFamily] }).cost = 41 := by native_decide
example : (modelSourceEqCosted
    { namedSource with facts := #[factCases[0]!, factCases[0]!] }
    { namedSource with facts := #[factCases[0]!] }).value = false := by native_decide

private def tables : FactTables :=
  { unary := ({} : Std.HashMap String (Array (Nat × Nat))).insert "endurant" #[(0, 0), (1, 0)]
    binary := ({} : Std.HashMap String (Array (Nat × Nat × Nat))).insert "part" #[(0, 1, 0)]
    ternary := ({} : Std.HashMap String (Array (Nat × Nat × Nat × Nat))).insert "distance" #[(0, 1, 2, 0)]
    tupleProjection := #[(0, 0, 1, 0)]
    productFamilies := #[⟨0, 1, #[2, 3], #[4]⟩] }

example : sameUnaryFootprintCosted #["endurant"] tables tables = ⟨true, 21⟩ := by native_decide
example : sameBinaryFootprintCosted #["part"] tables tables = ⟨true, 16⟩ := by native_decide
example : sameTernaryFootprintCosted #["distance"] tables tables = ⟨true, 18⟩ := by native_decide
example : sameUnaryFootprintCosted #["missing"] tables tables = ⟨true, 7⟩ := by native_decide
example : sameUnaryFootprintCosted #["endurant"] tables {} = ⟨false, 7⟩ := by native_decide
example : sameUnaryFootprintCosted #["endurant", "missing"] tables
    { tables with unary := tables.unary.insert "endurant" #[(1, 0), (0, 0)] } =
      ⟨false, 13⟩ := by native_decide
example : sameUnaryFootprint #["endurant"] tables
    { tables with unary := tables.unary.insert "other" #[(9, 9)] } = true := by native_decide
example : footprintUnchangedCosted { field := "test" } tables {} = ⟨true, 6⟩ := by native_decide
example : footprintUnchangedCosted { field := "test", tupleProjection := true }
    tables tables = ⟨true, 19⟩ := by native_decide
example : footprintUnchangedCosted { field := "test", productFamilies := true }
    tables tables = ⟨true, 36⟩ := by native_decide

example : (reusableFieldFootprintCosted "ax1").cost = 5 := by native_decide
example : (reusableFieldFootprintCosted "missing").cost =
    4 * reusableFieldFootprints.size + 1 := by native_decide
example : (reusableFieldFootprint? "ax99").map (·.field) = some "ax99" := by native_decide
example : (reusableFieldFootprint? "missing").isNone = true := by native_decide

-- Fresh mode does no comparison; equal sources skip footprint lookup.
example : certificateReuseSourceCosted `Parent namedSource emptySource tables {} true "ax1" =
    ⟨none, 1⟩ := by native_decide
example : certificateReuseSourceCosted `Parent emptySource emptySource tables {} false "missing" =
    ⟨some `Parent, 16⟩ := by native_decide
example : certificateReuseSource? `Parent namedSource emptySource tables tables false "ax105" =
    some `Parent := by native_decide
example : certificateReuseSource? `Parent namedSource emptySource tables {} false "missing" =
    none := by native_decide

-- Dense materialization must leave duplicate metadata rows intact. Each
-- fact appends at most one row, even when the resulting dense cell was set.
private def duplicateAST : ModelAST :=
  { worldCount := 1, thingCount := 2
    facts := #[.unary .endurant 0 0, .unary .endurant 0 0,
      .binary .part 0 1 0, .ternary .distance 0 1 0 0,
      .tupleProjection 0 0 1 0, .tupleProjection 0 0 1 0, .derived "True"]
    productFamilies := #[⟨0, 1, #[0, 1], #[1, 0]⟩] }

example :
    let out := compileExplicitModelAST duplicateAST
    ((out.unary.getD "endurant" #[]).size, (out.binary.getD "part" #[]).size,
      (out.ternary.getD "distance" #[]).size, out.tupleProjection.size,
      out.productFamilies.size, out.derivedProps.size) = (2, 1, 1, 2, 1, 1) := by native_decide

example (ast : ModelAST) : (compileExplicitModelAST ast).RowSizesBoundedBy ast.facts.size :=
  compileExplicitModelAST_rowSizes ast

example (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled) :
    compiled.tables.RowSizesBoundedBy (sourceMetrics source).specializationFactsUpper :=
  compiledRowSizes_le_sourceMetrics source compiled success

private def familySource : ModelSource :=
  { worlds := #["w", "v"], things := #["x", "y"]
    facts := #[.unary .object "x" .everywhere, .unary .object "x" .everywhere,
      .tupleProjection "x" 0 "y" (.at "w")]
    productFamilies := #[⟨"x", "y", #["x", "y"], #["y", "x"]⟩,
      ⟨"x", "y", #["x", "y"], #["y", "x"]⟩] }

-- The bound uses returned parent tables, including expanded facts and slots.
-- Child comparisons may stop early, but the same size bound covers them all.
example :
    (match compileModelSource familySource with
    | .error _ => false
    | .ok parent => sourceCases.all (fun child => reusableFieldFootprints.all (fun fp =>
        decide ((certificateReuseSourceCosted `Parent familySource child parent.tables {} false fp.field).cost ≤
          18 * (sourceMetrics child).inputSize + 11023 * (sourceMetrics familySource).inputSize)))) =
      true := by native_decide

example (parentSource childSource : ModelSource) (parent : CompiledModelSource)
    (success : compileModelSource parentSource = .ok parent) :
    (certificateReuseSourceCosted `Parent parentSource childSource parent.tables {} false "ax99").cost ≤
      18 * (sourceMetrics childSource).inputSize + 11023 * (sourceMetrics parentSource).inputSize :=
  certificateReuseSource_source_bound _ _ _ _ _ _ _ success

example {C C' P P' : Nat} (child : C ≤ C') (parent : P ≤ P') :
    18 * C + 11023 * P ≤ 18 * C' + 11023 * P' :=
  certificateReuseSource_bound_mono child parent

end LeanUfo.Test.Certificates.Reuse
