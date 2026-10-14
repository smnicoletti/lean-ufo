import LeanUfo.UFO.DSL.Compiler.VerifiedModel

/-!
# Native and kernel table agreement

Raw table updates can leave dense storage absent or stale. These regressions
exercise that public API as well as the proved compiled-model boundary. A
native-only test would miss a disagreement with kernel reduction, so each raw
lookup has both kinds of evidence.
-/

namespace LeanUfo.Test.TableCorrespondence

open LeanUfo.UFO.DSL

private def rawUnary : FactTables := addUnary {} "endurant" 0 0
private def rawBinary : FactTables := addBinary {} "inst" 0 1 0
private def rawTernary : FactTables := addTernary {} "distance" 0 1 1 0
private def rawProjection : FactTables := addTupleProjection {} 0 0 1 0

example : rawUnary.unaryTypedTable .endurant (0 : Fin 2) (0 : Fin 1) = true := rfl
example : rawUnary.unaryTypedTable .endurant (0 : Fin 2) (0 : Fin 1) = true := by native_decide
example : rawBinary.binaryTypedTable .inst (0 : Fin 2) 1 (0 : Fin 1) = true := rfl
example : rawBinary.binaryTypedTable .inst (0 : Fin 2) 1 (0 : Fin 1) = true := by native_decide
example : rawTernary.ternaryTypedTable .distance (0 : Fin 2) 1 1 (0 : Fin 1) = true := rfl
example : rawTernary.ternaryTypedTable .distance (0 : Fin 2) 1 1 (0 : Fin 1) = true := by native_decide
example : rawProjection.tupleProjectionTypedTable (0 : Fin 2) 0 (0 : Fin 1) = 1 := rfl
example : rawProjection.tupleProjectionTypedTable (0 : Fin 2) 0 (0 : Fin 1) = 1 := by native_decide

/-- A stale dense field cannot change the meaning of the raw lookup API. -/
private def staleUnary : FactTables :=
  { rawUnary with
    denseThingCount := 2
    denseWorldCount := 1
    unaryCells := Array.replicate (UnaryField.count * 2) false }

example : staleUnary.unaryTypedTable .endurant (0 : Fin 2) (0 : Fin 1) = true := rfl
example : staleUnary.unaryTypedTable .endurant (0 : Fin 2) (0 : Fin 1) = true := by native_decide

private def input : ModelAST :=
  { worldCount := 1
    thingCount := 2
    facts := #[.unary .endurant 0 0, .binary .inst 0 1 0,
      .ternary .distance 0 1 1 0, .tupleProjection 0 0 1 0]
    productFamilies := #[{
      domain := 0
      qualityType := 1
      dimensionThings := #[0]
      typeThings := #[1] }] }

private theorem inputBounded : Complexity.Production.explicitModelWellBounded input := by decide

private def model := compileVerifiedModel input (by decide) (by decide) inputBounded

example : model.endurant (0 : Fin 2) (0 : Fin 1) = true := rfl
example : model.endurant (0 : Fin 2) (0 : Fin 1) = true := by native_decide
example : model.inst (0 : Fin 2) (1 : Fin 2) (0 : Fin 1) = true := by native_decide
example : model.distance (0 : Fin 2) (1 : Fin 2) (1 : Fin 2) (0 : Fin 1) = true := by native_decide
example : (model.tupleProjection (0 : Fin 2) (0 : Fin 1) (0 : Fin 1)).val = 1 := rfl
example : (model.tupleProjection (0 : Fin 2) (0 : Fin 1) (0 : Fin 1)).val = 1 := by native_decide
-- The proved native replacement preserves the full projection result. Kernel
-- reduction retains the compact value, while native code runs one dense lookup.
example : model.tupleProjectionCosted (0 : Fin 2) (0 : Fin 1) (0 : Fin 1) =
    ⟨(1 : Fin 2), 11⟩ := by decide
example : model.tupleProjectionCosted (0 : Fin 2) (0 : Fin 1) (0 : Fin 1) =
    ⟨(1 : Fin 2), 11⟩ := by native_decide
example : model.productFamilies.size = 1 := by native_decide

end LeanUfo.Test.TableCorrespondence
