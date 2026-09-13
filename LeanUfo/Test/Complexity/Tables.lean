import LeanUfo.UFO.DSL.Compiler

/-!
# Counted table construction and queries

Initialization precedes each measured insertion. These regressions check exact
coordinate-arithmetic counts, field isolation, and idempotent duplicate writes.
Query tests include index arithmetic and each visited branch, including raw
tables with missing cells or invalid projection results. General value
correspondence and cost bounds are proved in the compiler.
-/

namespace LeanUfo.Test.Complexity.Tables

open LeanUfo.UFO.DSL

private def emptyTables : FactTables := ({} : FactTables).initializeDense 2 2 2

private def queryTables : FactTables :=
  (((emptyTables.writeDenseFact (.unary .ex 1 1)).writeDenseFact
    (.binary .inst 0 1 0)).writeDenseFact
    (.ternary .distance 1 0 1 1)).writeDenseFact (.tupleProjection 0 1 1 1)

-- Both callers execute the same binary operation, including its cost.
example (tables : FactTables) (world : Fin tables.denseWorldCount)
    (left right : Fin tables.denseThingCount) :
    tables.inherenceEdgeAtCosted world.val left right =
      tables.binaryTypedTableCosted .inheresIn left right world := rfl

example : queryTables.inherenceEdgeAtCosted 0 (0 : Fin 2) (1 : Fin 2) = ⟨false, 11⟩ := by native_decide
example : (queryTables.writeDenseFact (.binary .inheresIn 0 1 0)).inherenceEdgeAtCosted
    0 (0 : Fin 2) (1 : Fin 2) = ⟨true, 11⟩ := by native_decide

-- Empty and singleton matrices make no edge queries. A high callback cost
-- therefore changes neither count. The singleton includes its one pivot.
example : (Complexity.warshallStateEvalCosted 0
    (fun _ _ => Complexity.Costed.tick false 1000)).cost = 0 := by native_decide
example : (Complexity.warshallStateEvalCosted 1
    (fun _ _ => Complexity.Costed.tick false 1000)).cost = 29 := by native_decide

-- Two off-diagonal pairs are queried in each initial matrix. Replacing unit
-- queries by eleven-operation queries adds 4 * 10 = 40 operations. Expensive
-- diagonal callbacks remain skipped, not charged at their upper bound.
example : (Complexity.warshallStateEvalCosted 2 (fun i j =>
    Complexity.Costed.tick false (if i == j then 1000 else 11))).cost = 228 := by native_decide
example : (Complexity.warshallStateEvalCosted 2 (fun i j =>
    Complexity.Costed.tick true (if i == j then 1000 else 11))).cost = 200 := by native_decide

example (n : Nat) (edge : Fin n → Fin n → Bool) (cost : Fin n → Fin n → Nat) :
    (Complexity.warshallStateEvalCosted n (fun i j => Complexity.Costed.tick (edge i j) (cost i j))).value =
      Complexity.warshallState n edge :=
  Complexity.warshallStateEvalCosted_value n _

-- Row-major conversion adds 13 * 4 = 52 operations to the two-thing core.
-- A two-edge cycle reaches every pair and retains first hops 0, 1, 0, 1.
example :
    let result := emptyTables.inherenceClosureAtCosted 0
    result.cost = 280 ∧ result.value.reachable = #[true, false, false, true] ∧
      result.value.nextHop = #[some 0, none, none, some 1] := by native_decide
example :
    let tables := (emptyTables.writeDenseFact (.binary .inheresIn 0 1 0)).writeDenseFact
      (.binary .inheresIn 1 0 0)
    let result := tables.inherenceClosureAtCosted 0
    result.cost = 252 ∧ result.value.reachable = #[true, true, true, true] ∧
      result.value.nextHop = #[some 0, some 1, some 0, some 1] := by native_decide

example : (({} : FactTables).inherenceClosureAtCosted 0).cost = 0 := by native_decide

-- Width products, coordinates, field selection, flat indexing, checked read,
-- and optional-result test total 8, 11, and 14 operations respectively.
example : queryTables.unaryTypedTableCosted .ex (1 : Fin 2) (1 : Fin 2) =
    ⟨true, 8⟩ := by native_decide
example : queryTables.unaryTypedTableCosted .endurant (1 : Fin 2) (1 : Fin 2) =
    ⟨false, 8⟩ := by native_decide
example : queryTables.binaryTypedTableCosted .inst (0 : Fin 2) 1 (0 : Fin 2) =
    ⟨true, 11⟩ := by native_decide
example : queryTables.binaryTypedTableCosted .inheresIn (0 : Fin 2) 1 (0 : Fin 2) =
    ⟨false, 11⟩ := by native_decide
example : queryTables.ternaryTypedTableCosted .distance (1 : Fin 2) 0 1 (1 : Fin 2) =
    ⟨true, 14⟩ := by native_decide
example : queryTables.ternaryTypedTableCosted .distance (1 : Fin 2) 1 0 (1 : Fin 2) =
    ⟨false, 14⟩ := by native_decide
example : ({} : FactTables).unaryTypedTableCosted .ex (1 : Fin 2) (1 : Fin 2) =
    ⟨false, 8⟩ := by native_decide

-- Projection lookup first tests the slot, then computes and reads its cell.
-- Stored results add their own finite-coordinate check. A missing result
-- returns the queried tuple; these branches perform different amounts of work.
example : queryTables.tupleProjectionTypedTableCosted (0 : Fin 2) 1 (1 : Fin 2) =
    ⟨1, 11⟩ := by native_decide
example : queryTables.tupleProjectionTypedTableCosted (0 : Fin 2) 2 (1 : Fin 2) =
    ⟨0, 2⟩ := by native_decide
example : emptyTables.tupleProjectionTypedTableCosted (0 : Fin 2) 1 (1 : Fin 2) =
    ⟨0, 9⟩ := by native_decide
example : ({ denseProjectionArity := 2 } : FactTables).tupleProjectionTypedTableCosted
    (0 : Fin 2) 1 (1 : Fin 2) = ⟨0, 8⟩ := by native_decide
example : (emptyTables.writeDenseFact (.tupleProjection 0 1 7 1)).tupleProjectionTypedTableCosted
    (0 : Fin 2) 1 (1 : Fin 2) = ⟨0, 11⟩ := by native_decide

example : ({} : FactTables).inherenceClosureTableCosted
    (0 : Fin 2) 1 (0 : Fin 1) = ⟨false, 2⟩ := by native_decide
example : ({ denseThingCount := 2, inherenceClosures := #[#[false, true, false, false]] } :
    FactTables).inherenceClosureTableCosted (0 : Fin 2) 1 (0 : Fin 1) =
    ⟨true, 6⟩ := by native_decide
example : ({ denseThingCount := 2, inherenceClosures := #[#[]] } :
    FactTables).inherenceClosureTableCosted (0 : Fin 2) 1 (0 : Fin 1) =
    ⟨false, 6⟩ := by native_decide

example : (emptyTables.writeDenseFactCosted (.unary .ex 1 1)).cost = 8 := by native_decide
example : (emptyTables.writeDenseFactCosted (.binary .inst 0 1 0)).cost = 11 := by native_decide
example : (emptyTables.writeDenseFactCosted (.ternary .distance 1 0 1 1)).cost = 14 := by
  native_decide
example : (emptyTables.writeDenseFactCosted (.tupleProjection 1 0 1 1)).cost = 6 := by
  native_decide
example : (emptyTables.writeDenseFactCosted (.derived "unused by dense tables")).cost = 1 := by
  native_decide

/-- Five input visits add ten operations to the forty operations spent in the
insertion callbacks. Only the selected coordinate in each table becomes true. -/
example :
    let result := Complexity.Costed.foldArray #[.unary .ex 1 1,
      .binary .inst 0 1 0, .ternary .distance 1 0 1 1,
      .tupleProjection 1 0 1 1, .derived "unused by dense tables"]
      emptyTables FactTables.writeDenseFactCosted
    result.cost = 50 ∧
      (result.value.unaryCells.toList.filter id).length = 1 ∧
      (result.value.binaryCells.toList.filter id).length = 1 ∧
      (result.value.ternaryCells.toList.filter id).length = 1 ∧
      result.value.unaryCells[UnaryField.ex.index * 4 + 3]! = true ∧
      result.value.binaryCells[BinaryField.inst.index * 8 + 2]! = true ∧
      result.value.ternaryCells[TernaryField.distance.index * 16 + 11]! = true ∧
      result.value.projectionCells[5]! = some 1 := by native_decide

/-- Repeating an insertion still incurs its operations but changes no extra
cell. A different unary field at the same coordinates occupies a separate cell. -/
example :
    let result := Complexity.Costed.foldArray #[.unary .ex 1 1,
      .unary .endurant 1 1, .unary .ex 1 1] emptyTables FactTables.writeDenseFactCosted
    result.cost = 30 ∧
      (result.value.unaryCells.toList.filter id).length = 2 ∧
      result.value.unaryCells[UnaryField.ex.index * 4 + 3]! = true ∧
      result.value.unaryCells[UnaryField.endurant.index * 4 + 3]! = true ∧
      (result.value.binaryCells.toList.filter id).length = 0 ∧
      (result.value.ternaryCells.toList.filter id).length = 0 := by native_decide

example : (compileExplicitFactCosted {} (.unary .ex 1 1)).cost = 5 := by native_decide
example : (compileExplicitFactCosted {} (.binary .inst 0 1 0)).cost = 5 := by native_decide
example : (compileExplicitFactCosted {} (.ternary .distance 1 0 1 1)).cost = 5 := by native_decide
example : (compileExplicitFactCosted {} (.tupleProjection 1 0 1 1)).cost = 2 := by native_decide
example : (compileExplicitFactCosted {} (.derived "assertion")).cost = 2 := by native_decide

/-- Sparse construction retains inspectable records and the corresponding
lookup functions. These queries occur after the measured construction. -/
example :
    let result := Complexity.Costed.foldArray #[.unary .ex 1 1,
      .binary .inst 0 1 0, .ternary .distance 1 0 1 1,
      .tupleProjection 1 0 1 1, .derived "assertion"] {} compileExplicitFactCosted
    result.cost = 29 ∧
      result.value.unary.getD "ex" #[] = #[(1, 1)] ∧
      result.value.binary.getD "inst" #[] = #[(0, 1, 0)] ∧
      result.value.ternary.getD "distance" #[] = #[(1, 0, 1, 1)] ∧
      result.value.tupleProjection = #[(1, 0, 1, 1)] ∧
      result.value.derivedProps = #["assertion"] ∧
      result.value.unaryLookup "ex" 1 1 = true ∧
      result.value.unaryLookup "endurant" 1 1 = false ∧
      result.value.binaryLookup "inst" 0 1 0 = true ∧
      result.value.ternaryLookup "distance" 1 0 1 1 = true ∧
      result.value.tupleProjectionResult? 1 0 1 = some 1 := by native_decide

/-- Raw sparse construction does not validate projection conflicts. It keeps
both asserted tuples, with the last result returned by the projection function. -/
example :
    let result := Complexity.Costed.foldArray #[.tupleProjection 1 0 0 1,
      .tupleProjection 1 0 1 1] {} compileExplicitFactCosted
    result.cost = 8 ∧ result.value.tupleProjection = #[(1, 0, 0, 1), (1, 0, 1, 1)] ∧
      result.value.tupleProjectionLookup 1 0 0 1 = true ∧
      result.value.tupleProjectionLookup 1 0 1 1 = true ∧
      result.value.tupleProjectionResult? 1 0 1 = some 1 := by native_decide

example :
    let ast : ModelAST := { worldCount := 0, thingCount := 0, facts := #[] }
    (compileExplicitModelASTCosted ast).cost = 11 := by native_decide

/-- A derived fact costs four operations in sparse construction, four in the
arity scan, and three in dense traversal, in addition to eleven size products. -/
example :
    let ast : ModelAST := { worldCount := 0, thingCount := 0, facts := #[.derived "assertion"] }
    let result := compileExplicitModelASTCosted ast
    result.cost = 22 ∧ result.value.derivedProps = #["assertion"] := by native_decide

/-- Registering two existing family records costs six operations, independently
of their witness-array sizes. Converting those witnesses is a separate stage. -/
example :
    let families : Array ProductFamilySpec := #[
      ⟨1, 2, #[3, 4], #[5]⟩, ⟨6, 7, #[], #[8, 9, 10]⟩]
    let ast : ModelAST :=
      { worldCount := 0, thingCount := 0, facts := #[], productFamilies := families }
    let result := compileExplicitModelASTCosted ast
    result.cost = 17 ∧ result.value.productFamilies = families := by native_decide

end LeanUfo.Test.Complexity.Tables
