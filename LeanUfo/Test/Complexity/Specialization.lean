import LeanUfo.UFO.DSL.Compiler

/-!
# Reflexive-specialization traversal regressions

The original fact sequence is a prefix of the output. Each instantiation then
contributes one reflexive-specialization witness per world, in ascending world
order. Repeated targets remain repeated. Exact counts include copying the
original prefix, inspecting facts, and constructing witnesses.

The native tests supplement the compiler's general value, size, projection,
and cost proofs. Large inputs check that numeric traversal does not allocate
a world-range array or retain one pending cost addition per world.
-/

namespace LeanUfo.Test.Complexity.Specialization

open LeanUfo.UFO.DSL

example :
    let result := addReflexiveSpecializationFactsCosted 3 #[]
    result.value.size = 0 ∧ result.cost = 0 := by native_decide

/-- A non-binary fact costs three copy operations and three inspection
operations. Binary inspection adds a field comparison and Boolean test. -/
example :
    let result := addReflexiveSpecializationFactsCosted 3 #[
      .unary .ex 1 0, .binary .sub 1 2 0, .ternary .distance 0 1 2 0,
      .tupleProjection 3 2 4 0, .derived "retained"]
    (match result.value.toList with
      | [.unary .ex 1 0, .binary .sub 1 2 0, .ternary .distance 0 1 2 0,
         .tupleProjection 3 2 4 0, .derived "retained"] => true
      | _ => false) = true ∧ result.cost = 32 := by native_decide

/-- Raw input coordinates are not revalidated by expansion. With zero worlds,
the instantiation is retained and no specialization witness is emitted. -/
example :
    let result := addReflexiveSpecializationFactsCosted 0 #[.binary .inst 0 1 7]
    (match result.value.toList with | [.binary .inst 0 1 7] => true | _ => false) =
      true ∧ result.cost = 8 := by native_decide

/-- Six copy operations, ten input-inspection operations, and twelve witness
operations give 28. Witnesses follow the complete original prefix. -/
example :
    let result := addReflexiveSpecializationFactsCosted 2 #[
      .binary .inst 0 1 0, .binary .inst 2 1 1]
    (match result.value.toList with
      | [.binary .inst 0 1 0, .binary .inst 2 1 1,
         .binary .sub 1 1 0, .binary .sub 1 1 1,
         .binary .sub 1 1 0, .binary .sub 1 1 1] => true
      | _ => false) = true ∧ result.cost = 28 := by native_decide

example :
    let result := addReflexiveSpecializationFactsCosted 1000000 #[.binary .inst 0 1 0]
    result.value.size = 1000001 ∧ result.cost = 3000008 ∧
      (match result.value[1000000]! with
        | .binary .sub 1 1 999999 => true | _ => false) = true := by native_decide

example :
    let result := addReflexiveSpecializationFactsCosted 0
      (Array.replicate 100000 (.binary .inst 0 1 0))
    result.value.size = 100000 ∧ result.cost = 800000 := by native_decide

end LeanUfo.Test.Complexity.Specialization
