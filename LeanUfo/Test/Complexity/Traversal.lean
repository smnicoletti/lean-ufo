import LeanUfo.UFO.DSL.Compiler

/-!
# Counted traversal regressions

Million-entry inputs guard against retaining one pending cost addition per
entry on the call stack. The inputs to the fold tests are already allocated:
their construction is outside the measured fold. Initialization has its own
test. These native checks supplement the general kernel-checked value and cost
theorems in `CostModel`; they do not establish those theorems.
-/

namespace LeanUfo.Test.Complexity.Traversal

open LeanUfo.UFO.DSL.Complexity
open LeanUfo.UFO.DSL

example :
    let result := Costed.replicateArray 1000000 false
    (result.value.size, result.cost) = (1000000, 2000000) := by
  native_decide

example :
    let result := Costed.vectorOfFn (fun i : Fin 1000000 => Costed.tick i.val 1)
    (result.value[999999]!, result.cost) = (999999, 3000000) := by
  native_decide

example :
    Costed.foldArray (Array.replicate 1000000 ()) 0
      (fun n _ => Costed.tick (n + 1) 1) = ⟨1000000, 3000000⟩ := by
  native_decide

example :
    let result := Costed.foldArrayExcept (Array.replicate 1000000 ()) 0
      (fun n _ => Costed.tick (Except.ok (n + 1) : Except Unit Nat) 1)
    (match result.value with | .ok n => n == 1000000 | .error _ => false) = true ∧
      result.cost = 3000000 := by
  native_decide

/-- Five successful entries and the first failing entry each cost three units.
The unvisited suffix contributes nothing to this fold's count. -/
example :
    let result := Costed.foldArrayExcept (Array.replicate 1000000 ()) 0
      (fun n _ => Costed.tick (if n == 5 then Except.error () else Except.ok (n + 1)) 1)
    (match result.value with | .error () => true | .ok _ => false) = true ∧
      result.cost = 18 := by
  native_decide

/-- The mapper writes one output cell per successful callback. -/
example :
    let result := mapArrayExceptCosted (Array.replicate 1000000 ())
      (fun _ => Costed.tick (Except.ok true : Except Unit Bool) 1)
    (match result.value with | .ok output => output.size == 1000000 | .error _ => false) =
      true ∧ result.cost = 5000000 := by
  native_decide

example :
    let result := mapArrayExceptCosted (#[] : Array Nat)
      (fun n => Costed.tick (Except.ok n : Except Nat Nat) 1)
    result.cost = 0 := by
  native_decide

/-- The first entry costs five units. The failing second entry costs four,
because it does not write an output. A later error must not replace it. -/
example :
    let result := mapArrayExceptCosted #[0, 1, 2]
      (fun n => Costed.tick (if n == 0 then Except.ok n else Except.error n) 1)
    (match result.value with | .error n => n == 1 | .ok _ => false) = true ∧
      result.cost = 9 := by
  native_decide

/-- Construction assigns source-order indices, including names whose spelling
does not match that order. An absent name must remain absent. -/
example :
    (match (buildNameIndexCosted #["z", "a", "m"]).value with
    | .error _ => false
    | .ok index => index.find? "z" == some 0 && index.find? "a" == some 1 &&
        index.find? "m" == some 2 && index.find? "absent" == none) = true := by
  native_decide

example : (buildNameIndexCosted #[]).cost = 1 := by native_decide

/-- String generation is outside the indexing call. This successful scan
checks a long traversal as well as the final source-order index. -/
example :
    let names := Array.ofFn (fun i : Fin 100000 => toString i.val)
    let result := buildNameIndexCosted names
    (match result.value with
      | .ok index => index.find? "99999" == some 99999
      | .error _ => false) = true ∧ result.cost = 600001 := by
  native_decide

/-- The second entry is already a duplicate. Input allocation precedes this
call; indexing reads two entries and tests the final result, for eleven units. -/
example :
    let result := buildNameIndexCosted (Array.replicate 1000000 "duplicate")
    (match result.value with | .error name => name == "duplicate" | .ok _ => false) =
      true ∧ result.cost = 11 := by
  native_decide

example :
    let result := buildNameIndexCosted #["x", "y", "y", "x"]
    (match result.value with | .error name => name == "y" | .ok _ => false) =
      true ∧ result.cost = 17 := by
  native_decide

/-- The standalone linear resolver returns the first duplicate's index. Its
count includes the final conversion from the scan result to an option. -/
example : nameIndexCosted? #["z", "a", "a"] "a" = ⟨some 1, 10⟩ := by native_decide

example : nameIndexCosted? #[] "missing" = ⟨none, 1⟩ := by native_decide

/-- Both early success and full failure use direct array traversal. The
supplied million-entry array is allocated before the measured call. -/
example :
    nameIndexCosted? (Array.replicate 1000000 "match") "match" = ⟨some 0, 5⟩ := by
  native_decide

example :
    nameIndexCosted? (Array.replicate 1000000 "other") "missing" = ⟨none, 5000001⟩ := by
  native_decide

/-- Scope expansion preserves source-fact order, then ascending world order,
for all five fact constructors. Nine outputs and five inputs cost 47 units. -/
example :
    let result := expandScopedFactsCosted 2 #[
      .unary .ex 3 .everywhere, .binary .inst 1 2 (.at 1),
      .ternary .distance 0 1 2 .everywhere,
      .tupleProjection 4 2 5 .everywhere,
      .derived (fun world => toString world) .everywhere]
    (match result.value.toList with
    | [.unary .ex 3 0, .unary .ex 3 1, .binary .inst 1 2 1,
       .ternary .distance 0 1 2 0, .ternary .distance 0 1 2 1,
       .tupleProjection 4 2 5 0, .tupleProjection 4 2 5 1,
       .derived "0", .derived "1"] => true
    | _ => false) = true ∧ result.cost = 47 := by
  native_decide

example :
    let result := expandScopedFactsCosted 0 #[.unary .ex 0 .everywhere]
    result.value.size = 0 ∧ result.cost = 4 := by native_decide

/-- Expansion does not validate raw world coordinates. An explicit scope
still emits its stated world when the declared world count is zero. -/
example :
    let result := expandScopedFactsCosted 0 #[.unary .ex 0 (.at 7)]
    (match result.value.toList with | [.unary .ex 0 7] => true | _ => false) =
      true ∧ result.cost = 7 := by native_decide

example : (expandScopedFactsCosted 3 #[]).cost = 0 := by native_decide

/-- A single everywhere fact exercises a million numeric-loop iterations and
output writes without a range array or a per-fact temporary output array. -/
example :
    let result := expandScopedFactsCosted 1000000 #[.unary .ex 0 .everywhere]
    result.value.size = 1000000 ∧ result.cost = 3000004 ∧
      (match result.value[999999]! with | .unary .ex 0 999999 => true | _ => false) =
        true := by native_decide

end LeanUfo.Test.Complexity.Traversal
