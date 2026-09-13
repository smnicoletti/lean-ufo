import LeanUfo.UFO.DSL.Compiler

/-!
# Source-resolution counts and first-error order

These examples check both the returned result and the operations executed to
reach it. An unresolved thing must stop the resolver before it looks up the
world. A family with unequal witness-array lengths must fail before resolving
any name. General value and upper-bound proofs are in `DSL.Compiler` and
`Complexity.Compiler`; these native tests check concrete execution cases.
-/

namespace LeanUfo.Test.Complexity.Resolution

open LeanUfo.UFO.DSL

private def things : NameIndex := ⟨(∅ : Std.HashMap String Nat).insert "x" 0⟩
private def worlds : NameIndex := ⟨(∅ : Std.HashMap String Nat).insert "w" 0⟩

-- Each resolution performs one abstract map query and tests whether it found
-- an index. Building the supplied index is outside this call.
example : resolveThingIndexedCosted things "x" = ⟨.ok 0, 2⟩ := by native_decide
example : resolveThingIndexedCosted things "missing" =
    ⟨.error (.unknownThing "missing"), 2⟩ := by native_decide
example : resolveWorldIndexedCosted worlds "missing" =
    ⟨.error (.unknownWorld "missing"), 2⟩ := by native_decide

example : resolveScopeIndexedCosted worlds .everywhere = ⟨.ok .everywhere, 1⟩ := by
  native_decide
example : resolveScopeIndexedCosted worlds (.at "w") = ⟨.ok (.at 0), 4⟩ := by
  native_decide
example : resolveScopeIndexedCosted worlds (.at "missing") =
    ⟨.error (.unknownWorld "missing"), 4⟩ := by native_decide

-- The unary fact costs a fact-kind test, a two-unit thing lookup, two
-- success/error tests, and either a one-unit or four-unit scope resolution.
example :
    let result := resolveNamedFactIndexedCosted worlds things
      (.unary .endurant "x" .everywhere)
    (match result.value with
      | .ok (.unary .endurant 0 .everywhere) => true
      | _ => false) = true ∧ result.cost = 6 := by
  native_decide

example :
    let result := resolveNamedFactIndexedCosted worlds things
      (.unary .endurant "x" (.at "w"))
    (match result.value with
      | .ok (.unary .endurant 0 (.at 0)) => true
      | _ => false) = true ∧ result.cost = 9 := by
  native_decide

example :
    let result := resolveNamedFactIndexedCosted worlds things
      (.unary .endurant "missingThing" (.at "missingWorld"))
    (match result.value with
      | .error (.unknownThing "missingThing") => true
      | _ => false) = true ∧ result.cost = 4 := by
  native_decide

-- Four thing references attain the single-fact bound. The generated
-- proposition stores resolved coordinates; rendering its string is a later pass.
example :
    let result := resolveNamedFactIndexedCosted worlds things
      (.derived (.quaternary "relation" "x" "x" "x" "x") (.at "w"))
    (match result.value with
      | .ok (.derived (.quaternary "relation" 0 0 0 0) (.at 0)) => true
      | _ => false) = true ∧ result.cost = 20 := by
  native_decide

example :
    let result := resolveNamedProductFamilyIndexedCosted things
      ⟨"missingDomain", "missingType", #["missingSlot"], #[]⟩
    result.value = .error (.productFamilyArityMismatch
      "missingDomain" "missingType" 1 0) ∧ result.cost = 2 := by
  native_decide

-- A successful family costs ten fixed operations plus six per witness slot.
-- Both dimension and type arrays contribute slots, even for repeated names.
example : resolveNamedProductFamilyIndexedCosted things ⟨"x", "x", #[], #[]⟩ =
    ⟨.ok ⟨0, 0, #[], #[]⟩, 10⟩ := by native_decide

example : resolveNamedProductFamilyIndexedCosted things
    ⟨"x", "x", #["x", "x"], #["x", "x"]⟩ =
    ⟨.ok ⟨0, 0, #[0, 0], #[0, 0]⟩, 34⟩ := by native_decide

example : resolveNamedProductFamilyIndexedCosted things
    ⟨"x", "x", #["missingDimension"], #["missingType"]⟩ =
    ⟨.error (.unknownThing "missingDimension"), 14⟩ := by native_decide

-- Empty compilation still tests stage results and computes eleven table-size
-- expressions: two index stages cost four, four outer tests cost four, and
-- the materialization/validation tail costs thirteen.
example :
    let result := compileModelSourceCosted { worlds := #[], things := #[] }
    (match result.value with
      | .ok compiled => compiled.ast.worldCount == 0 && compiled.ast.thingCount == 0
      | .error _ => false) = true ∧ result.cost = 21 := by
  native_decide

example :
    let result := compileModelSourceCosted
      { worlds := #["w", "w"], things := #["x", "x"] }
    (match result.value with
      | .error (.duplicateWorld "w") => true
      | _ => false) = true ∧ result.cost = 13 := by
  native_decide

example :
    let result := compileModelSourceCosted
      { worlds := #["w"], things := #["x", "x"] }
    (match result.value with
      | .error (.duplicateThing "x") => true
      | _ => false) = true ∧ result.cost = 22 := by
  native_decide

example :
    let result := compileModelSourceCosted
      { worlds := #["w"], things := #["x"], facts :=
          #[.unary .endurant "missingThing" (.at "missingWorld")] }
    (match result.value with
      | .error (.unknownThing "missingThing") => true
      | _ => false) = true ∧ result.cost = 26 := by
  native_decide

end LeanUfo.Test.Complexity.Resolution
