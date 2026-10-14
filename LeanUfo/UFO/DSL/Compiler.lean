import Lean
import LeanUfo.UFO.DSL.FiniteModel
import LeanUfo.UFO.DSL.Compiler.AST
import LeanUfo.UFO.DSL.Compiler.DerivedFacts
import LeanUfo.UFO.DSL.Compiler.ProductFamilies
import LeanUfo.UFO.DSL.Complexity.CostModel
import LeanUfo.UFO.DSL.Complexity.Closure
import LeanUfo.UFO.DSL.Complexity.Taxonomy

/-!
# Pure compiler core for the finite UFO DSL

This module separates the semantic DSL compiler from Lean command elaboration.
The parser in `Syntax.lean` is metaprogramming, but it only constructs named
facts and emits the final Lean declarations. The pipeline implemented by this
module and its `Compiler/` support modules is ordinary Lean code:

```text
ModelSource
  → name indices and resolved facts/product families
  → scope, taxonomy, and reflexive-specialization expansion
  → projection validation
  → ModelAST and FactTables
  → FiniteModel4
```

`compileModelSource` runs the counted source-to-table pipeline and discards
its cost. Finite-model construction is a subsequent step.
`Compiler/VerifiedModel.lean` proves the successful compiler result's
correspondence to that model. `Complexity/Certification.lean` composes its
construction cost with the certification workflow.

The trust boundary is:

* `Syntax.lean` is responsible for parsing concrete syntax and emitting Lean
  declarations;
* `Compiler/Fields.lean` and `Compiler/AST.lean` define the compiler vocabulary;
* this file is responsible for name resolution, scoped fact expansion, taxonomy
  expansion, reflexive-specialization expansion, table compilation, and
  finite-model construction;
* `FiniteModel.lean` is responsible for interpreting the tables as
  `UFOSignature4`;
* generated `certify` declarations are still checked by Lean as ordinary
  theorems.

## How to read the implementation

Each compiler pass consumes one explicit representation and produces the next.
This pass-by-pass layout is inspired by the verified-interpreter organization
in de Moura's `RadixExperiment`: executable code remains direct, while local
theorems relate adjacent representations. We borrow the proof organization, not
the radix-tree data structure.

**Name indexing** replaces source strings with finite numeric indices.
**Accumulator passes** build a result by updating one value while traversing an
input once. **Materialization** allocates the flat dense tables used for direct
runtime lookup. These techniques avoid repeated scans and make the charged
operations visible at their call sites.

Counted functions follow the cost-aware semantics of Niu et al. (POPL 2022)
and Haslbeck (2018): a `Costed α` contains the computed `α` and the accumulated
abstract cost. Production functions erase that field or have named
implementation-correspondence proofs. The remaining accounting obligations,
references, and limits of the unit-cost model are documented in
`docs/dsl/complexity.md`.
-/

namespace LeanUfo.UFO.DSL

/-- Scan the array until the first matching name. A visited entry charges an
iteration, read, string comparison, and Boolean test. A mismatch also advances
the index. The final result-tag test costs one unit. String comparison is an
abstract primitive here; its character-level work is outside this bound. -/
def nameIndexCosted? (xs : Array String) (x : String) : Complexity.Costed (Option Nat) :=
  Complexity.Costed.charge 1 <|
    (Complexity.Costed.foldArrayExcept xs 0 (fun index candidate =>
      if candidate == x then Complexity.Costed.tick (.error index) 2
      else Complexity.Costed.tick (.ok (index + 1)) 3)).map fun
        | .error index => some index
        | .ok _ => none

/-- Erasing the scan agrees with Lean's first-matching-index specification.
The list induction is a proof device; production does not construct a list. -/
theorem nameIndexCosted_value_eq_findIdx (xs : Array String) (x : String) :
    (nameIndexCosted? xs x).value = xs.findIdx? (· == x) := by
  have aux (ys : List String) (index : Nat) :
      (match (ys.foldlM (fun index candidate =>
        if candidate == x then Except.error index else Except.ok (index + 1)) index) with
        | .error found => some found | .ok _ => none) =
      (ys.findIdx? (· == x)).map (index + ·) := by
    induction ys generalizing index with
    | nil => simp [Pure.pure, Except.pure]
    | cons candidate rest ih =>
        cases h : (candidate == x) with
        | true =>
            simp only [List.foldlM_cons, List.findIdx?_cons, h, ↓reduceIte,
              Bind.bind, Except.bind, Option.map_some, Nat.add_zero]
        | false =>
            simp only [List.foldlM_cons, List.findIdx?_cons, h, Bool.false_eq_true,
              ↓reduceIte, Bind.bind, Except.bind, ih, Option.map_map]
            congr 1
            funext n
            dsimp
            omega
  simp only [nameIndexCosted?, Complexity.Costed.charge_value,
    Complexity.Costed.map_value, Complexity.Costed.foldArrayExcept_value]
  simpa [Complexity.Costed.tick, apply_ite, ← Array.foldlM_toList,
    ← List.findIdx?_toArray] using aux xs.toList 0

/-- Production name lookup is the erasure of the counted executable scan. -/
def nameIndex? (xs : Array String) (x : String) : Option Nat :=
  (nameIndexCosted? xs x).value

@[simp] theorem nameIndexCosted_value (xs : Array String) (x : String) :
    (nameIndexCosted? xs x).value = nameIndex? xs x := rfl

theorem nameIndexCosted_cost_le_size (xs : Array String) (x : String) :
    (nameIndexCosted? xs x).cost ≤ 5 * xs.size + 1 := by
  have bound := Complexity.Costed.foldArrayExcept_cost_le xs 0
    (fun index candidate => if candidate == x then Complexity.Costed.tick (.error index) 2
      else Complexity.Costed.tick (.ok (index + 1)) 3) 3 (by
        intro index candidate _
        split <;> simp [Complexity.Costed.tick])
  simpa [nameIndexCosted?, Nat.mul_comm, Nat.add_comm] using Nat.add_le_add_left bound 1

example : nameIndexCosted? #["a", "b", "c"] "b" = ⟨some 1, 10⟩ := by
  native_decide

example : nameIndexCosted? #["a", "b", "c"] "z" = ⟨none, 16⟩ := by
  native_decide

/--
Reusable source-name index. Each `HashMap` lookup/insert is one abstract map
operation; this interface does not claim a verified character-level or native
hash-table bound. These map primitives are included in the unit-cost sum.
Naming the assumed machine primitives follows the implementation-correspondence
discipline emphasized by Forster et al. (ITP 2021).
-/
structure NameIndex where
  entries : Std.HashMap String Nat := {}
deriving Inhabited

/--
Build the name index in source order, stopping at the first duplicate.
The accumulator stores the next numeric index and the map of preceding names.
Each visited name charges an array iteration and read, a map membership query,
and its Boolean test. A new name also charges insertion and index increment.
Converting the completed scan to an index or error charges one final test.
The direct array fold does not allocate a list before checking the first name.
-/
def buildNameIndexCosted (names : Array String) :
    Complexity.Costed (Except String NameIndex) :=
  Complexity.Costed.charge 1 <|
  (Complexity.Costed.foldArrayExcept names (0, ({} : Std.HashMap String Nat))
    fun (index, entries) name =>
      if entries.contains name then
        ⟨.error name, 2⟩
      else
        ⟨.ok (index + 1, entries.insert name index), 4⟩).map
    (Except.map fun (_, entries) => ⟨entries⟩)

def buildNameIndex (names : Array String) : Except String NameIndex :=
  (buildNameIndexCosted names).value

def NameIndex.findCosted (index : NameIndex) (name : String) :
    Complexity.Costed (Option Nat) :=
  .tick (index.entries[name]?) 1

def NameIndex.find? (index : NameIndex) (name : String) : Option Nat :=
  (index.findCosted name).value

@[simp] theorem buildNameIndexCosted_value (names : Array String) :
    (buildNameIndexCosted names).value = buildNameIndex names := rfl

/--
Erasure agrees with an ordinary left-to-right array fold: successful entries
receive consecutive indices, and a duplicate returns its name immediately.
The specification uses the same abstract map interface as the counted code.
-/
theorem buildNameIndexCosted_value_eq_foldlM (names : Array String) :
    (buildNameIndexCosted names).value =
      Except.map (fun (_, entries) => (⟨entries⟩ : NameIndex))
        (names.foldlM (fun (index, entries) name =>
          if entries.contains name then .error name
          else .ok (index + 1, entries.insert name index))
          (0, ({} : Std.HashMap String Nat))) := by
  simp only [buildNameIndexCosted, Complexity.Costed.map_value,
    Complexity.Costed.charge_value, Complexity.Costed.foldArrayExcept_value]
  congr 2
  funext state name
  split <;> rfl

/-- At most six units per name, including map primitives and traversal, plus
one final result-tag test. A duplicate costs four units within the scan. -/
theorem buildNameIndexCosted_cost_le (names : Array String) :
    (buildNameIndexCosted names).cost ≤ 6 * names.size + 1 := by
  have bound := Complexity.Costed.foldArrayExcept_cost_le names
    (0, ({} : Std.HashMap String Nat))
    (fun (index, entries) name => if entries.contains name then
      (⟨.error name, 2⟩ : Complexity.Costed (Except String (Nat × Std.HashMap String Nat)))
      else ⟨.ok (index + 1, entries.insert name index), 4⟩)
    4 (by
      intro state name _
      rcases state with ⟨index, entries⟩
      dsimp
      split <;> simp)
  simpa [buildNameIndexCosted, Nat.mul_comm, Nat.add_comm] using Nat.add_le_add_left bound 1

example : (buildNameIndexCosted #["w0", "w1", "w2"]).cost = 19 := by
  native_decide

example : (buildNameIndexCosted #["x", "y", "x", "unreached"]).cost = 17 := by
  native_decide

private def duplicateName? : Except String NameIndex → Option String
  | .error duplicate => some duplicate
  | .ok _ => none

example : duplicateName?
    (buildNameIndexCosted #["x", "y", "x", "unreached"]).value = some "x" := by
  native_decide

@[simp] theorem NameIndex.findCosted_value (index : NameIndex) (name : String) :
    (index.findCosted name).value = index.find? name := rfl

@[simp] theorem NameIndex.findCosted_cost (index : NameIndex) (name : String) :
    (index.findCosted name).cost = 1 := rfl

private def hasDuplicate? (xs : Array String) : Option String :=
  Id.run do
    let mut seen : Std.HashSet String := {}
    for x in xs do
      if seen.contains x then
        return some x
      seen := seen.insert x
    return none

/-- Check world names for duplicates. -/
def checkWorldNames (worlds : Array String) : Except ResolveError Unit :=
  match hasDuplicate? worlds with
  | some world => throw (.duplicateWorld world)
  | none => pure ()

/-- Check thing names for duplicates. -/
def checkThingNames (things : Array String) : Except ResolveError Unit :=
  match hasDuplicate? things with
  | some thing => throw (.duplicateThing thing)
  | none => pure ()

/-- Resolve a thing name to its finite index. -/
def resolveThing (things : Array String) (thing : String) : Except ResolveError Nat :=
  match nameIndex? things thing with
  | some idx => pure idx
  | none => throw (.unknownThing thing)

/-- Resolve a world name to its finite index. -/
def resolveWorld (worlds : Array String) (world : String) : Except ResolveError Nat :=
  match nameIndex? worlds world with
  | some idx => pure idx
  | none => throw (.unknownWorld world)

/-- Resolve a named scope to an indexed scope. -/
def resolveScope (worlds : Array String) : NamedFactScope → Except ResolveError FactScope
  | .everywhere => pure .everywhere
  | .at world => return .at (← resolveWorld worlds world)

def resolveThingIndexed (things : NameIndex) (thing : String) : Except ResolveError Nat :=
  match things.find? thing with
  | some idx => pure idx
  | none => throw (.unknownThing thing)

def resolveWorldIndexed (worlds : NameIndex) (world : String) : Except ResolveError Nat :=
  match worlds.find? world with
  | some idx => pure idx
  | none => throw (.unknownWorld world)

def resolveScopeIndexed (worlds : NameIndex) :
    NamedFactScope → Except ResolveError FactScope
  | .everywhere => pure .everywhere
  | .at world => return .at (← resolveWorldIndexed worlds world)

/-- Inspect whether the result is a success or an error before continuing.
This test costs one unit even when an error skips the continuation. -/
def exceptBindCosted
    (result : Complexity.Costed (Except ε α))
    (next : α → Complexity.Costed (Except ε β)) :
    Complexity.Costed (Except ε β) :=
  match result.value with
  | .error error => ⟨.error error, result.cost + 1⟩
  | .ok value =>
      let following := next value
      ⟨following.value, result.cost + 1 + following.cost⟩

theorem exceptBindCosted_cost_le_add
    (result : Complexity.Costed (Except ε α))
    (next : α → Complexity.Costed (Except ε β)) (left right : Nat)
    (hLeft : result.cost ≤ left) (hRight : ∀ value, (next value).cost ≤ right) :
    (exceptBindCosted result next).cost ≤ left + right + 1 := by
  cases hValue : result.value with
  | error error =>
      simp [exceptBindCosted, hValue]
      omega
  | ok value =>
      simp [exceptBindCosted, hValue]
      have hNext := hRight value
      omega

/-- Map directly into an array, preserving the first error. Each visited input
charges a loop iteration, a read, and an error-tag test. A successful result
also charges its output write. The callback supplies its own cost. -/
def mapArrayExceptCosted {β ε : Type u}
    (xs : Array α) (f : α → Complexity.Costed (Except ε β)) :
    Complexity.Costed (Except ε (Array β)) :=
  Complexity.Costed.foldArrayExcept xs (Array.emptyWithCapacity xs.size) fun output x =>
    let next := f x
    match next.value with
    | .error error => ⟨.error error, next.cost + 1⟩
    | .ok value => ⟨.ok (output.push value), next.cost + 2⟩

def mapArrayExcept
    (xs : Array α) (f : α → Complexity.Costed (Except ε β)) :
    Except ε (Array β) :=
  (mapArrayExceptCosted xs f).value

@[simp] theorem mapArrayExceptCosted_value
    (xs : Array α) (f : α → Complexity.Costed (Except ε β)) :
    (mapArrayExceptCosted xs f).value = mapArrayExcept xs f := rfl

/-- The executable accumulator has the standard array map's order, result, and
first-error behavior. The list representation used in proofs is not allocated
by the executable mapper. -/
theorem mapArrayExceptCosted_value_eq_mapM
    (xs : Array α) (f : α → Complexity.Costed (Except ε β)) :
    (mapArrayExceptCosted xs f).value = xs.mapM (fun x => (f x).value) := by
  simp only [mapArrayExceptCosted, Complexity.Costed.foldArrayExcept_value,
    Array.mapM_eq_foldlM]
  congr 1
  funext output x
  cases h : (f x).value <;> rfl

theorem mapArrayExceptCosted_cost_le
    (xs : Array α) (f : α → Complexity.Costed (Except ε β)) (perItem : Nat)
    (hCost : ∀ x ∈ xs, (f x).cost ≤ perItem) :
    (mapArrayExceptCosted xs f).cost ≤ xs.size * (perItem + 4) := by
  apply Complexity.Costed.foldArrayExcept_cost_le xs _ _ (perItem + 2)
  intro output x hx
  have hc := hCost x hx
  cases h : (f x).value <;> simp [h] <;> omega

private theorem mapListExcept_preserves_weight {β ε : Type u}
    (f : α → Except ε β)
    (sourceWeight : α → Nat) (resultWeight : β → Nat)
    (hItem : ∀ x y, f x = .ok y → resultWeight y = sourceWeight x) :
    ∀ (xs : List α) (ys : List β),
      xs.mapM f = .ok ys →
      (ys.map resultWeight).sum = (xs.map sourceWeight).sum := by
  intro xs
  induction xs with
  | nil =>
      intro ys h
      simp [Pure.pure, Except.pure] at h
      subst ys
      simp
  | cons x xs ih =>
      intro ys h
      cases hHead : f x with
      | error error => simp [List.mapM_cons, hHead, Bind.bind, Except.bind] at h
      | ok y =>
          cases hTail : xs.mapM f with
          | error error => simp [List.mapM_cons, hHead, hTail, Bind.bind, Except.bind] at h
          | ok tail =>
              simp [List.mapM_cons, hHead, hTail, Bind.bind, Except.bind,
                Pure.pure, Except.pure] at h
              subst ys
              simp [hItem x y hHead, ih tail hTail]

theorem mapArrayExceptCosted_preserves_weight
    (xs : Array α) (f : α → Complexity.Costed (Except ε β))
    (sourceWeight : α → Nat) (resultWeight : β → Nat)
    (hItem : ∀ x y, (f x).value = .ok y → resultWeight y = sourceWeight x)
    (ys : Array β)
    (h : (mapArrayExceptCosted xs f).value = .ok ys) :
    (ys.toList.map resultWeight).sum =
      (xs.toList.map sourceWeight).sum := by
  rw [mapArrayExceptCosted_value_eq_mapM, Array.mapM_eq_mapM_toList] at h
  cases hMapped : xs.toList.mapM (fun x => (f x).value) with
  | error error => simp [hMapped] at h
  | ok values =>
      simp [hMapped] at h
      subst ys
      simpa using mapListExcept_preserves_weight
        (fun x => (f x).value) sourceWeight resultWeight hItem xs.toList values hMapped

private theorem mapListExcept_preserves_maxWeight {β ε : Type u}
    (f : α → Except ε β)
    (sourceWeight : α → Nat) (resultWeight : β → Nat)
    (hItem : ∀ x y, f x = .ok y → resultWeight y = sourceWeight x) :
    ∀ (xs : List α) (ys : List β) (initial : Nat),
      xs.mapM f = .ok ys →
      (ys.map resultWeight).foldl max initial =
        (xs.map sourceWeight).foldl max initial := by
  intro xs
  induction xs with
  | nil =>
      intro ys initial h
      simp [Pure.pure, Except.pure] at h
      subst ys
      simp
  | cons x xs ih =>
      intro ys initial h
      cases hHead : f x with
      | error error => simp [List.mapM_cons, hHead, Bind.bind, Except.bind] at h
      | ok y =>
          cases hTail : xs.mapM f with
          | error error => simp [List.mapM_cons, hHead, hTail, Bind.bind, Except.bind] at h
          | ok tail =>
              simp [List.mapM_cons, hHead, hTail, Bind.bind, Except.bind,
                Pure.pure, Except.pure] at h
              subst ys
              simp only [List.map_cons, List.foldl_cons]
              rw [hItem x y hHead]
              exact ih tail (max initial (sourceWeight x)) hTail

theorem mapArrayExceptCosted_preserves_maxWeight
    (xs : Array α) (f : α → Complexity.Costed (Except ε β))
    (sourceWeight : α → Nat) (resultWeight : β → Nat)
    (hItem : ∀ x y, (f x).value = .ok y → resultWeight y = sourceWeight x)
    (ys : Array β)
    (h : (mapArrayExceptCosted xs f).value = .ok ys) :
    (ys.toList.map resultWeight).foldl max 0 =
      (xs.toList.map sourceWeight).foldl max 0 := by
  rw [mapArrayExceptCosted_value_eq_mapM, Array.mapM_eq_mapM_toList] at h
  cases hMapped : xs.toList.mapM (fun x => (f x).value) with
  | error error => simp [hMapped] at h
  | ok values =>
      simp [hMapped] at h
      subst ys
      simpa using mapListExcept_preserves_maxWeight
        (fun x => (f x).value) sourceWeight resultWeight hItem xs.toList values 0 hMapped
theorem mapArrayExceptCosted_ok_size
    (xs : Array α) (f : α → Complexity.Costed (Except ε β))
    (ys : Array β)
    (h : (mapArrayExceptCosted xs f).value = .ok ys) :
    ys.size = xs.size := by
  have weights := mapArrayExceptCosted_preserves_weight xs f
    (fun _ => 1) (fun _ => 1) (by intro _ _ _; rfl) ys h
  have sourceOnes : ∀ source : List α,
      (source.map (fun _ => 1)).sum = source.length := by
    intro source
    induction source <;> simp_all [Nat.add_comm]
  have resultOnes : ∀ result : List β,
      (result.map (fun _ => 1)).sum = result.length := by
    intro result
    induction result <;> simp_all [Nat.add_comm]
  rw [resultOnes, sourceOnes] at weights
  simpa using weights

/-- One abstract map query and one test for a present or absent index. -/
def resolveThingIndexedCosted (things : NameIndex) (thing : String) :
    Complexity.Costed (Except ResolveError Nat) :=
  Complexity.Costed.charge 1 <|
  (things.findCosted thing).map fun
    | some idx => .ok idx
    | none => .error (.unknownThing thing)

def resolveWorldIndexedCosted (worlds : NameIndex) (world : String) :
    Complexity.Costed (Except ResolveError Nat) :=
  Complexity.Costed.charge 1 <|
  (worlds.findCosted world).map fun
    | some idx => .ok idx
    | none => .error (.unknownWorld world)

/-- The scope test always runs. A named world adds its lookup and a test of
whether that lookup succeeded before constructing the resolved scope. -/
def resolveScopeIndexedCosted (worlds : NameIndex) :
    NamedFactScope → Complexity.Costed (Except ResolveError FactScope)
  | .everywhere => Complexity.Costed.tick (.ok .everywhere) 1
  | .at world =>
      Complexity.Costed.charge 2 <|
        (resolveWorldIndexedCosted worlds world).map (Except.map FactScope.at)

@[simp] theorem resolveThingIndexedCosted_value
    (things : NameIndex) (thing : String) :
    (resolveThingIndexedCosted things thing).value =
      resolveThingIndexed things thing := rfl

@[simp] theorem resolveWorldIndexedCosted_value
    (worlds : NameIndex) (world : String) :
    (resolveWorldIndexedCosted worlds world).value =
      resolveWorldIndexed worlds world := rfl

@[simp] theorem resolveScopeIndexedCosted_value
    (worlds : NameIndex) (scope : NamedFactScope) :
    (resolveScopeIndexedCosted worlds scope).value =
      resolveScopeIndexed worlds scope := by
  cases scope <;> rfl

/--
Merge a parent model source with a child extension.

For now, extensions may add things, facts, and product-family witnesses, but not
worlds. This avoids deciding whether parent `everywhere` facts should be
re-expanded over child-added worlds; that semantics is not yet defined.
-/
def extendModelSource (parent child : ModelSource) : Except ResolveError ModelSource := do
  if !child.worlds.isEmpty then
    throw .extensionAddsWorlds
  if parent.deriveRelations != child.deriveRelations then
    throw .extensionDisablesDerivations
  let things := parent.things ++ child.things
  checkThingNames things
  pure
    { worlds := parent.worlds
      things := things
      facts := parent.facts ++ child.facts
      productFamilies := parent.productFamilies ++ child.productFamilies
      deriveRelations := parent.deriveRelations && child.deriveRelations }

private def resolveDerivedFact
    (things : Array String) (fact : NamedDerivedFact) :
    Except ResolveError ResolvedDerivedFact := do
  match fact with
  | .unary field thing =>
      let thingIdx ← resolveThing things thing
      pure (.unary field thingIdx)
  | .binary field left right =>
      let leftIdx ← resolveThing things left
      let rightIdx ← resolveThing things right
      pure (.binary field leftIdx rightIdx)
  | .ternary field first second third =>
      let firstIdx ← resolveThing things first
      let secondIdx ← resolveThing things second
      let thirdIdx ← resolveThing things third
      pure (.ternary field firstIdx secondIdx thirdIdx)
  | .quaternary field first second third fourth =>
      let firstIdx ← resolveThing things first
      let secondIdx ← resolveThing things second
      let thirdIdx ← resolveThing things third
      let fourthIdx ← resolveThing things fourth
      pure (.quaternary field firstIdx secondIdx thirdIdx fourthIdx)

/-- Resolve one named scoped fact to an indexed scoped fact. -/
def resolveNamedFact
    (worlds things : Array String) : NamedScopedFact → Except ResolveError ScopedCompiledFact
  | .unary field thing scope => do
      let thingIdx ← resolveThing things thing
      let scope ← resolveScope worlds scope
      pure (.unary field thingIdx scope)
  | .binary field left right scope => do
      let leftIdx ← resolveThing things left
      let rightIdx ← resolveThing things right
      let scope ← resolveScope worlds scope
      pure (.binary field leftIdx rightIdx scope)
  | .ternary field first second third scope => do
      let firstIdx ← resolveThing things first
      let secondIdx ← resolveThing things second
      let thirdIdx ← resolveThing things third
      let scope ← resolveScope worlds scope
      pure (.ternary field firstIdx secondIdx thirdIdx scope)
  | .tupleProjection tuple index result scope => do
      let tupleIdx ← resolveThing things tuple
      let resultIdx ← resolveThing things result
      let scope ← resolveScope worlds scope
      pure (.tupleProjection tupleIdx index resultIdx scope)
  | .derived fact scope => do
      let assertion ← resolveDerivedFact things fact
      let scope ← resolveScope worlds scope
      pure (.derived assertion scope)

private def resolveDerivedFactIndexed
    (things : NameIndex) (fact : NamedDerivedFact) :
    Except ResolveError ResolvedDerivedFact := do
  match fact with
  | .unary field thing =>
      let thingIdx ← resolveThingIndexed things thing
      pure (.unary field thingIdx)
  | .binary field left right =>
      let leftIdx ← resolveThingIndexed things left
      let rightIdx ← resolveThingIndexed things right
      pure (.binary field leftIdx rightIdx)
  | .ternary field first second third =>
      let firstIdx ← resolveThingIndexed things first
      let secondIdx ← resolveThingIndexed things second
      let thirdIdx ← resolveThingIndexed things third
      pure (.ternary field firstIdx secondIdx thirdIdx)
  | .quaternary field first second third fourth =>
      let firstIdx ← resolveThingIndexed things first
      let secondIdx ← resolveThingIndexed things second
      let thirdIdx ← resolveThingIndexed things third
      let fourthIdx ← resolveThingIndexed things fourth
      pure (.quaternary field firstIdx secondIdx thirdIdx fourthIdx)

/-- Uninstrumented specification for the name-resolution equivalence proof. -/
private def resolveNamedFactIndexedSpecification
    (worlds things : NameIndex) : NamedScopedFact → Except ResolveError ScopedCompiledFact
  | .unary field thing scope => do
      pure (.unary field (← resolveThingIndexed things thing)
        (← resolveScopeIndexed worlds scope))
  | .binary field left right scope => do
      pure (.binary field (← resolveThingIndexed things left)
        (← resolveThingIndexed things right) (← resolveScopeIndexed worlds scope))
  | .ternary field first second third scope => do
      pure (.ternary field (← resolveThingIndexed things first)
        (← resolveThingIndexed things second) (← resolveThingIndexed things third)
        (← resolveScopeIndexed worlds scope))
  | .tupleProjection tuple index result scope => do
      pure (.tupleProjection (← resolveThingIndexed things tuple) index
        (← resolveThingIndexed things result) (← resolveScopeIndexed worlds scope))
  | .derived fact scope => do
      -- Resolve coordinates before world expansion renders the proposition.
      let assertion ← resolveDerivedFactIndexed things fact
      pure (.derived assertion (← resolveScopeIndexed worlds scope))

private def resolveDerivedFactIndexedCosted
    (things : NameIndex) (fact : NamedDerivedFact) :
    Complexity.Costed (Except ResolveError ResolvedDerivedFact) :=
  Complexity.Costed.charge 1 <| match fact with
  | .unary field thing =>
      exceptBindCosted (resolveThingIndexedCosted things thing) fun thingIdx =>
        Complexity.Costed.pure (.ok (.unary field thingIdx))
  | .binary field left right =>
      exceptBindCosted (resolveThingIndexedCosted things left) fun leftIdx =>
      exceptBindCosted (resolveThingIndexedCosted things right) fun rightIdx =>
        Complexity.Costed.pure (.ok (.binary field leftIdx rightIdx))
  | .ternary field first second third =>
      exceptBindCosted (resolveThingIndexedCosted things first) fun firstIdx =>
      exceptBindCosted (resolveThingIndexedCosted things second) fun secondIdx =>
      exceptBindCosted (resolveThingIndexedCosted things third) fun thirdIdx =>
        Complexity.Costed.pure (.ok (.ternary field firstIdx secondIdx thirdIdx))
  | .quaternary field first second third fourth =>
      exceptBindCosted (resolveThingIndexedCosted things first) fun firstIdx =>
      exceptBindCosted (resolveThingIndexedCosted things second) fun secondIdx =>
      exceptBindCosted (resolveThingIndexedCosted things third) fun thirdIdx =>
      exceptBindCosted (resolveThingIndexedCosted things fourth) fun fourthIdx =>
        Complexity.Costed.pure (.ok (.quaternary field firstIdx secondIdx thirdIdx fourthIdx))

/-- Count the fact-kind test, reference lookups, scope resolution, and tests
between those stages. A failed reference stops all later lookups. -/
def resolveNamedFactIndexedCosted
    (worlds things : NameIndex) (fact : NamedScopedFact) :
    Complexity.Costed (Except ResolveError ScopedCompiledFact) :=
  Complexity.Costed.charge 1 <| match fact with
  | .unary field thing scope =>
      exceptBindCosted (resolveThingIndexedCosted things thing) fun thingIdx =>
      exceptBindCosted (resolveScopeIndexedCosted worlds scope) fun resolvedScope =>
        Complexity.Costed.pure (.ok (.unary field thingIdx resolvedScope))
  | .binary field left right scope =>
      exceptBindCosted (resolveThingIndexedCosted things left) fun leftIdx =>
      exceptBindCosted (resolveThingIndexedCosted things right) fun rightIdx =>
      exceptBindCosted (resolveScopeIndexedCosted worlds scope) fun resolvedScope =>
        Complexity.Costed.pure (.ok (.binary field leftIdx rightIdx resolvedScope))
  | .ternary field first second third scope =>
      exceptBindCosted (resolveThingIndexedCosted things first) fun firstIdx =>
      exceptBindCosted (resolveThingIndexedCosted things second) fun secondIdx =>
      exceptBindCosted (resolveThingIndexedCosted things third) fun thirdIdx =>
      exceptBindCosted (resolveScopeIndexedCosted worlds scope) fun resolvedScope =>
        Complexity.Costed.pure (.ok (.ternary field firstIdx secondIdx thirdIdx resolvedScope))
  | .tupleProjection tuple index result scope =>
      exceptBindCosted (resolveThingIndexedCosted things tuple) fun tupleIdx =>
      exceptBindCosted (resolveThingIndexedCosted things result) fun resultIdx =>
      exceptBindCosted (resolveScopeIndexedCosted worlds scope) fun resolvedScope =>
        Complexity.Costed.pure (.ok (.tupleProjection tupleIdx index resultIdx resolvedScope))
  | .derived fact scope =>
      exceptBindCosted (resolveDerivedFactIndexedCosted things fact) fun assertion =>
      exceptBindCosted (resolveScopeIndexedCosted worlds scope) fun resolvedScope =>
        Complexity.Costed.pure (.ok (.derived assertion resolvedScope))

/-- Production resolution is the erasure of the counted, short-circuiting pass. -/
def resolveNamedFactIndexed
    (worlds things : NameIndex) (fact : NamedScopedFact) :
    Except ResolveError ScopedCompiledFact :=
  (resolveNamedFactIndexedCosted worlds things fact).value

theorem resolveNamedFactIndexedCosted_cost_le
    (worlds things : NameIndex) (fact : NamedScopedFact) :
    (resolveNamedFactIndexedCosted worlds things fact).cost ≤ 20 := by
  cases fact with
  | unary field thing scope =>
      cases scope <;>
        simp [resolveNamedFactIndexedCosted, exceptBindCosted,
          resolveThingIndexedCosted, resolveScopeIndexedCosted,
          resolveWorldIndexedCosted, NameIndex.findCosted,
          Complexity.Costed.map] <;> repeat' first | split | simp_all
  | binary field left right scope =>
      cases scope <;>
        simp [resolveNamedFactIndexedCosted, exceptBindCosted,
          resolveThingIndexedCosted, resolveScopeIndexedCosted,
          resolveWorldIndexedCosted, NameIndex.findCosted,
          Complexity.Costed.map] <;> repeat' first | split | simp_all
  | ternary field first second third scope =>
      cases scope <;>
        simp [resolveNamedFactIndexedCosted, exceptBindCosted,
          resolveThingIndexedCosted, resolveScopeIndexedCosted,
          resolveWorldIndexedCosted, NameIndex.findCosted,
          Complexity.Costed.map] <;> repeat' first | split | simp_all
  | tupleProjection tuple index result scope =>
      cases scope <;>
        simp [resolveNamedFactIndexedCosted, exceptBindCosted,
          resolveThingIndexedCosted, resolveScopeIndexedCosted,
          resolveWorldIndexedCosted, NameIndex.findCosted,
          Complexity.Costed.map] <;> repeat' first | split | simp_all
  | derived fact scope =>
      cases fact <;> cases scope <;>
        simp [resolveNamedFactIndexedCosted, resolveDerivedFactIndexedCosted,
          exceptBindCosted, resolveThingIndexedCosted,
          resolveScopeIndexedCosted, resolveWorldIndexedCosted,
          NameIndex.findCosted, Complexity.Costed.map] <;>
        repeat' first | split | simp_all

theorem resolveNamedFactsIndexedCosted_cost_le
    (worlds things : NameIndex) (facts : Array NamedScopedFact) :
    (mapArrayExceptCosted facts
      (resolveNamedFactIndexedCosted worlds things)).cost ≤ 24 * facts.size := by
  have h := mapArrayExceptCosted_cost_le facts
    (resolveNamedFactIndexedCosted worlds things) 20
    (by
      intro fact _
      exact resolveNamedFactIndexedCosted_cost_le worlds things fact)
  omega

@[simp] theorem resolveNamedFactIndexed_eq_costed_value
    (worlds things : NameIndex) (fact : NamedScopedFact) :
    resolveNamedFactIndexed worlds things fact =
      (resolveNamedFactIndexedCosted worlds things fact).value := rfl

/-- Resolve all named facts after checking uniqueness of world and thing names. -/
def resolveNamedFacts
    (worlds things : Array String) (facts : Array NamedScopedFact) :
    Except ResolveError (Array ScopedCompiledFact) := do
  checkWorldNames worlds
  checkThingNames things
  facts.mapM (resolveNamedFact worlds things)

/-- Resolve one named product-family witness. -/
def resolveNamedProductFamily
    (things : Array String) (family : NamedProductFamily) :
    Except ResolveError ProductFamilySpec := do
  if family.dimensionThings.size != family.typeThings.size then
    throw (.productFamilyArityMismatch
      family.domain family.qualityType family.dimensionThings.size family.typeThings.size)
  let domain ← resolveThing things family.domain
  let qualityType ← resolveThing things family.qualityType
  let dimensionThings ← family.dimensionThings.mapM (resolveThing things)
  let typeThings ← family.typeThings.mapM (resolveThing things)
  pure { domain, qualityType, dimensionThings, typeThings }

private def resolveNamedProductFamilyIndexedSpecification
    (things : NameIndex) (family : NamedProductFamily) :
    Except ResolveError ProductFamilySpec := do
  if family.dimensionThings.size != family.typeThings.size then
    throw (.productFamilyArityMismatch
      family.domain family.qualityType family.dimensionThings.size family.typeThings.size)
  let domain ← resolveThingIndexed things family.domain
  let qualityType ← resolveThingIndexed things family.qualityType
  let dimensionThings ← family.dimensionThings.mapM (resolveThingIndexed things)
  let typeThings ← family.typeThings.mapM (resolveThingIndexed things)
  pure { domain, qualityType, dimensionThings, typeThings }

/-- Compare witness-array lengths before resolving any name. On success,
resolve domain, quality type, dimensions, and types in that order. Every
lookup and intervening success/error test contributes to the count. -/
def resolveNamedProductFamilyIndexedCosted
    (things : NameIndex) (family : NamedProductFamily) :
    Complexity.Costed (Except ResolveError ProductFamilySpec) :=
  Complexity.Costed.charge 2 <| if family.dimensionThings.size != family.typeThings.size then
    .pure (.error (.productFamilyArityMismatch
      family.domain family.qualityType family.dimensionThings.size
        family.typeThings.size))
  else
    exceptBindCosted (resolveThingIndexedCosted things family.domain) fun domain =>
    exceptBindCosted (resolveThingIndexedCosted things family.qualityType) fun qualityType =>
    exceptBindCosted
      (mapArrayExceptCosted family.dimensionThings
        (resolveThingIndexedCosted things)) fun dimensionThings =>
    exceptBindCosted
      (mapArrayExceptCosted family.typeThings
        (resolveThingIndexedCosted things)) fun typeThings =>
      Complexity.Costed.pure (.ok
        { domain, qualityType, dimensionThings, typeThings })

def resolveNamedProductFamilyIndexed
    (things : NameIndex) (family : NamedProductFamily) :
    Except ResolveError ProductFamilySpec :=
  (resolveNamedProductFamilyIndexedCosted things family).value

def NamedProductFamily.slotCount (family : NamedProductFamily) : Nat :=
  family.dimensionThings.size + family.typeThings.size

theorem resolveNamedProductFamilyIndexedCosted_cost_le
    (things : NameIndex) (family : NamedProductFamily) :
    (resolveNamedProductFamilyIndexedCosted things family).cost ≤
      6 * (family.dimensionThings.size + family.typeThings.size) + 10 := by
  unfold resolveNamedProductFamilyIndexedCosted
  simp only [Complexity.Costed.charge_cost]
  split
  · simp
  · refine (Nat.add_le_add_left (exceptBindCosted_cost_le_add _ _ 2
        (6 * (family.dimensionThings.size + family.typeThings.size) + 5)
        (by rfl) ?_) 2).trans (by omega)
    intro domain
    refine (exceptBindCosted_cost_le_add _ _ 2
        (6 * (family.dimensionThings.size + family.typeThings.size) + 2)
        (by rfl) ?_).trans (by omega)
    intro qualityType
    refine (exceptBindCosted_cost_le_add _ _
        (6 * family.dimensionThings.size)
        (6 * family.typeThings.size + 1) ?_ ?_).trans (by omega)
    · simpa [Nat.mul_comm] using
        (mapArrayExceptCosted_cost_le family.dimensionThings
          (resolveThingIndexedCosted things) 2 (by intro name _; rfl))
    · intro dimensionThings
      apply exceptBindCosted_cost_le_add _ _
          (6 * family.typeThings.size) 0
      · simpa [Nat.mul_comm] using
          (mapArrayExceptCosted_cost_le family.typeThings
            (resolveThingIndexedCosted things) 2 (by intro name _; rfl))
      · intro typeThings
        simp

/--
Batch product-family resolution is bounded by the concrete witness slots in
the source.  The extra factor comes from applying the generic short-circuiting
array traversal to a non-uniform per-family bound; no unexecuted suffix is
charged after a failure.
-/
theorem resolveNamedProductFamiliesIndexedCosted_cost_le
    (things : NameIndex) (families : Array NamedProductFamily) :
    (mapArrayExceptCosted families
      (resolveNamedProductFamilyIndexedCosted things)).cost ≤
      families.size *
        (6 * (families.toList.map NamedProductFamily.slotCount).sum + 14) := by
  apply mapArrayExceptCosted_cost_le
  intro family hFamily
  have hOwn : family.slotCount ≤
      (families.toList.map NamedProductFamily.slotCount).sum := by
    have memberLe : ∀ (xs : List NamedProductFamily), family ∈ xs →
        family.slotCount ≤
          (xs.map NamedProductFamily.slotCount).sum := by
      intro xs hx
      induction xs with
      | nil => simp at hx
      | cons head tail ih =>
          simp only [List.mem_cons] at hx
          simp only [List.map_cons, List.sum_cons]
          rcases hx with rfl | hx
          · omega
          · have := ih hx
            omega
    exact memberLe families.toList (by simpa using hFamily)
  have hCost := resolveNamedProductFamilyIndexedCosted_cost_le things family
  unfold NamedProductFamily.slotCount at hOwn ⊢
  omega

@[simp] theorem resolveNamedProductFamilyIndexed_eq_costed_value
    (things : NameIndex) (family : NamedProductFamily) :
    resolveNamedProductFamilyIndexed things family =
      (resolveNamedProductFamilyIndexedCosted things family).value := rfl

/-- Resolve product-family witnesses after thing-name checks. -/
def resolveNamedProductFamilies
    (things : Array String) (families : Array NamedProductFamily) :
    Except ResolveError (Array ProductFamilySpec) := do
  checkThingNames things
  families.mapM (resolveNamedProductFamily things)

/--
Resolved model AST used by the syntax frontend.

The AST stores `Nat` indices rather than names. Name lookup and
duplicate-name checks happen in the pure resolver above, before scoped facts are
expanded into ordinary `CompiledFact`s.
-/
structure ModelAST where
  worldCount : Nat
  thingCount : Nat
  facts : Array CompiledFact := #[]
  productFamilies : Array ProductFamilySpec := #[]
  deriving Repr, Inhabited

/--
Accumulated finite table data before construction of a `FiniteModel4`.

The maps support diagnostics. The lookup closures give kernel reduction a
compact view for generated certificate proofs. Verified model construction
uses the typed dense arrays in native execution. Raw table interpretation
keeps the sparse meaning unless the caller supplies a correspondence proof.
-/
structure FactTables where
  unary : Std.HashMap String (Array (Nat × Nat)) := {}
  binary : Std.HashMap String (Array (Nat × Nat × Nat)) := {}
  ternary : Std.HashMap String (Array (Nat × Nat × Nat × Nat)) := {}
  tupleProjection : Array (Nat × Nat × Nat × Nat) := #[]
  productFamilies : Array ProductFamilySpec := #[]
  unaryLookup : String → Nat → Nat → Bool := fun _ _ _ => false
  binaryLookup : String → Nat → Nat → Nat → Bool := fun _ _ _ _ => false
  ternaryLookup : String → Nat → Nat → Nat → Nat → Bool := fun _ _ _ _ _ => false
  tupleProjectionLookup : Nat → Nat → Nat → Nat → Bool := fun _ _ _ _ => false
  tupleProjectionResult? : Nat → Nat → Nat → Option Nat := fun _ _ _ => none
  /-
  Dense typed tables are the native checker representation. The sparse maps
  remain inspectable compiler artifacts for diagnostics. `initializeDense`
  initializes every dense cell and the cost model charges each cell.
  -/
  denseWorldCount : Nat := 0
  denseThingCount : Nat := 0
  denseProjectionArity : Nat := 0
  unaryCells : Array Bool := #[]
  binaryCells : Array Bool := #[]
  ternaryCells : Array Bool := #[]
  projectionCells : Array (Option Nat) := #[]
  inherenceClosures : Array (Array Bool) := #[]
  inherenceNextHops : Array (Array (Option Nat)) := #[]
  derivedProps : Array String := #[]
  deriving Inhabited

structure CompiledModelSource where
  scopedFacts : Array ScopedCompiledFact
  productFamilies : Array ProductFamilySpec
  expandedFacts : Array CompiledFact
  ast : ModelAST
  tables : FactTables
  deriving Inhabited

def addUnary (tables : FactTables) (field : String) (x w : Nat) : FactTables :=
  { tables with
    unary := tables.unary.insert field ((tables.unary.getD field #[]).push (x, w))
    unaryLookup := fun field' x' w' =>
      tables.unaryLookup field' x' w' || (field' == field && x' == x && w' == w) }


/--
Insert a unary fact together with its deterministic taxonomy ancestors.

Duplicate insertions are harmless semantically, but the local `seen` set keeps
generated Boolean tables smaller and avoids cycles if the taxonomy map is
extended later.
-/
partial def addUnaryWithTaxonomyAux
    (tables : FactTables) (field : String) (x w : Nat)
    (seen : Std.HashSet String) : FactTables × Std.HashSet String :=
  if seen.contains field then
    (tables, seen)
  else
    let tables := addUnary tables field x w
    let seen := seen.insert field
    unaryTaxonomyParents field |>.foldl
      (fun (acc : FactTables × Std.HashSet String) parent =>
        addUnaryWithTaxonomyAux acc.1 parent x w acc.2)
      (tables, seen)

/-- Add a user-written unary fact and all deterministic taxonomy consequences. -/
def addUnaryWithTaxonomy (tables : FactTables) (field : String) (x w : Nat) : FactTables :=
  (addUnaryWithTaxonomyAux tables field x w {}).1

/-- Insert one binary table fact into both the inspectable store and executable lookup. -/
def addBinary (tables : FactTables) (field : String) (x y w : Nat) : FactTables :=
  { tables with
    binary := tables.binary.insert field ((tables.binary.getD field #[]).push (x, y, w))
    binaryLookup := fun field' x' y' w' =>
      tables.binaryLookup field' x' y' w' ||
        (field' == field && x' == x && y' == y && w' == w) }

/-- Insert one ternary table fact into both the inspectable store and executable lookup. -/
def addTernary (tables : FactTables) (field : String) (x y z w : Nat) : FactTables :=
  { tables with
    ternary := tables.ternary.insert field ((tables.ternary.getD field #[]).push (x, y, z, w))
    ternaryLookup := fun field' x' y' z' w' =>
      tables.ternaryLookup field' x' y' z' w' ||
        (field' == field && x' == x && y' == y && z' == z && w' == w) }

/-- Insert one tuple-projection fact into both the inspectable store and executable lookup. -/
def addTupleProjection (tables : FactTables) (tuple index result w : Nat) : FactTables :=
  { tables with
    tupleProjection := tables.tupleProjection.push (tuple, index, result, w)
    tupleProjectionLookup := fun tuple' index' result' w' =>
      tables.tupleProjectionLookup tuple' index' result' w' ||
        (tuple' == tuple && index' == index && result' == result && w' == w)
    tupleProjectionResult? := fun tuple' index' w' =>
      if tuple' == tuple && index' == index && w' == w then some result
      else tables.tupleProjectionResult? tuple' index' w' }

def addProductFamily (tables : FactTables) (family : ProductFamilySpec) : FactTables :=
  { tables with productFamilies := tables.productFamilies.push family }

/-- Record an asserted derived-relation proposition for generated checking. -/
def addDerivedProp (tables : FactTables) (prop : String) : FactTables :=
  { tables with derivedProps := tables.derivedProps.push prop }

/-- Concrete row-major coordinate used by production unary tables.
Kept public so table-correctness proofs can refer to the executed encoding. -/
def unaryCoordinate (thing worldCount world : Nat) : Nat :=
  thing * worldCount + world

/-- Concrete row-major coordinate used by production binary tables. -/
def binaryCoordinate (thingCount worldCount left right world : Nat) : Nat :=
  (left * thingCount + right) * worldCount + world

/-- Concrete row-major coordinate used by production ternary tables. -/
def ternaryCoordinate
    (thingCount worldCount first second third world : Nat) : Nat :=
  ((first * thingCount + second) * thingCount + third) * worldCount + world

/-- Concrete row-major coordinate used by production projection tables. -/
def projectionCoordinate
    (maxArity worldCount tuple index world : Nat) : Nat :=
  (tuple * maxArity + index) * worldCount + world

/-- Initialize explicit tables with counted loops. Size calculations use
eleven multiplications in total. Each cell then costs one loop iteration and
one write; capacity allocation itself is outside the unit-cost model. -/
def FactTables.initializeDenseCosted
    (tables : FactTables) (worldCount thingCount maxProjectionArity : Nat) :
    Complexity.Costed FactTables := do
  let unaryCount ← Complexity.Costed.tick (UnaryField.count * thingCount * worldCount) 2
  let binaryCount ← Complexity.Costed.tick (BinaryField.count * thingCount * thingCount * worldCount) 3
  let ternaryCount ← Complexity.Costed.tick
    (TernaryField.count * thingCount * thingCount * thingCount * worldCount) 4
  let projectionCount ← Complexity.Costed.tick (thingCount * maxProjectionArity * worldCount) 2
  let unaryCells ← Complexity.Costed.replicateArray unaryCount false
  let binaryCells ← Complexity.Costed.replicateArray binaryCount false
  let ternaryCells ← Complexity.Costed.replicateArray ternaryCount false
  let projectionCells ← Complexity.Costed.replicateArray projectionCount none
  pure { tables with
    denseWorldCount := worldCount
    denseThingCount := thingCount
    denseProjectionArity := maxProjectionArity
    unaryCells, binaryCells, ternaryCells, projectionCells }

/-- Compact production initialization used by generated certificates. -/
def FactTables.initializeDense
    (tables : FactTables) (worldCount thingCount maxProjectionArity : Nat) : FactTables :=
  let unaryCount := UnaryField.count * thingCount * worldCount
  let binaryCount := BinaryField.count * thingCount * thingCount * worldCount
  let ternaryCount := TernaryField.count * thingCount * thingCount * thingCount * worldCount
  let projectionCount := thingCount * maxProjectionArity * worldCount
  { tables with
    denseWorldCount := worldCount
    denseThingCount := thingCount
    denseProjectionArity := maxProjectionArity
    unaryCells := Array.replicate unaryCount false
    binaryCells := Array.replicate binaryCount false
    ternaryCells := Array.replicate ternaryCount false
    projectionCells := Array.replicate projectionCount none }

@[simp] theorem FactTables.initializeDenseCosted_value
    (tables : FactTables) (worldCount thingCount maxProjectionArity : Nat) :
    (tables.initializeDenseCosted worldCount thingCount maxProjectionArity).value =
      tables.initializeDense worldCount thingCount maxProjectionArity := by
  simp [FactTables.initializeDenseCosted, FactTables.initializeDense,
    Bind.bind, Pure.pure, Complexity.Costed.bind, Complexity.Costed.pure]

@[simp] theorem FactTables.initializeDenseCosted_cost
    (tables : FactTables) (worldCount thingCount maxProjectionArity : Nat) :
    (tables.initializeDenseCosted worldCount thingCount maxProjectionArity).cost =
      2 * (UnaryField.count * thingCount * worldCount +
      BinaryField.count * thingCount * thingCount * worldCount +
      TernaryField.count * thingCount * thingCount * thingCount * worldCount +
      thingCount * maxProjectionArity * worldCount) + 11 := by
  simp [FactTables.initializeDenseCosted, Bind.bind, Pure.pure,
    Complexity.Costed.bind, Complexity.Costed.pure, Nat.mul_add]
  omega

private def FactTables.initializeDenseErased
    (tables : FactTables) (worldCount thingCount maxProjectionArity : Nat) : FactTables :=
  (tables.initializeDenseCosted worldCount thingCount maxProjectionArity).value

/-- Native initialization uses the counted constructor. The proved function
equality preserves the compact kernel definition used by certificates. -/
@[csimp] theorem FactTables.initializeDense_eq_erased :
    FactTables.initializeDense = FactTables.initializeDenseErased := by
  funext tables worldCount thingCount maxProjectionArity
  exact (tables.initializeDenseCosted_value worldCount thingCount maxProjectionArity).symm

-- Empty tables still compute their four sizes. Positive dimensions charge
-- two operations per initialized cell, in addition to those eleven products.
example : (FactTables.initializeDenseCosted {} 0 0 0).cost = 11 := by native_decide
example : (FactTables.initializeDenseCosted {} 1 1 1).cost =
    2 * (UnaryField.count + BinaryField.count + TernaryField.count + 1) + 11 := by
  native_decide

/-- Write one compiled fact to its typed flat table. -/
def FactTables.writeDenseFact (tables : FactTables) : CompiledFact → FactTables
  | .unary field thing world =>
      let coordinate := unaryCoordinate thing tables.denseWorldCount world
      let index := field.index * (tables.denseThingCount * tables.denseWorldCount) + coordinate
      { tables with unaryCells := tables.unaryCells.set! index true }
  | .binary field left right world =>
      let coordinate := binaryCoordinate tables.denseThingCount tables.denseWorldCount
        left right world
      let width := tables.denseThingCount * tables.denseThingCount * tables.denseWorldCount
      let index := field.index * width + coordinate
      { tables with binaryCells := tables.binaryCells.set! index true }
  | .ternary field first second third world =>
      let coordinate := ternaryCoordinate tables.denseThingCount tables.denseWorldCount
        first second third world
      let width := tables.denseThingCount ^ 3 * tables.denseWorldCount
      let index := field.index * width + coordinate
      { tables with ternaryCells := tables.ternaryCells.set! index true }
  | .tupleProjection tuple index result world =>
      let coordinate := projectionCoordinate tables.denseProjectionArity
        tables.denseWorldCount tuple index world
      { tables with projectionCells := tables.projectionCells.set! coordinate (some result) }
  | .derived _ => tables

/-- Count row-major coordinate arithmetic, the fixed field-index lookup, and
the checked array write. Each tag dispatch costs one unit. `set!` is one
checked-write primitive under the array interface; allocator and native
instruction costs remain outside the model. The straight-line arithmetic
blocks charge each addition and multiplication, as in the counted initializer. -/
def FactTables.writeDenseFactCosted (tables : FactTables) (fact : CompiledFact) :
    Complexity.Costed FactTables :=
  Complexity.Costed.charge 1 <| match fact with
  | .unary field thing world => do
      let coordinate ← Complexity.Costed.tick
        (unaryCoordinate thing tables.denseWorldCount world) 2
      let width ← Complexity.Costed.tick (tables.denseThingCount * tables.denseWorldCount) 1
      let fieldIndex ← Complexity.Costed.tick field.index 1
      let index ← Complexity.Costed.tick (fieldIndex * width + coordinate) 2
      let cells ← Complexity.Costed.tick (tables.unaryCells.set! index true) 1
      pure { tables with unaryCells := cells }
  | .binary field left right world => do
      let coordinate ← Complexity.Costed.tick
        (binaryCoordinate tables.denseThingCount tables.denseWorldCount left right world) 4
      let width ← Complexity.Costed.tick
        (tables.denseThingCount * tables.denseThingCount * tables.denseWorldCount) 2
      let fieldIndex ← Complexity.Costed.tick field.index 1
      let index ← Complexity.Costed.tick (fieldIndex * width + coordinate) 2
      let cells ← Complexity.Costed.tick (tables.binaryCells.set! index true) 1
      pure { tables with binaryCells := cells }
  | .ternary field first second third world => do
      let coordinate ← Complexity.Costed.tick
        (ternaryCoordinate tables.denseThingCount tables.denseWorldCount
          first second third world) 6
      let width ← Complexity.Costed.tick
        (tables.denseThingCount * tables.denseThingCount * tables.denseThingCount *
          tables.denseWorldCount) 3
      let fieldIndex ← Complexity.Costed.tick field.index 1
      let index ← Complexity.Costed.tick (fieldIndex * width + coordinate) 2
      let cells ← Complexity.Costed.tick (tables.ternaryCells.set! index true) 1
      pure { tables with ternaryCells := cells }
  | .tupleProjection tuple index result world => do
      let coordinate ← Complexity.Costed.tick
        (projectionCoordinate tables.denseProjectionArity tables.denseWorldCount
          tuple index world) 4
      let cells ← Complexity.Costed.tick
        (tables.projectionCells.set! coordinate (some result)) 1
      pure { tables with projectionCells := cells }
  | .derived _ => .pure tables

@[simp] theorem FactTables.writeDenseFactCosted_value
    (tables : FactTables) (fact : CompiledFact) :
    (tables.writeDenseFactCosted fact).value = tables.writeDenseFact fact := by
  cases fact <;> simp [writeDenseFactCosted, writeDenseFact, Bind.bind, Pure.pure,
    Complexity.Costed.bind, Complexity.Costed.tick, Complexity.Costed.pure, Nat.pow_succ,
    Nat.mul_assoc]

/-- Ternary insertion has the largest straight-line block: fourteen operations. -/
theorem FactTables.writeDenseFactCosted_cost_le (tables : FactTables) (fact : CompiledFact) :
    (tables.writeDenseFactCosted fact).cost ≤ 14 := by
  cases fact <;> simp [writeDenseFactCosted, Bind.bind, Pure.pure,
    Complexity.Costed.bind, Complexity.Costed.tick, Complexity.Costed.pure]

private def FactTables.writeDenseFactErased (tables : FactTables) (fact : CompiledFact) :
    FactTables := (tables.writeDenseFactCosted fact).value

/-- Native insertion uses the counted core's value. The kernel retains the
compact definition used by certificate proofs; the equality holds for all
tables and coordinates, without a well-formedness assumption. -/
@[csimp] theorem FactTables.writeDenseFact_eq_erased :
    FactTables.writeDenseFact = FactTables.writeDenseFactErased := by
  funext tables fact
  exact (tables.writeDenseFactCosted_value fact).symm

theorem FactTables.foldl_writeDenseFact_denseWorldCount
    (facts : Array CompiledFact) (tables : FactTables) :
    (facts.foldl FactTables.writeDenseFact tables).denseWorldCount =
      tables.denseWorldCount := by
  rw [← Array.foldl_toList]
  induction facts.toList generalizing tables with
  | nil => rfl
  | cons fact facts ih =>
      simp only [List.foldl_cons, ih]
      cases fact <;> rfl

theorem FactTables.foldl_writeDenseFact_denseThingCount
    (facts : Array CompiledFact) (tables : FactTables) :
    (facts.foldl FactTables.writeDenseFact tables).denseThingCount =
      tables.denseThingCount := by
  rw [← Array.foldl_toList]
  induction facts.toList generalizing tables with
  | nil => rfl
  | cons fact facts ih =>
      simp only [List.foldl_cons, ih]
      cases fact <;> rfl

theorem FactTables.foldl_writeDenseFact_denseProjectionArity
    (facts : Array CompiledFact) (tables : FactTables) :
    (facts.foldl FactTables.writeDenseFact tables).denseProjectionArity =
      tables.denseProjectionArity := by
  rw [← Array.foldl_toList]
  induction facts.toList generalizing tables with
  | nil => rfl
  | cons fact facts ih =>
      simp only [List.foldl_cons, ih]
      cases fact <;> rfl

theorem FactTables.foldl_writeDenseFact_unaryLookup
    (facts : Array CompiledFact) (tables : FactTables) :
    (facts.foldl FactTables.writeDenseFact tables).unaryLookup =
      tables.unaryLookup := by
  rw [← Array.foldl_toList]
  induction facts.toList generalizing tables with
  | nil => rfl
  | cons fact facts ih =>
      simp only [List.foldl_cons, ih]
      cases fact <;> rfl

theorem FactTables.foldl_writeDenseFact_binaryLookup
    (facts : Array CompiledFact) (tables : FactTables) :
    (facts.foldl FactTables.writeDenseFact tables).binaryLookup =
      tables.binaryLookup := by
  rw [← Array.foldl_toList]
  induction facts.toList generalizing tables with
  | nil => rfl
  | cons fact facts ih =>
      simp only [List.foldl_cons, ih]
      cases fact <;> rfl

theorem FactTables.foldl_writeDenseFact_ternaryLookup
    (facts : Array CompiledFact) (tables : FactTables) :
    (facts.foldl FactTables.writeDenseFact tables).ternaryLookup =
      tables.ternaryLookup := by
  rw [← Array.foldl_toList]
  induction facts.toList generalizing tables with
  | nil => rfl
  | cons fact facts ih =>
      simp only [List.foldl_cons, ih]
      cases fact <;> rfl

theorem FactTables.foldl_writeDenseFact_tupleProjectionLookup
    (facts : Array CompiledFact) (tables : FactTables) :
    (facts.foldl FactTables.writeDenseFact tables).tupleProjectionLookup =
      tables.tupleProjectionLookup := by
  rw [← Array.foldl_toList]
  induction facts.toList generalizing tables with
  | nil => rfl
  | cons fact facts ih =>
      simp only [List.foldl_cons, ih]
      cases fact <;> rfl

theorem FactTables.foldl_writeDenseFact_tupleProjectionResult?
    (facts : Array CompiledFact) (tables : FactTables) :
    (facts.foldl FactTables.writeDenseFact tables).tupleProjectionResult? =
      tables.tupleProjectionResult? := by
  rw [← Array.foldl_toList]
  induction facts.toList generalizing tables with
  | nil => rfl
  | cons fact facts ih =>
      simp only [List.foldl_cons, ih]
      cases fact <;> rfl

/-- Shared dense binary read for finite relation queries and closure edges.
Natural coordinates permit the same checked read at both boundaries. The
eleven operations are two width products, four coordinate operations, field
selection, a product and sum for flat indexing, a checked read, and an option
test. Invalid coordinates retain the checked-array behavior. -/
@[inline] def FactTables.binaryCellCosted (tables : FactTables) (field : BinaryField)
    (left right world : Nat) : Complexity.Costed Bool := do
  let width ← Complexity.Costed.tick
    (tables.denseThingCount * tables.denseThingCount * tables.denseWorldCount) 2
  let coordinate ← Complexity.Costed.tick
    (binaryCoordinate tables.denseThingCount tables.denseWorldCount left right world) 4
  let fieldIndex ← Complexity.Costed.tick field.index 1
  let index ← Complexity.Costed.tick (fieldIndex * width + coordinate) 2
  let cell ← Complexity.Costed.tick tables.binaryCells[index]? 1
  Complexity.Costed.tick (cell.getD false) 1

@[simp] theorem FactTables.binaryCellCosted_cost (tables : FactTables) (field : BinaryField)
    (left right world : Nat) :
    (tables.binaryCellCosted field left right world).cost = 11 := rfl

def FactTables.inherenceEdgeAt (tables : FactTables) (world : Nat)
    (left right : Fin tables.denseThingCount) : Bool :=
  let width := tables.denseThingCount * tables.denseThingCount * tables.denseWorldCount
  let coordinate := binaryCoordinate tables.denseThingCount tables.denseWorldCount
    left.val right.val world
  tables.binaryCells[BinaryField.inheresIn.index * width + coordinate]?.getD false

/-- The closure callback executes the same counted binary read as typed model
queries. A diagonal closure cell does not call it because reflexivity already
determines that cell's value. -/
def FactTables.inherenceEdgeAtCosted (tables : FactTables) (world : Nat)
    (left right : Fin tables.denseThingCount) : Complexity.Costed Bool :=
  tables.binaryCellCosted .inheresIn left.val right.val world

@[simp] theorem FactTables.inherenceEdgeAtCosted_value (tables : FactTables) (world : Nat)
    (left right : Fin tables.denseThingCount) :
    (tables.inherenceEdgeAtCosted world left right).value = tables.inherenceEdgeAt world left right := rfl

structure InherenceClosureData where
  reachable : Array Bool
  nextHop : Array (Option Nat)
deriving Repr, Inhabited

/-- Build one row-major closure and its first-hop evidence in one counted pass. -/
def FactTables.inherenceClosureAtCosted
    (tables : FactTables) (world : Nat) : Complexity.Costed InherenceClosureData := do
  let closure ← Complexity.warshallStateEvalCosted tables.denseThingCount
    (tables.inherenceEdgeAtCosted world)
  let reachable ← Complexity.matrixToArrayCosted closure.reachable Complexity.Costed.pure
  let nextHop ← Complexity.matrixToArrayCosted closure.nextHop
    (fun hop => Complexity.Costed.tick (hop.map Fin.val))
  pure { reachable, nextHop }

@[simp] theorem FactTables.inherenceClosureAtCosted_value
    (tables : FactTables) (world : Nat) :
    (tables.inherenceClosureAtCosted world).value =
      let closure := Complexity.warshallState tables.denseThingCount (tables.inherenceEdgeAt world)
      { reachable := closure.reachable.flatten.toArray
        nextHop := closure.nextHop.flatten.toArray.map (Option.map Fin.val) } := by
  simp [FactTables.inherenceClosureAtCosted, Bind.bind, Pure.pure,
    Complexity.Costed.bind, Complexity.Costed.pure]

theorem FactTables.inherenceClosureAtCosted_cost_le
    (tables : FactTables) (world : Nat) :
    (tables.inherenceClosureAtCosted world).cost ≤
      23 * tables.denseThingCount ^ 3 + 48 * tables.denseThingCount ^ 2 +
        5 * tables.denseThingCount := by
  let closure := Complexity.warshallStateEvalCosted tables.denseThingCount (tables.inherenceEdgeAtCosted world)
  have hc := Complexity.warshallStateEvalCosted_cost_le tables.denseThingCount
    (tables.inherenceEdgeAtCosted world) 11 (by intro i j; exact Nat.le_refl 11)
  have hr := Complexity.matrixToArrayCosted_cost_le closure.value.reachable
    Complexity.Costed.pure 0 (by intro x; simp)
  have hn := Complexity.matrixToArrayCosted_cost_le closure.value.nextHop
    (fun hop => Complexity.Costed.tick (hop.map Fin.val)) 1 (by intro x; simp)
  change closure.cost ≤ _ at hc
  change closure.cost + (_ + (_ + 0)) ≤ _
  dsimp only [closure] at hc hr hn ⊢
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.mul_one, Nat.mul_assoc, Nat.mul_comm] at hc hr hn ⊢
  simp only [← Nat.mul_assoc] at hc hr hn ⊢
  omega

/-- Every stored coordinate denotes the proved reachability recurrence. -/
theorem FactTables.inherenceClosureAtCosted_lookup
    (tables : FactTables) (world : Nat)
    (source target : Fin tables.denseThingCount) :
    (tables.inherenceClosureAtCosted world).value.reachable[
        Complexity.matrixIndex tables.denseThingCount source.val target.val]?.getD false =
      Complexity.reachableVia
        (tables.inherenceEdgeAt world)
        (List.finRange tables.denseThingCount) source target := by
  rw [FactTables.inherenceClosureAtCosted_value]
  rw [Complexity.flatten_toArray_getElem?_matrixIndex]
  simp only [Option.getD_some]
  exact Complexity.warshallMatrix_get _ _ _ _

structure InherenceClosureTables where
  reachable : Array (Array Bool)
  nextHop : Array (Array (Option Nat))
deriving Repr, Inhabited

/-- Compute one deterministic Warshall matrix per world from dense inherence. -/
private def FactTables.buildInherenceClosuresCosted
    (tables : FactTables) : Complexity.Costed InherenceClosureTables :=
  Id.run do
    let mut closures := #[]
    let mut nextHops := #[]
    let mut cost := 0
    for world in [:tables.denseWorldCount] do
      /-
      Store the erasure of the same sized matrix whose recurrence is proved in
      `Complexity.Closure`; there is no second, extensionally assumed closure
      routine. This follows the pass-correspondence pattern used by de Moura's
      RadixExperiment and the concrete-machine discipline of Forster et al.
      -/
      let closure := tables.inherenceClosureAtCosted world
      closures := closures.push closure.value.reachable
      nextHops := nextHops.push closure.value.nextHop
      cost := cost + closure.cost + 3
    return ⟨⟨closures, nextHops⟩, cost⟩

private def FactTables.buildInherenceClosures (tables : FactTables) : InherenceClosureTables :=
  Id.run do
    let mut closures := #[]
    let mut nextHops := #[]
    for world in [:tables.denseWorldCount] do
      let closure := Complexity.warshallState tables.denseThingCount
        (tables.inherenceEdgeAt world)
      closures := closures.push closure.reachable.flatten.toArray
      nextHops := nextHops.push
        (closure.nextHop.flatten.toArray.map (Option.map Fin.val))
    return ⟨closures, nextHops⟩

private theorem foldl_snd_const_add
    (xs : List α) (initial : β × Nat) (step : β → α → β) (charge : Nat) :
    (xs.foldl (fun state x => (step state.1 x, state.2 + charge)) initial).2 =
      initial.2 + xs.length * charge := by
  induction xs generalizing initial with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons, ih]
      simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.succ_mul]

private theorem foldl_snd_snd_add_le
    (xs : List α) (initial : β × γ × Nat)
    (step₁ : β → α → β) (step₂ : γ → α → γ) (charge : α → Nat)
    (bound : Nat) (h : ∀ x, charge x ≤ bound) :
    (xs.foldl (fun state x =>
      (step₁ state.1 x, step₂ state.2.1 x, state.2.2 + charge x)) initial).2.2 ≤
      initial.2.2 + xs.length * bound := by
  induction xs generalizing initial with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons, List.length_cons, Nat.succ_mul]
      have hr := ih (step₁ initial.1 x, step₂ initial.2.1 x, initial.2.2 + charge x)
      have hx := h x
      dsimp only at hr
      omega

/-- Adding a cost accumulator does not change either value accumulator. -/
private theorem foldl_pair_eq_costedTriple
    (xs : List α) (initial₁ : β) (initial₂ : γ) (initialCost : Nat)
    (step₁ : β → α → β) (step₂ : γ → α → γ)
    (costStep : Nat → α → Nat) :
    let counted := xs.foldl (fun state x =>
      (step₁ state.1 x, step₂ state.2.1 x, costStep state.2.2 x))
      (initial₁, initial₂, initialCost)
    let plain := xs.foldl (fun state x =>
      (step₁ state.1 x, step₂ state.2 x)) (initial₁, initial₂)
    counted.1 = plain.1 ∧ counted.2.1 = plain.2 := by
  induction xs generalizing initial₁ initial₂ initialCost with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      exact ih (step₁ initial₁ x) (step₂ initial₂ x) (costStep initialCost x)

@[simp] theorem FactTables.buildInherenceClosuresCosted_value (tables : FactTables) :
    (tables.buildInherenceClosuresCosted).value = tables.buildInherenceClosures := by
  let reach := fun world =>
    (Complexity.warshallState tables.denseThingCount
      (tables.inherenceEdgeAt world)).reachable.flatten.toArray
  let hops := fun world =>
    (Complexity.warshallState tables.denseThingCount
      (tables.inherenceEdgeAt world)).nextHop.flatten.toArray.map
        (Option.map Fin.val)
  have h := foldl_pair_eq_costedTriple
    (List.range' 0 tables.denseWorldCount)
    (#[] : Array (Array Bool)) (#[] : Array (Array (Option Nat))) 0
    (fun closures world => closures.push (reach world))
    (fun nextHops world => nextHops.push (hops world))
    (fun cost world => cost + (tables.inherenceClosureAtCosted world).cost + 3)
  simpa [FactTables.buildInherenceClosuresCosted,
    FactTables.buildInherenceClosures, reach, hops] using h

private def FactTables.buildInherenceClosuresErased (tables : FactTables) : InherenceClosureTables :=
  tables.buildInherenceClosuresCosted.value

/-- The compiler executes the counted closure and conversion loops. The
unconditional rewrite proof lets certificate reduction retain the compact
definition without relying on an unchecked native replacement. -/
@[csimp] theorem FactTables.buildInherenceClosures_eq_erased :
    FactTables.buildInherenceClosures = FactTables.buildInherenceClosuresErased := by
  funext tables
  exact tables.buildInherenceClosuresCosted_value.symm

theorem FactTables.buildInherenceClosuresCosted_cost_le (tables : FactTables) :
    (tables.buildInherenceClosuresCosted).cost ≤
      tables.denseWorldCount *
        (23 * tables.denseThingCount ^ 3 + 48 * tables.denseThingCount ^ 2 +
          5 * tables.denseThingCount + 3) := by
  let bound := 23 * tables.denseThingCount ^ 3 + 48 * tables.denseThingCount ^ 2 +
    5 * tables.denseThingCount + 3
  let produce := fun world => (tables.inherenceClosureAtCosted world).value
  have h := foldl_snd_snd_add_le (List.range' 0 tables.denseWorldCount)
    (#[], #[], 0)
    (fun closures world => closures.push (produce world).reachable)
    (fun nextHops world => nextHops.push (produce world).nextHop)
    (fun world => (tables.inherenceClosureAtCosted world).cost + 3) bound
    (fun world => Nat.add_le_add_right (tables.inherenceClosureAtCosted_cost_le world) 3)
  simpa [FactTables.buildInherenceClosuresCosted, produce, bound,
    Nat.mul_comm, Nat.add_assoc] using h

def projectionArityOfFacts (facts : Array CompiledFact) : Nat :=
  facts.foldl (fun arity fact => max arity fact.projectionArity) 0

/-- The arity scan charges fact dispatch, a successor for projection indices,
and the maximum comparison. The array fold charges traversal and reads. -/
def projectionArityOfFactsCosted (facts : Array CompiledFact) : Complexity.Costed Nat :=
  Complexity.Costed.foldArray facts 0 fun arity fact =>
    let extracted : Complexity.Costed Nat := match fact with
      | .tupleProjection _ index _ _ => .tick (index + 1) 2
      | _ => .tick 0 1
    extracted.bind fun next => .tick (max arity next)

@[simp] theorem projectionArityOfFactsCosted_value (facts : Array CompiledFact) :
    (projectionArityOfFactsCosted facts).value = projectionArityOfFacts facts := by
  simp only [projectionArityOfFactsCosted, Complexity.Costed.foldArray_value,
    Complexity.Costed.bind_value, Complexity.Costed.tick_value, projectionArityOfFacts]
  congr 1
  funext arity fact
  cases fact <;> rfl

private def projectionArityOfFactsErased (facts : Array CompiledFact) : Nat :=
  (projectionArityOfFactsCosted facts).value

/-- Dense-table sizing executes the same counted arity scan as validation.
The compact fold remains available to kernel reduction. -/
@[csimp] theorem projectionArityOfFacts_eq_erased :
    projectionArityOfFacts = projectionArityOfFactsErased := by
  funext facts
  exact (projectionArityOfFactsCosted_value facts).symm

theorem projectionArityOfFactsCosted_cost_le (facts : Array CompiledFact) :
    (projectionArityOfFactsCosted facts).cost ≤ 5 * facts.size := by
  calc
    _ ≤ facts.size * (3 + 2) := Complexity.Costed.foldArray_cost_le facts 0 _ 3 (by
      intro arity fact _
      cases fact <;> simp [Complexity.Costed.bind, Complexity.Costed.tick])
    _ = 5 * facts.size := by omega

def projectionArityOfScopedFacts (facts : Array ScopedCompiledFact) : Nat :=
  facts.foldl (fun arity fact => max arity fact.projectionArity) 0

def projectionArityOfNamedFacts (facts : Array NamedScopedFact) : Nat :=
  facts.foldl (fun arity fact => max arity fact.projectionArity) 0

private theorem foldl_map_maxWeight
    (weight : α → Nat) (xs : List α) (initial : Nat) :
    (xs.map weight).foldl max initial =
      xs.foldl (fun current x => max current (weight x)) initial := by
  induction xs generalizing initial with
  | nil => simp
  | cons x xs ih => simp [ih]

private theorem initial_le_foldl_maxWeight
    (weight : α → Nat) (xs : List α) (initial : Nat) :
    initial ≤ (xs.map weight).foldl max initial := by
  induction xs generalizing initial with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.foldl_cons]
      exact le_trans (le_max_left _ _) (ih _)

private theorem weight_le_foldl_max_of_mem
    (weight : α → Nat) (x : α) (xs : List α) (initial : Nat)
    (hx : x ∈ xs) :
    weight x ≤ (xs.map weight).foldl max initial := by
  induction xs generalizing initial with
  | nil => simp at hx
  | cons head tail ih =>
      simp only [List.mem_cons] at hx
      simp only [List.map_cons, List.foldl_cons]
      rcases hx with hEq | hx
      · subst x
        have initialLe : max initial (weight head) ≤
            (tail.map weight).foldl max (max initial (weight head)) :=
          initial_le_foldl_maxWeight weight tail _
        exact le_trans (le_max_right _ _) initialLe
      · exact ih (max initial (weight head)) hx

theorem ScopedCompiledFact.projectionArity_le_of_mem
    (fact : ScopedCompiledFact) (facts : Array ScopedCompiledFact)
    (h : fact ∈ facts) :
    fact.projectionArity ≤ projectionArityOfScopedFacts facts := by
  unfold projectionArityOfScopedFacts
  rw [← Array.foldl_toList]
  rw [← foldl_map_maxWeight]
  exact weight_le_foldl_max_of_mem _ fact facts.toList 0 (by simpa using h)

theorem CompiledFact.projectionArity_le_of_mem
    (fact : CompiledFact) (facts : Array CompiledFact)
    (h : fact ∈ facts) :
    fact.projectionArity ≤ projectionArityOfFacts facts := by
  unfold projectionArityOfFacts
  rw [← Array.foldl_toList]
  rw [← foldl_map_maxWeight]
  exact weight_le_foldl_max_of_mem _ fact facts.toList 0 (by simpa using h)

theorem NamedScopedFact.projectionArity_le_of_mem
    (fact : NamedScopedFact) (facts : Array NamedScopedFact)
    (h : fact ∈ facts) :
    fact.projectionArity ≤ projectionArityOfNamedFacts facts := by
  unfold projectionArityOfNamedFacts
  rw [← Array.foldl_toList]
  rw [← foldl_map_maxWeight]
  exact weight_le_foldl_max_of_mem _ fact facts.toList 0 (by simpa using h)

@[simp] theorem projectionArityOfFacts_push
    (facts : Array CompiledFact) (fact : CompiledFact) :
    projectionArityOfFacts (facts.push fact) =
      max (projectionArityOfFacts facts) fact.projectionArity := by
  simp [projectionArityOfFacts]

theorem projectionArityOfFacts_le (facts : Array CompiledFact) (bound : Nat)
    (hFact : ∀ fact ∈ facts, fact.projectionArity ≤ bound) :
    projectionArityOfFacts facts ≤ bound := by
  unfold projectionArityOfFacts
  rw [← Array.foldl_toList]
  have listBound : ∀ (xs : List CompiledFact) (initial : Nat),
      (∀ fact ∈ xs, fact.projectionArity ≤ bound) → initial ≤ bound →
      xs.foldl (fun arity fact => max arity fact.projectionArity) initial ≤
        bound := by
    intro xs
    induction xs with
    | nil => simp
    | cons fact facts ih =>
        intro initial hMembers hInitial
        simp only [List.foldl_cons]
        apply ih
        · intro tailFact hTail
          exact hMembers tailFact (by simp [hTail])
        · exact max_le hInitial (hMembers fact (by simp))
  exact listBound facts.toList 0 (by simpa using hFact) (Nat.zero_le _)

/--
Uninstrumented specification of projection validation. It fixes the first
conflict and its error payload, and accepts identical duplicate facts. The
production entry point below erases the counted implementation instead.
-/
private def validateTupleProjectionsSpec
    (worldCount thingCount : Nat) (facts : Array CompiledFact) : Except ResolveError Unit := do
  let maxArity := projectionArityOfFacts facts
  let mut cells : Array (Option Nat) :=
    Array.replicate (thingCount * maxArity * worldCount) none
  for fact in facts do
    match fact with
    | .tupleProjection tuple index result world =>
        let coordinate := projectionCoordinate maxArity worldCount tuple index world
        match cells[coordinate]? with
        | some none => cells := cells.set! coordinate (some result)
        | some (some firstResult) =>
            if firstResult != result then
              throw (.conflictingTupleProjection tuple index world firstResult result)
        | none =>
            throw (.conflictingTupleProjection tuple index world result result)
    | _ => pure ()

/-- Validate one fact. Projection coordinates use four arithmetic operations.
The lookup charges its bounds check and read. Separate case charges account
for the fact tag and both option tags; writes and inequality tests are counted
only on their executed branches. -/
private def validateProjectionStepCosted (maxArity worldCount : Nat)
    (cells : Array (Option Nat)) (fact : CompiledFact) :
    Complexity.Costed (Except ResolveError (Array (Option Nat))) :=
  Complexity.Costed.charge 1 <| match fact with
  | .tupleProjection tuple index result world =>
      let coordinate := projectionCoordinate maxArity worldCount tuple index world
      Complexity.Costed.charge 4 <|
        (Complexity.Costed.tick cells[coordinate]? 2).bind fun found =>
          Complexity.Costed.charge 1 <| match found with
          | none => .pure (.error (.conflictingTupleProjection tuple index world result result))
          | some entry => Complexity.Costed.charge 1 <| match entry with
            | none => .tick (.ok (cells.set! coordinate (some result))) 2
            | some firstResult =>
                Complexity.Costed.branch (.tick (firstResult != result))
                  (fun _ => .pure (.error (.conflictingTupleProjection tuple index world firstResult result)))
                  (fun _ => .pure (.ok cells))
  | _ => .pure (.ok cells)

private def validateProjectionStep (maxArity worldCount : Nat)
    (cells : Array (Option Nat)) (fact : CompiledFact) : Except ResolveError (Array (Option Nat)) :=
  match fact with
  | .tupleProjection tuple index result world =>
      let coordinate := projectionCoordinate maxArity worldCount tuple index world
      match cells[coordinate]? with
      | some none => .ok (cells.set! coordinate (some result))
      | some (some firstResult) =>
          if firstResult != result then
            .error (.conflictingTupleProjection tuple index world firstResult result)
          else .ok cells
      | none => .error (.conflictingTupleProjection tuple index world result result)
  | _ => .ok cells

@[simp] private theorem validateProjectionStepCosted_value (maxArity worldCount : Nat)
    (cells : Array (Option Nat)) (fact : CompiledFact) :
    (validateProjectionStepCosted maxArity worldCount cells fact).value =
      validateProjectionStep maxArity worldCount cells fact := by
  cases fact <;> simp only [validateProjectionStepCosted, validateProjectionStep,
    Complexity.Costed.charge_value, Complexity.Costed.bind_value, Complexity.Costed.tick_value,
    Complexity.Costed.pure_value]
  split
  · simp_all
  · split <;> simp_all [Complexity.Costed.branch_value]

private theorem validateProjectionStepCosted_cost_le (maxArity worldCount : Nat)
    (cells : Array (Option Nat)) (fact : CompiledFact) :
    (validateProjectionStepCosted maxArity worldCount cells fact).cost ≤ 11 := by
  cases fact <;> simp only [validateProjectionStepCosted, Complexity.Costed.charge_cost,
    Complexity.Costed.bind_cost, Complexity.Costed.tick_cost, Complexity.Costed.tick_value,
    Complexity.Costed.pure_cost]
  all_goals first | omega | skip
  rename_i tuple index result world
  cases h : cells[projectionCoordinate maxArity worldCount tuple index world]? with
  | none => simp
  | some entry =>
      cases entry with
      | none => simp
      | some firstResult =>
          simp only [Complexity.Costed.charge_cost]
          have hb := Complexity.Costed.branch_cost_le
            (Complexity.Costed.tick (firstResult != result))
            (fun _ => Complexity.Costed.pure
              (.error (.conflictingTupleProjection tuple index world firstResult result) :
                Except ResolveError (Array (Option Nat))))
            (fun _ => Complexity.Costed.pure (.ok cells)) 1 0 (by simp) (by simp) (by simp)
          omega

def validateTupleProjectionsCosted
    (worldCount thingCount : Nat) (facts : Array CompiledFact) :
    Complexity.Costed (Except ResolveError Unit) := do
  let maxArity ← projectionArityOfFactsCosted facts
  let cells ← Complexity.Costed.replicateArray (thingCount * maxArity * worldCount) none
  let checked ← Complexity.Costed.foldArrayExcept facts cells
    (validateProjectionStepCosted maxArity worldCount)
  pure (checked.map (fun _ => ()))

def validateTupleProjections
    (worldCount thingCount : Nat) (facts : Array CompiledFact) :
    Except ResolveError Unit :=
  (validateTupleProjectionsCosted worldCount thingCount facts).value

/-- Instrumentation preserves the existing validation result on every input,
including out-of-range coordinates and multiple possible conflicts. -/
private theorem validateTupleProjectionsCosted_eq_spec
    (worldCount thingCount : Nat) (facts : Array CompiledFact) :
    (validateTupleProjectionsCosted worldCount thingCount facts).value =
      validateTupleProjectionsSpec worldCount thingCount facts := by
  simp only [validateTupleProjectionsCosted, Bind.bind, Pure.pure, Complexity.Costed.bind,
    Complexity.Costed.pure, projectionArityOfFactsCosted_value,
    Complexity.Costed.replicateArray_value, Complexity.Costed.foldArrayExcept_value,
    validateProjectionStepCosted_value]
  have hf := Array.forIn_yield_eq_foldlM (m := Except ResolveError) (xs := facts)
    (fun fact cells => validateProjectionStep (projectionArityOfFacts facts) worldCount cells fact)
    (fun _ _ cells => cells)
    (Array.replicate (thingCount * projectionArityOfFacts facts * worldCount) none)
  simp only [id_map'] at hf
  rw [← hf]
  simp only [validateTupleProjectionsSpec]
  congr 2
  funext fact cells
  cases fact <;> simp [validateProjectionStep, Pure.pure, Except.pure]
  split <;> simp_all
  · split <;> simp_all [Bind.bind, Except.bind]
    rfl
  · rfl

@[simp] theorem validateTupleProjectionsCosted_value
    (worldCount thingCount : Nat) (facts : Array CompiledFact) :
    (validateTupleProjectionsCosted worldCount thingCount facts).value =
      validateTupleProjections worldCount thingCount facts := rfl

theorem validateTupleProjectionsCosted_cost_le
    (worldCount thingCount : Nat) (facts : Array CompiledFact) :
    (validateTupleProjectionsCosted worldCount thingCount facts).cost ≤
      2 * (thingCount * projectionArityOfFacts facts * worldCount) + 18 * facts.size := by
  have ha := projectionArityOfFactsCosted_cost_le facts
  have hc := Complexity.Costed.foldArrayExcept_cost_le facts
    (Array.replicate (thingCount * projectionArityOfFacts facts * worldCount) none)
    (validateProjectionStepCosted (projectionArityOfFacts facts) worldCount) 11
    (by intro cells fact _; exact validateProjectionStepCosted_cost_le _ _ _ _)
  simp only [validateTupleProjectionsCosted, Bind.bind, Pure.pure, Complexity.Costed.bind,
    Complexity.Costed.pure, projectionArityOfFactsCosted_value,
    Complexity.Costed.replicateArray_value, Complexity.Costed.replicateArray_cost]
  omega

example : validateTupleProjections 1 2 #[
    .tupleProjection 0 0 1 0, .tupleProjection 0 0 1 0] = .ok () := by
  native_decide

example : validateTupleProjections 1 2 #[
    .tupleProjection 0 0 1 0, .tupleProjection 0 0 0 0] =
      .error (.conflictingTupleProjection 0 0 0 1 0) := by
  native_decide

-- Exact native counts exercise the compiled traversal. A single projection
-- costs 5 for the arity scan, 4 to initialize two cells, and 13 to validate.
-- The general bound and behavior correspondence above use structural proofs.
example : (validateTupleProjectionsCosted 1 2 #[]).cost = 0 := by native_decide
example : (validateTupleProjectionsCosted 1 2 #[.tupleProjection 0 0 1 0]).cost = 22 := by
  native_decide
example : (validateTupleProjectionsCosted 1 2 #[
    .tupleProjection 0 0 1 0, .tupleProjection 0 0 1 0]).cost = 40 := by native_decide
example : (validateTupleProjectionsCosted 1 2 #[
    .tupleProjection 0 0 1 0, .tupleProjection 0 0 0 0]).cost = 40 := by native_decide

-- The arity scan must still inspect the suffix. After a conflict, validation
-- skips that suffix: this extra non-projection fact adds four operations.
example : (validateTupleProjectionsCosted 1 2 #[
    .tupleProjection 0 0 1 0, .tupleProjection 0 0 0 0, .derived "unreached"]).cost = 44 := by
  native_decide
example : validateTupleProjections 1 2 #[
    .tupleProjection 0 0 1 0, .tupleProjection 0 0 0 0,
    .tupleProjection 1 0 1 0, .tupleProjection 1 0 0 0] =
      .error (.conflictingTupleProjection 0 0 0 1 0) := by native_decide

-- Out-of-range input retains the established error category and payload.
example : validateTupleProjections 0 2 #[.tupleProjection 0 0 1 0] =
    .error (.conflictingTupleProjection 0 0 0 1 1) := by native_decide
example : (validateTupleProjectionsCosted 0 2 #[.tupleProjection 0 0 1 0]).cost = 15 := by
  native_decide

/-- Populate dense tables from the already-expanded fact stream. -/
def FactTables.withDenseFactsCosted
    (tables : FactTables) (worldCount thingCount : Nat)
    (facts : Array CompiledFact) : Complexity.Costed FactTables :=
  let arity := projectionArityOfFactsCosted facts
  let initialized := tables.initializeDenseCosted worldCount thingCount arity.value
  let populated := Complexity.Costed.foldArray facts initialized.value
    FactTables.writeDenseFactCosted
  let closures := populated.value.buildInherenceClosuresCosted
  ⟨{ populated.value with
      inherenceClosures := closures.value.reachable
      inherenceNextHops := closures.value.nextHop },
    arity.cost + initialized.cost + populated.cost + closures.cost⟩

/--
Compact production materialization used by generated certificates.

The counted implementation below follows the same initialization, fact-write,
and closure stages. `FactTables.withDenseFactsCosted_value` proves their
correspondence without making the theorem a global simplification rule.
-/
def FactTables.withDenseFacts
    (tables : FactTables) (worldCount thingCount : Nat)
  (facts : Array CompiledFact) : FactTables :=
  let initialized := tables.initializeDense
    worldCount thingCount (projectionArityOfFacts facts)
  let populated := facts.foldl FactTables.writeDenseFact initialized
  let closures := populated.buildInherenceClosures
  { populated with
    inherenceClosures := closures.reachable
    inherenceNextHops := closures.nextHop }

@[simp] theorem FactTables.withDenseFacts_denseWorldCount
    (tables : FactTables) (worldCount thingCount : Nat)
    (facts : Array CompiledFact) :
    (tables.withDenseFacts worldCount thingCount facts).denseWorldCount = worldCount := by
  simp [FactTables.withDenseFacts, FactTables.buildInherenceClosures,
    FactTables.foldl_writeDenseFact_denseWorldCount, FactTables.initializeDense]

@[simp] theorem FactTables.withDenseFacts_denseThingCount
    (tables : FactTables) (worldCount thingCount : Nat)
    (facts : Array CompiledFact) :
    (tables.withDenseFacts worldCount thingCount facts).denseThingCount = thingCount := by
  simp [FactTables.withDenseFacts, FactTables.buildInherenceClosures,
    FactTables.foldl_writeDenseFact_denseThingCount, FactTables.initializeDense]

@[simp] theorem FactTables.withDenseFacts_denseProjectionArity
    (tables : FactTables) (worldCount thingCount : Nat)
    (facts : Array CompiledFact) :
    (tables.withDenseFacts worldCount thingCount facts).denseProjectionArity =
      projectionArityOfFacts facts := by
  simp [FactTables.withDenseFacts, FactTables.buildInherenceClosures,
    FactTables.foldl_writeDenseFact_denseProjectionArity,
    FactTables.initializeDense]

@[simp] theorem FactTables.withDenseFacts_unaryLookup
    (tables : FactTables) (worldCount thingCount : Nat)
    (facts : Array CompiledFact) :
    (tables.withDenseFacts worldCount thingCount facts).unaryLookup =
      tables.unaryLookup := by
  simp [FactTables.withDenseFacts, FactTables.buildInherenceClosures,
    FactTables.initializeDense, FactTables.foldl_writeDenseFact_unaryLookup]

@[simp] theorem FactTables.withDenseFacts_binaryLookup
    (tables : FactTables) (worldCount thingCount : Nat)
    (facts : Array CompiledFact) :
    (tables.withDenseFacts worldCount thingCount facts).binaryLookup =
      tables.binaryLookup := by
  simp [FactTables.withDenseFacts, FactTables.buildInherenceClosures,
    FactTables.initializeDense, FactTables.foldl_writeDenseFact_binaryLookup]

@[simp] theorem FactTables.withDenseFacts_ternaryLookup
    (tables : FactTables) (worldCount thingCount : Nat)
    (facts : Array CompiledFact) :
    (tables.withDenseFacts worldCount thingCount facts).ternaryLookup =
      tables.ternaryLookup := by
  simp [FactTables.withDenseFacts, FactTables.buildInherenceClosures,
    FactTables.initializeDense, FactTables.foldl_writeDenseFact_ternaryLookup]

@[simp] theorem FactTables.withDenseFacts_tupleProjectionLookup
    (tables : FactTables) (worldCount thingCount : Nat)
    (facts : Array CompiledFact) :
    (tables.withDenseFacts worldCount thingCount facts).tupleProjectionLookup =
      tables.tupleProjectionLookup := by
  simp [FactTables.withDenseFacts, FactTables.buildInherenceClosures,
    FactTables.initializeDense,
    FactTables.foldl_writeDenseFact_tupleProjectionLookup]

@[simp] theorem FactTables.withDenseFacts_tupleProjectionResult?
    (tables : FactTables) (worldCount thingCount : Nat)
    (facts : Array CompiledFact) :
    (tables.withDenseFacts worldCount thingCount facts).tupleProjectionResult? =
      tables.tupleProjectionResult? := by
  simp [FactTables.withDenseFacts, FactTables.buildInherenceClosures,
    FactTables.initializeDense,
    FactTables.foldl_writeDenseFact_tupleProjectionResult?]

theorem FactTables.withDenseFactsCosted_value
    (tables : FactTables) (worldCount thingCount : Nat) (facts : Array CompiledFact) :
    (tables.withDenseFactsCosted worldCount thingCount facts).value =
      tables.withDenseFacts worldCount thingCount facts := by
  simp [FactTables.withDenseFactsCosted, FactTables.withDenseFacts,
    Complexity.Costed.foldArray_value]

theorem FactTables.withDenseFactsCosted_cost_le
    (tables : FactTables) (worldCount thingCount : Nat)
    (facts : Array CompiledFact) :
    (tables.withDenseFactsCosted worldCount thingCount facts).cost ≤
      2 * (UnaryField.count * thingCount * worldCount +
      BinaryField.count * thingCount * thingCount * worldCount +
      TernaryField.count * thingCount * thingCount * thingCount * worldCount +
      thingCount * projectionArityOfFacts facts * worldCount) +
      21 * facts.size +
      worldCount * (23 * thingCount ^ 3 + 48 * thingCount ^ 2 + 5 * thingCount + 3) + 11 := by
  let initialized := tables.initializeDenseCosted worldCount thingCount (projectionArityOfFacts facts)
  let populated := Complexity.Costed.foldArray facts initialized.value FactTables.writeDenseFactCosted
  have hc := populated.value.buildInherenceClosuresCosted_cost_le
  have ha := projectionArityOfFactsCosted_cost_le facts
  have hp := Complexity.Costed.foldArray_cost_le facts initialized.value
    FactTables.writeDenseFactCosted 14 (fun tables fact _ =>
      tables.writeDenseFactCosted_cost_le fact)
  simp only [populated, initialized, Complexity.Costed.foldArray_value,
    FactTables.writeDenseFactCosted_value,
    FactTables.foldl_writeDenseFact_denseWorldCount,
    FactTables.foldl_writeDenseFact_denseThingCount,
    FactTables.initializeDenseCosted_value, FactTables.initializeDense] at hc
  simp only [FactTables.withDenseFactsCosted, projectionArityOfFactsCosted_value,
    FactTables.initializeDenseCosted_cost, Complexity.Costed.foldArray_value,
    FactTables.writeDenseFactCosted_value,
    FactTables.initializeDenseCosted_value, FactTables.initializeDense]
  dsimp [initialized] at hp
  simp only [FactTables.initializeDenseCosted_value, FactTables.initializeDense] at hp
  omega

/-- Reify inspectable sparse tables for the compatibility `compileModelAST` path. -/
def FactTables.sparseFacts (tables : FactTables) : Array CompiledFact :=
  let unaryFacts := UnaryField.all.foldl (fun facts field =>
    (tables.unary.getD field.toTableField #[]).foldl
      (fun facts entry => facts.push (.unary field entry.1 entry.2)) facts) #[]
  let binaryFacts := BinaryField.all.foldl (fun facts field =>
    (tables.binary.getD field.toTableField #[]).foldl
      (fun facts entry =>
        let (left, right, world) := entry
        facts.push (.binary field left right world)) facts) unaryFacts
  let ternaryFacts := TernaryField.all.foldl (fun facts field =>
    (tables.ternary.getD field.toTableField #[]).foldl
      (fun facts entry =>
        let (first, second, third, world) := entry
        facts.push (.ternary field first second third world)) facts) binaryFacts
  tables.tupleProjection.foldl (fun facts entry =>
    let (tuple, index, result, world) := entry
    facts.push (.tupleProjection tuple index result world)) ternaryFacts

/--
Close the specialization table under the basic reflexivity required by (a5).

In this semantic compiler, `Type` is defined by possible instantiation:
a thing is a type iff it appears as the target of some `x :: T` fact in some
world. Since (a5) makes every type specialize itself at every world, the DSL
inserts those reflexive `T ⊑ T` facts automatically.
-/
def closeReflexiveSpecialization
    (worldCount : Nat) (tables : FactTables) : FactTables :=
  let instFacts := tables.binary.getD "inst" #[]
  let typeTargets :=
    instFacts.foldl
      (fun (seen : Std.HashSet Nat) (_x, t, _w) => seen.insert t)
      {}
  typeTargets.toArray.foldl
    (fun tables t =>
      Id.run do
        let mut tables := tables
        for w in [:worldCount] do
          tables := addBinary tables "sub" t t w
        pure tables)
    tables

/-- Compile one resolved DSL fact into finite-table data. -/
def compileFact (tables : FactTables) : CompiledFact → FactTables
  | .unary field x w => addUnaryWithTaxonomy tables field.toTableField x w
  | .binary field x y w => addBinary tables field.toTableField x y w
  | .ternary field x y z w => addTernary tables field.toTableField x y z w
  | .tupleProjection tuple index result w => addTupleProjection tables tuple index result w
  | .derived prop => addDerivedProp tables prop

/-- Compile one resolved fact whose unary taxonomy closure is already explicit. -/
def compileExplicitFact (tables : FactTables) : CompiledFact → FactTables
  | .unary field x w => addUnary tables field.toTableField x w
  | .binary field x y w => addBinary tables field.toTableField x y w
  | .ternary field x y z w => addTernary tables field.toTableField x y z w
  | .tupleProjection tuple index result w => addTupleProjection tables tuple index result w
  | .derived prop => addDerivedProp tables prop

/-- Insert an expanded fact into the inspectable sparse store. The tag test,
fixed field-name lookup, map read, array write, and map insertion are charged
where they execute. Map operations use the documented abstract interface.
The lookup closure is stored here; its body runs only on a later query and
must be counted by that query. Closure allocation is outside the cost model. -/
def compileExplicitFactCosted (tables : FactTables) (fact : CompiledFact) :
    Complexity.Costed FactTables :=
  Complexity.Costed.charge 1 <| match fact with
  | .unary field x w => do
      let field ← Complexity.Costed.tick field.toTableField 1
      let entries ← Complexity.Costed.tick (tables.unary.getD field #[]) 1
      let entries ← Complexity.Costed.tick (entries.push (x, w)) 1
      let unary ← Complexity.Costed.tick (tables.unary.insert field entries) 1
      pure { tables with
        unary := unary
        unaryLookup := fun field' x' w' =>
          tables.unaryLookup field' x' w' || (field' == field && x' == x && w' == w) }
  | .binary field x y w => do
      let field ← Complexity.Costed.tick field.toTableField 1
      let entries ← Complexity.Costed.tick (tables.binary.getD field #[]) 1
      let entries ← Complexity.Costed.tick (entries.push (x, y, w)) 1
      let binary ← Complexity.Costed.tick (tables.binary.insert field entries) 1
      pure { tables with
        binary := binary
        binaryLookup := fun field' x' y' w' =>
          tables.binaryLookup field' x' y' w' ||
            (field' == field && x' == x && y' == y && w' == w) }
  | .ternary field x y z w => do
      let field ← Complexity.Costed.tick field.toTableField 1
      let entries ← Complexity.Costed.tick (tables.ternary.getD field #[]) 1
      let entries ← Complexity.Costed.tick (entries.push (x, y, z, w)) 1
      let ternary ← Complexity.Costed.tick (tables.ternary.insert field entries) 1
      pure { tables with
        ternary := ternary
        ternaryLookup := fun field' x' y' z' w' =>
          tables.ternaryLookup field' x' y' z' w' ||
            (field' == field && x' == x && y' == y && z' == z && w' == w) }
  | .tupleProjection tuple index result world =>
      Complexity.Costed.tick (addTupleProjection tables tuple index result world) 1
  | .derived prop => Complexity.Costed.tick (addDerivedProp tables prop) 1

@[simp] theorem compileExplicitFactCosted_value (tables : FactTables) (fact : CompiledFact) :
    (compileExplicitFactCosted tables fact).value = compileExplicitFact tables fact := by
  cases fact <;> rfl

theorem compileExplicitFactCosted_cost_le (tables : FactTables) (fact : CompiledFact) :
    (compileExplicitFactCosted tables fact).cost ≤ 5 := by
  cases fact <;> simp [compileExplicitFactCosted, Bind.bind, Pure.pure,
    Complexity.Costed.bind, Complexity.Costed.tick, Complexity.Costed.pure]

private def compileExplicitFactErased (tables : FactTables) (fact : CompiledFact) :
    FactTables := (compileExplicitFactCosted tables fact).value

/-- Keep compact kernel reduction and use the proved counted erasure natively. -/
@[csimp] theorem compileExplicitFact_eq_erased :
    compileExplicitFact = compileExplicitFactErased := by
  funext tables fact
  exact (compileExplicitFactCosted_value tables fact).symm

/-- Compile resolved facts before global closure steps. -/
def compileFacts (facts : Array CompiledFact) : FactTables :=
  facts.foldl compileFact {}

/-- Compile a resolved model AST into finite tables, including global closures. -/
def compileModelAST (ast : ModelAST) : FactTables :=
  let tables := closeReflexiveSpecialization ast.worldCount (compileFacts ast.facts)
  let tables := ast.productFamilies.foldl addProductFamily tables
  tables.withDenseFacts ast.worldCount ast.thingCount tables.sparseFacts

private def expandAtWorld (world : Nat) : ScopedCompiledFact → CompiledFact
  | .unary field x _ => .unary field x world
  | .binary field x y _ => .binary field x y world
  | .ternary field x y z _ => .ternary field x y z world
  | .tupleProjection tuple index result _ => .tupleProjection tuple index result world
  | .derived assertion _ => .derived (renderDerivedFact assertion world)

/-- One fact-instantiation dispatch. A derived assertion also performs its
counted proposition rendering; primitive fixed-arity constructors add no further
work in this source-operation model. -/
private def expandAtWorldCosted (world : Nat) (fact : ScopedCompiledFact) :
    Complexity.Costed CompiledFact :=
  Complexity.Costed.charge 1 <| match fact with
  | .unary field x _ => Complexity.Costed.pure (.unary field x world)
  | .binary field x y _ => Complexity.Costed.pure (.binary field x y world)
  | .ternary field x y z _ => Complexity.Costed.pure (.ternary field x y z world)
  | .tupleProjection tuple index result _ =>
      Complexity.Costed.pure (.tupleProjection tuple index result world)
  | .derived assertion _ =>
      (renderDerivedFactCosted assertion world).map CompiledFact.derived

private theorem expandAtWorldCosted_value (world : Nat) (fact : ScopedCompiledFact) :
    (expandAtWorldCosted world fact).value = expandAtWorld world fact := by
  cases fact <;> rfl

/-- Instantiation cost at any world. The renderer's world-invariance theorem
justifies using zero here; this is an exact cost, not a size envelope. -/
def ScopedCompiledFact.instantiationCost (fact : ScopedCompiledFact) : Nat :=
  (expandAtWorldCosted 0 fact).cost

private theorem expandAtWorldCosted_cost (world : Nat) (fact : ScopedCompiledFact) :
    (expandAtWorldCosted world fact).cost = fact.instantiationCost := by
  cases fact <;> simp [expandAtWorldCosted, ScopedCompiledFact.instantiationCost,
    renderDerivedFactCosted_cost_world _ world 0]

theorem ScopedCompiledFact.instantiationCost_le (fact : ScopedCompiledFact) :
    fact.instantiationCost ≤ 29 := by
  cases fact <;>
    simp [ScopedCompiledFact.instantiationCost, expandAtWorldCosted]
  rename_i assertion scope
  have h := renderDerivedFactCosted_cost_le assertion 0
  omega

/-- Expand one scoped resolved fact into ordinary world-indexed facts. -/
private def expandScopedFactCore (worldCount : Nat) : ScopedCompiledFact → Array CompiledFact
  | fact@(.unary _ _ (.at w)) => #[expandAtWorld w fact]
  | fact@(.binary _ _ _ (.at w)) => #[expandAtWorld w fact]
  | fact@(.derived _ (.at w)) => #[expandAtWorld w fact]
  | fact@(.unary _ _ .everywhere) =>
      (Array.range worldCount).map fun w => expandAtWorld w fact
  | fact@(.binary _ _ _ .everywhere) =>
      (Array.range worldCount).map fun w => expandAtWorld w fact
  | fact@(.ternary _ _ _ _ (.at w)) => #[expandAtWorld w fact]
  | fact@(.ternary _ _ _ _ .everywhere) =>
      (Array.range worldCount).map fun w => expandAtWorld w fact

  | fact@(.tupleProjection _ _ _ (.at w)) => #[expandAtWorld w fact]
  | fact@(.tupleProjection _ _ _ .everywhere) =>
      (Array.range worldCount).map fun w => expandAtWorld w fact
  | fact@(.derived _ .everywhere) =>
      (Array.range worldCount).map fun w => expandAtWorld w fact

def FactScope.worldMultiplicity (worldCount : Nat) : FactScope → Nat
  | .at _ => 1
  | .everywhere => worldCount

def NamedFactScope.worldMultiplicity (worldCount : Nat) : NamedFactScope → Nat
  | .at _ => 1
  | .everywhere => worldCount

def NamedScopedFact.scope : NamedScopedFact → NamedFactScope
  | .unary _ _ scope | .binary _ _ _ scope | .ternary _ _ _ _ scope
  | .tupleProjection _ _ _ scope | .derived _ scope => scope

def ScopedCompiledFact.scope : ScopedCompiledFact → FactScope
  | .unary _ _ scope | .binary _ _ _ scope | .ternary _ _ _ _ scope
  | .tupleProjection _ _ _ scope | .derived _ scope => scope

def NamedScopedFact.unaryField? : NamedScopedFact → Option UnaryField
  | .unary field _ _ => some field
  | _ => none

def ScopedCompiledFact.unaryField? : ScopedCompiledFact → Option UnaryField
  | .unary field _ _ => some field
  | _ => none

def NamedScopedFact.expansionWeight (worldCount : Nat)
    (fact : NamedScopedFact) : Nat :=
  fact.scope.worldMultiplicity worldCount

def ScopedCompiledFact.expansionWeight (worldCount : Nat)
    (fact : ScopedCompiledFact) : Nat :=
  fact.scope.worldMultiplicity worldCount

set_option maxHeartbeats 800000 in
/-- Successful name resolution preserves the structural data used by metrics. -/
theorem resolveNamedFactIndexed_preserves_metric_shape
    (worldCount : Nat) (worlds things : NameIndex) (named : NamedScopedFact)
    (resolved : ScopedCompiledFact)
    (h : resolveNamedFactIndexed worlds things named = .ok resolved) :
    resolved.scope.worldMultiplicity worldCount =
        named.scope.worldMultiplicity worldCount ∧
      resolved.unaryField? = named.unaryField? := by
  unfold resolveNamedFactIndexed at h
  cases named with
  | unary field thing scope =>
      cases scope <;>
        simp [resolveNamedFactIndexedCosted, exceptBindCosted,
          resolveThingIndexedCosted, resolveScopeIndexedCosted,
          resolveWorldIndexedCosted, NameIndex.findCosted,
          Complexity.Costed.map] at h <;>
        repeat' first | split at h | simp_all [ScopedCompiledFact.scope,
          NamedScopedFact.scope, ScopedCompiledFact.unaryField?,
          NamedScopedFact.unaryField?, FactScope.worldMultiplicity,
          NamedFactScope.worldMultiplicity]
      all_goals subst resolved
      all_goals try cases ‹FactScope›
      all_goals repeat' first | split at * | simp_all [Except.map]

  | binary field left right scope =>
      cases scope <;>
        simp [resolveNamedFactIndexedCosted, exceptBindCosted,
          resolveThingIndexedCosted, resolveScopeIndexedCosted,
          resolveWorldIndexedCosted, NameIndex.findCosted,
          Complexity.Costed.map] at h <;>
        repeat' first | split at h | simp_all [ScopedCompiledFact.scope,
          NamedScopedFact.scope, ScopedCompiledFact.unaryField?,
          NamedScopedFact.unaryField?, FactScope.worldMultiplicity,
          NamedFactScope.worldMultiplicity]
      all_goals subst resolved
      all_goals try cases ‹FactScope›
      all_goals repeat' first | split at * | simp_all [Except.map]
  | ternary field first second third scope =>
      cases scope <;>
        simp [resolveNamedFactIndexedCosted, exceptBindCosted,
          resolveThingIndexedCosted, resolveScopeIndexedCosted,
          resolveWorldIndexedCosted, NameIndex.findCosted,
          Complexity.Costed.map] at h <;>
        repeat' first | split at h | simp_all [ScopedCompiledFact.scope,
          NamedScopedFact.scope, ScopedCompiledFact.unaryField?,
          NamedScopedFact.unaryField?, FactScope.worldMultiplicity,
          NamedFactScope.worldMultiplicity]
      all_goals subst resolved
      all_goals try cases ‹FactScope›
      all_goals repeat' first | split at * | simp_all [Except.map]
  | tupleProjection tuple index result scope =>
      cases scope <;>
        simp [resolveNamedFactIndexedCosted, exceptBindCosted,
          resolveThingIndexedCosted, resolveScopeIndexedCosted,
          resolveWorldIndexedCosted, NameIndex.findCosted,
          Complexity.Costed.map] at h <;>
        repeat' first | split at h | simp_all [ScopedCompiledFact.scope,
          NamedScopedFact.scope, ScopedCompiledFact.unaryField?,
          NamedScopedFact.unaryField?, FactScope.worldMultiplicity,
          NamedFactScope.worldMultiplicity]
      all_goals subst resolved
      all_goals try cases ‹FactScope›
      all_goals repeat' first | split at * | simp_all [Except.map]
  | derived fact scope =>
      cases fact <;> cases scope <;>
        simp [resolveNamedFactIndexedCosted, resolveDerivedFactIndexedCosted,
          exceptBindCosted, resolveThingIndexedCosted,
          resolveScopeIndexedCosted, resolveWorldIndexedCosted,
          NameIndex.findCosted, Complexity.Costed.map] at h <;>
        repeat' first | split at h | simp_all [ScopedCompiledFact.scope,
          NamedScopedFact.scope, ScopedCompiledFact.unaryField?,
          NamedScopedFact.unaryField?, FactScope.worldMultiplicity,
          NamedFactScope.worldMultiplicity]
      all_goals subst resolved
      all_goals try cases ‹FactScope›
      all_goals repeat' first | split at * | simp_all [Except.map]

theorem expandScopedFactCore_size (worldCount : Nat) (fact : ScopedCompiledFact) :
    (expandScopedFactCore worldCount fact).size =
      match fact with
      | .unary _ _ scope | .binary _ _ _ scope | .ternary _ _ _ _ scope
      | .tupleProjection _ _ _ scope | .derived _ scope =>
          scope.worldMultiplicity worldCount := by
  cases fact with
  | unary field x scope => cases scope <;>
      simp [expandScopedFactCore, FactScope.worldMultiplicity]
  | binary field x y scope => cases scope <;>
      simp [expandScopedFactCore, FactScope.worldMultiplicity]
  | ternary field x y z scope => cases scope <;>
      simp [expandScopedFactCore, FactScope.worldMultiplicity]
  | tupleProjection tuple index result scope => cases scope <;>
      simp [expandScopedFactCore, FactScope.worldMultiplicity]
  | derived prop scope => cases scope <;>
      simp [expandScopedFactCore, FactScope.worldMultiplicity]

theorem expandScopedFactCore_projectionArity_le
    (worldCount : Nat) (fact : ScopedCompiledFact) :
    projectionArityOfFacts (expandScopedFactCore worldCount fact) ≤
      fact.projectionArity := by
  apply projectionArityOfFacts_le
  intro compiled hCompiled
  cases fact with
  | unary field x scope =>
      cases scope <;> simp [expandScopedFactCore, expandAtWorld] at hCompiled ⊢
      all_goals rcases hCompiled with ⟨_, ⟨_, rfl⟩⟩
      all_goals simp

  | binary field x y scope =>
      cases scope <;> simp [expandScopedFactCore, expandAtWorld] at hCompiled ⊢
      all_goals rcases hCompiled with ⟨_, ⟨_, rfl⟩⟩
      all_goals simp
  | ternary field x y z scope =>
      cases scope <;> simp [expandScopedFactCore, expandAtWorld] at hCompiled ⊢
      all_goals rcases hCompiled with ⟨_, ⟨_, rfl⟩⟩
      all_goals simp
  | tupleProjection tuple index result scope =>
      cases scope <;> simp [expandScopedFactCore, expandAtWorld] at hCompiled ⊢
      all_goals rcases hCompiled with ⟨_, ⟨_, rfl⟩⟩
      all_goals simp
  | derived prop scope =>
      cases scope <;> simp [expandScopedFactCore, expandAtWorld] at hCompiled ⊢
      all_goals rcases hCompiled with ⟨_, ⟨_, rfl⟩⟩
      all_goals simp

/-- Append one scoped fact without constructing a temporary expansion array.
Two dispatch charges select the fact's scope. Each emitted fact charges its
numeric iteration, counted instantiation, and output write. Derived assertions
include the renderer's actual cost; no arbitrary world function is stored. -/
private def expandScopedFactIntoCosted
    (worldCount : Nat) (fact : ScopedCompiledFact) (out : Array CompiledFact) :
    Complexity.Costed (Array CompiledFact) :=
  Complexity.Costed.charge 2 <| match fact.scope with
  | .at world => Complexity.Costed.foldFin 1 out fun output _ =>
      (expandAtWorldCosted world fact).bind fun compiled =>
        Complexity.Costed.tick (output.push compiled) 1
  | .everywhere => Complexity.Costed.foldFin worldCount out fun output i =>
      (expandAtWorldCosted i.val fact).bind fun compiled =>
        Complexity.Costed.tick (output.push compiled) 1

private theorem foldFin_push_eq_append (n : Nat) (f : Fin n → α) (out : Array α) :
    Fin.foldl n (fun output i => output.push (f i)) out = out ++ Array.ofFn f := by
  induction n with
  | zero => simp
  | succ n ih => simp [Fin.foldl_succ_last, Array.ofFn_succ, ih, Fin.last]

private theorem expandScopedFactIntoCosted_value
    (worldCount : Nat) (fact : ScopedCompiledFact) (out : Array CompiledFact) :
    (expandScopedFactIntoCosted worldCount fact out).value =
      out ++ expandScopedFactCore worldCount fact := by
  cases fact <;> rename_i scope <;> cases scope <;>
    simp [expandScopedFactIntoCosted, ScopedCompiledFact.scope,
      Complexity.Costed.foldFin_value, Complexity.Costed.tick,
      expandAtWorldCosted_value, foldFin_push_eq_append, expandScopedFactCore,
      Fin.foldl_succ, Array.range, Function.comp_def]

private theorem expandScopedFactIntoCosted_cost
    (worldCount : Nat) (fact : ScopedCompiledFact) (out : Array CompiledFact) :
    (expandScopedFactIntoCosted worldCount fact out).cost =
      (fact.instantiationCost + 2) * fact.expansionWeight worldCount + 2 := by
  have hc (n : Nat) (world : Fin n → Nat) :
      (Complexity.Costed.foldFin n out (fun output i =>
        (expandAtWorldCosted (world i) fact).bind fun compiled =>
          Complexity.Costed.tick (output.push compiled) 1)).cost =
        (fact.instantiationCost + 2) * n := by
    simpa [Nat.mul_comm, Nat.add_assoc] using Complexity.Costed.foldFin_cost_eq n out
      (fun output i => (expandAtWorldCosted (world i) fact).bind fun compiled =>
        Complexity.Costed.tick (output.push compiled) 1)
      (fact.instantiationCost + 1)
      (by intro _ _; simp [expandAtWorldCosted_cost])
  unfold expandScopedFactIntoCosted
  cases h : fact.scope <;>
    simp [h, ScopedCompiledFact.expansionWeight, FactScope.worldMultiplicity, hc, Nat.add_comm]


def expandScopedFactCosted
    (worldCount : Nat) (fact : ScopedCompiledFact) :
    Complexity.Costed (Array CompiledFact) :=
  expandScopedFactIntoCosted worldCount fact #[]

def expandScopedFact (worldCount : Nat) (fact : ScopedCompiledFact) :
    Array CompiledFact :=
  (expandScopedFactCosted worldCount fact).value

@[simp] theorem expandScopedFactCosted_value
    (worldCount : Nat) (fact : ScopedCompiledFact) :
    (expandScopedFactCosted worldCount fact).value =
      expandScopedFact worldCount fact := rfl

/-- Expand into one output accumulator, in source-fact and then world order. -/
def expandScopedFactsCosted
    (worldCount : Nat) (facts : Array ScopedCompiledFact) :
    Complexity.Costed (Array CompiledFact) :=
  Complexity.Costed.foldArray facts #[] fun out fact =>
    expandScopedFactIntoCosted worldCount fact out

/-- The append-based specification is used only to prove output properties;
the executable fold writes each fact directly into its final output array. -/
private theorem expandScopedFactsCosted_value_eq_foldl
    (worldCount : Nat) (facts : Array ScopedCompiledFact) :
    (expandScopedFactsCosted worldCount facts).value =
      facts.foldl (fun out fact => out ++ expandScopedFactCore worldCount fact) #[] := by
  simp [expandScopedFactsCosted, expandScopedFactIntoCosted_value]

def expandScopedFacts (worldCount : Nat) (facts : Array ScopedCompiledFact) : Array CompiledFact :=
  (expandScopedFactsCosted worldCount facts).value

@[simp] theorem expandScopedFactsCosted_value
    (worldCount : Nat) (facts : Array ScopedCompiledFact) :
    (expandScopedFactsCosted worldCount facts).value =
      expandScopedFacts worldCount facts := rfl

private theorem foldPush_projectionArity_le
    (added out : Array CompiledFact) (bound : Nat)
    (hOut : projectionArityOfFacts out ≤ bound)
    (hAdded : ∀ fact ∈ added, fact.projectionArity ≤ bound) :
    projectionArityOfFacts
      (added.foldl (fun result fact => result.push fact) out) ≤ bound := by
  rw [← Array.foldl_toList]
  have listBound : ∀ (xs : List CompiledFact) (initial : Array CompiledFact),
      projectionArityOfFacts initial ≤ bound →
      (∀ fact ∈ xs, fact.projectionArity ≤ bound) →
      projectionArityOfFacts
        (xs.foldl (fun result fact => result.push fact) initial) ≤ bound := by
    intro xs
    induction xs with
    | nil => simp
    | cons fact facts ih =>
        intro initial hInitial hFacts
        simp only [List.foldl_cons]
        apply ih
        · rw [projectionArityOfFacts_push]
          exact max_le hInitial (hFacts fact (by simp))
        · intro tailFact hTail
          exact hFacts tailFact (by simp [hTail])
  exact listBound added.toList out hOut (by simpa using hAdded)

theorem expandScopedFactsCosted_projectionArity_le
    (worldCount : Nat) (facts : Array ScopedCompiledFact) :
    projectionArityOfFacts (expandScopedFactsCosted worldCount facts).value ≤
      projectionArityOfScopedFacts facts := by
  have listBound (xs : List ScopedCompiledFact) (out : Array CompiledFact) (bound : Nat)
      (hOut : projectionArityOfFacts out ≤ bound)
      (hFacts : ∀ fact ∈ xs, fact.projectionArity ≤ bound) :
      projectionArityOfFacts
        (xs.foldl (fun out fact => out ++ expandScopedFactCore worldCount fact) out) ≤
          bound := by
    induction xs generalizing out with
    | nil => simpa using hOut
    | cons fact facts ih =>
        simp only [List.foldl_cons]
        apply ih
        · have hAppend := foldPush_projectionArity_le
            (expandScopedFactCore worldCount fact) out bound hOut (by
              intro compiled hCompiled
              exact (compiled.projectionArity_le_of_mem
                (expandScopedFactCore worldCount fact) hCompiled).trans
                ((expandScopedFactCore_projectionArity_le worldCount fact).trans
                  (hFacts fact (by simp))))
          have hFold := Array.foldl_push_eq_append
            (as := expandScopedFactCore worldCount fact) (bs := out) (f := id) rfl
          simp only [Array.map_id, id_eq] at hFold
          rw [hFold] at hAppend
          exact hAppend
        · intro tailFact hTail
          exact hFacts tailFact (by simp [hTail])
  rw [expandScopedFactsCosted_value_eq_foldl, ← Array.foldl_toList]
  apply listBound facts.toList #[] (projectionArityOfScopedFacts facts)
  · simp [projectionArityOfFacts]
  · intro fact hFact
    exact fact.projectionArity_le_of_mem facts (by simpa using hFact)

theorem expandScopedFactCosted_cost
    (worldCount : Nat) (fact : ScopedCompiledFact) :
    (expandScopedFactCosted worldCount fact).cost =
      (fact.instantiationCost + 2) * fact.expansionWeight worldCount + 2 :=
  expandScopedFactIntoCosted_cost worldCount fact #[]

/-- Exact accumulated instantiation, loop, and output cost. Each input also
contributes two scope-dispatch and two array-traversal operations. -/
theorem expandScopedFactsCosted_cost
    (worldCount : Nat) (facts : Array ScopedCompiledFact) :
    (expandScopedFactsCosted worldCount facts).cost =
      (facts.toList.map (fun fact =>
        (fact.instantiationCost + 2) * fact.expansionWeight worldCount)).sum +
        4 * facts.size := by
  have hc := Complexity.Costed.foldArray_cost_eq_sum facts #[]
    (fun out fact => expandScopedFactIntoCosted worldCount fact out)
    (fun fact => (fact.instantiationCost + 2) * fact.expansionWeight worldCount + 2)
    (fun out fact => expandScopedFactIntoCosted_cost worldCount fact out)
  have sumCost (xs : List ScopedCompiledFact) :
      (xs.map (fun fact =>
        ((fact.instantiationCost + 2) * fact.expansionWeight worldCount + 2) + 2)).sum =
        (xs.map (fun fact =>
          (fact.instantiationCost + 2) * fact.expansionWeight worldCount)).sum +
          4 * xs.length := by
    induction xs with
    | nil => simp
    | cons fact facts ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
        omega
  simpa [expandScopedFactsCosted, sumCost] using hc

/-- Instantiation costs at most 29, including derived rendering. The loop and
write add two per emitted fact. This bound also covers empty-world inputs. -/
theorem expandScopedFactsCosted_cost_le_expansionWeight
    (worldCount : Nat) (facts : Array ScopedCompiledFact) :
    (expandScopedFactsCosted worldCount facts).cost ≤
      31 * (facts.toList.map (ScopedCompiledFact.expansionWeight worldCount)).sum +
        4 * facts.size := by
  rw [expandScopedFactsCosted_cost]
  have hsum (xs : List ScopedCompiledFact) :
      (xs.map (fun fact =>
        (fact.instantiationCost + 2) * fact.expansionWeight worldCount)).sum ≤
          31 * (xs.map (ScopedCompiledFact.expansionWeight worldCount)).sum := by
    induction xs with
    | nil => simp
    | cons fact facts ih =>
        have hcost := fact.instantiationCost_le
        have head := Nat.mul_le_mul_right (fact.expansionWeight worldCount)
          (show fact.instantiationCost + 2 ≤ 31 by omega)
        simp only [List.map_cons, List.sum_cons, Nat.mul_add]
        omega
  exact Nat.add_le_add_right (hsum facts.toList) _


theorem expandScopedFactsCosted_value_size
    (worldCount : Nat) (facts : Array ScopedCompiledFact) :
    (expandScopedFactsCosted worldCount facts).value.size =
      (facts.toList.map (ScopedCompiledFact.expansionWeight worldCount)).sum := by
  have listValue (xs : List ScopedCompiledFact) (out : Array CompiledFact) :
      (xs.foldl (fun out fact => out ++ expandScopedFactCore worldCount fact) out).size =
        out.size + (xs.map (ScopedCompiledFact.expansionWeight worldCount)).sum := by
    induction xs generalizing out with
    | nil => simp
    | cons fact facts ih =>
        rw [List.foldl_cons, ih, Array.size_append, expandScopedFactCore_size]
        cases fact <;>
          simp [ScopedCompiledFact.expansionWeight, ScopedCompiledFact.scope,
            Nat.add_assoc]
  rw [expandScopedFactsCosted_value_eq_foldl, ← Array.foldl_toList]
  simpa using listValue facts.toList #[]

/-- Coarse source-only scope-expansion bound, including zero-world sources. -/
theorem expandScopedFactsCosted_cost_le
    (worldCount : Nat) (facts : Array ScopedCompiledFact) :
    (expandScopedFactsCosted worldCount facts).cost ≤
      facts.size * (31 * worldCount + 35) := by
  apply le_trans (expandScopedFactsCosted_cost_le_expansionWeight worldCount facts)
  have listBound (xs : List ScopedCompiledFact) :
      (xs.map (ScopedCompiledFact.expansionWeight worldCount)).sum ≤
        xs.length * (worldCount + 1) := by
    induction xs with
    | nil => simp
    | cons fact facts ih =>
        have hhead : fact.expansionWeight worldCount ≤ worldCount + 1 := by
          cases fact <;> rename_i scope <;> cases scope <;>
            simp [ScopedCompiledFact.expansionWeight, ScopedCompiledFact.scope,
              FactScope.worldMultiplicity]
        simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
        omega
  have h := listBound facts.toList
  simp only [Array.length_toList] at h
  simp only [Nat.mul_add, Nat.mul_one] at h ⊢
  rw [Nat.mul_left_comm facts.size 31 worldCount]
  omega

example : (expandScopedFactsCosted 3 #[
    .unary .ex 0 .everywhere,
    .binary .inst 0 1 (.at 0)]).cost = 20 := by
  native_decide

example : (expandScopedFactsCosted 0 #[.unary .ex 0 .everywhere]).cost = 4 := by
  native_decide

/-- Counted explicit AST compiler used by generated certificate models. -/
def compileExplicitModelASTCosted (ast : ModelAST) : Complexity.Costed FactTables :=
  let facts := Complexity.Costed.foldArray ast.facts ({} : FactTables) compileExplicitFactCosted
  -- Registration writes one existing family record. Witness conversion is a
  -- separate model-construction stage, not hidden in this array push.
  let families := Complexity.Costed.foldArray ast.productFamilies facts.value
    (fun tables family => Complexity.Costed.tick (addProductFamily tables family) 1)
  let dense := families.value.withDenseFactsCosted
    ast.worldCount ast.thingCount ast.facts
  ⟨dense.value, facts.cost + families.cost + dense.cost⟩

/--
Compact kernel definition used by generated certificate declarations.
Certificate simplification sees table construction without cost bookkeeping.
Native compilation uses the counted erasure through the unconditional function
equality below. The cost theorem therefore concerns that executable core.
-/
def compileExplicitModelAST (ast : ModelAST) : FactTables :=
  let tables := ast.facts.foldl compileExplicitFact {}
  let tables := ast.productFamilies.foldl addProductFamily tables
  tables.withDenseFacts ast.worldCount ast.thingCount ast.facts

/-- The counted explicit compiler computes the compact production result. -/
theorem compileExplicitModelASTCosted_value (ast : ModelAST) :
    (compileExplicitModelASTCosted ast).value = compileExplicitModelAST ast := by
  simp only [compileExplicitModelASTCosted, Complexity.Costed.foldArray_value,
    compileExplicitFactCosted_value, Complexity.Costed.tick_value]
  exact FactTables.withDenseFactsCosted_value _ _ _ _

private def compileExplicitModelASTErased (ast : ModelAST) : FactTables :=
  (compileExplicitModelASTCosted ast).value

/-- Native explicit-AST compilation runs the counted core. The unconditional
equality retains compact kernel reduction for certificates while connecting
the executed implementation to the bound, following the implementation
correspondence discipline of Forster et al. (ITP 2021). -/
@[csimp] theorem compileExplicitModelAST_eq_erased :
    compileExplicitModelAST = compileExplicitModelASTErased := by
  funext ast
  exact (compileExplicitModelASTCosted_value ast).symm

theorem compileExplicitModelASTCosted_cost_le_parts (ast : ModelAST) :
    (compileExplicitModelASTCosted ast).cost ≤
      7 * ast.facts.size + 3 * ast.productFamilies.size +
        ((ast.productFamilies.foldl addProductFamily
          (ast.facts.foldl compileExplicitFact {})).withDenseFactsCosted
            ast.worldCount ast.thingCount ast.facts).cost := by
  have factsBound := Complexity.Costed.foldArray_cost_le ast.facts ({} : FactTables)
    compileExplicitFactCosted 5 (fun tables fact _ => compileExplicitFactCosted_cost_le tables fact)
  have familyCost := Complexity.Costed.foldArray_cost_eq ast.productFamilies
    (ast.facts.foldl compileExplicitFact {})
    (fun tables family => Complexity.Costed.tick (addProductFamily tables family) 1)
    1 (by intro _ _ _; rfl)
  simp only [compileExplicitModelASTCosted, Complexity.Costed.foldArray_value,
    compileExplicitFactCosted_value, Complexity.Costed.tick_value, familyCost]
  change (Complexity.Costed.foldArray ast.facts ({} : FactTables) compileExplicitFactCosted).cost +
    ast.productFamilies.size * 3 +
    ((ast.productFamilies.foldl addProductFamily
      (ast.facts.foldl compileExplicitFact {})).withDenseFactsCosted
        ast.worldCount ast.thingCount ast.facts).cost ≤ _
  omega

theorem compileExplicitModelASTCosted_cost_polynomial (ast : ModelAST) :
    (compileExplicitModelASTCosted ast).cost ≤
      28 * ast.facts.size + 3 * ast.productFamilies.size +
      2 * (UnaryField.count * ast.thingCount * ast.worldCount +
      BinaryField.count * ast.thingCount * ast.thingCount * ast.worldCount +
      TernaryField.count * ast.thingCount * ast.thingCount * ast.thingCount * ast.worldCount +
      ast.thingCount * projectionArityOfFacts ast.facts * ast.worldCount) +
      ast.worldCount *
        (23 * ast.thingCount ^ 3 + 48 * ast.thingCount ^ 2 + 5 * ast.thingCount + 3) + 11 := by
  apply compileExplicitModelASTCosted_cost_le_parts ast |>.trans
  apply Nat.le_trans (Nat.add_le_add_left
    (FactTables.withDenseFactsCosted_cost_le _ _ _ _) _)
  omega

namespace FactTables

/-- Count coordinate arithmetic, fixed field selection, the checked read, and
the option test that supplies `false` for a missing cell. Array reads use the
same checked-operation interface as table writes. -/
@[inline] def unaryTypedTableCosted (tables : FactTables) (field : UnaryField)
    {thingCount worldCount : Nat}
    (x : Fin thingCount) (w : Fin worldCount) : Complexity.Costed Bool := do
  let width ← Complexity.Costed.tick (tables.denseThingCount * tables.denseWorldCount) 1
  let coordinate ← Complexity.Costed.tick
    (unaryCoordinate x.val tables.denseWorldCount w.val) 2
  let fieldIndex ← Complexity.Costed.tick field.index 1
  let index ← Complexity.Costed.tick (fieldIndex * width + coordinate) 2
  let cell ← Complexity.Costed.tick tables.unaryCells[index]? 1
  Complexity.Costed.tick (cell.getD false) 1

/-- Dense executable unary lookup used after compiler materialization. -/
def unaryTypedTableDense (tables : FactTables) (field : UnaryField)
    {thingCount worldCount : Nat}
    (x : Fin thingCount) (w : Fin worldCount) : Bool :=
  let width := tables.denseThingCount * tables.denseWorldCount
  let coordinate := unaryCoordinate x.val tables.denseWorldCount w.val
  tables.unaryCells[field.index * width + coordinate]?.getD false

theorem unaryTypedTableCosted_value_dense (tables : FactTables) (field : UnaryField)
    {thingCount worldCount : Nat}
    (x : Fin thingCount) (w : Fin worldCount) :
    (tables.unaryTypedTableCosted field x w).value =
      tables.unaryTypedTableDense field x w := rfl

/--
Raw unary lookup over the inspectable fact stream. Both kernel reduction and
native execution use this definition. Dense replacement requires the equality
proof carried by `verifiedLookups` below.
-/
def unaryTypedTable (tables : FactTables) (field : UnaryField)
    {thingCount worldCount : Nat}
    (x : Fin thingCount) (w : Fin worldCount) : Bool :=
  tables.unaryLookup field.toTableField x.val w.val

/-- Binary lookup counts four coordinate operations and two width products,
in addition to field selection, flat indexing, a read, and an option test. -/
@[inline] def binaryTypedTableCosted (tables : FactTables) (field : BinaryField)
    {thingCount worldCount : Nat}
    (x y : Fin thingCount) (w : Fin worldCount) : Complexity.Costed Bool :=
  tables.binaryCellCosted field x.val y.val w.val

/-- Dense executable binary lookup used after compiler materialization. -/
def binaryTypedTableDense (tables : FactTables) (field : BinaryField)
    {thingCount worldCount : Nat}
    (x y : Fin thingCount) (w : Fin worldCount) : Bool :=
  let width := tables.denseThingCount * tables.denseThingCount * tables.denseWorldCount
  let coordinate := binaryCoordinate tables.denseThingCount tables.denseWorldCount
    x.val y.val w.val
  tables.binaryCells[field.index * width + coordinate]?.getD false

theorem binaryTypedTableCosted_value_dense (tables : FactTables) (field : BinaryField)
    {thingCount worldCount : Nat}
    (x y : Fin thingCount) (w : Fin worldCount) :
    (tables.binaryTypedTableCosted field x y w).value =
      tables.binaryTypedTableDense field x y w := rfl

def binaryTypedTable (tables : FactTables) (field : BinaryField)
    {thingCount worldCount : Nat}
    (x y : Fin thingCount) (w : Fin worldCount) : Bool :=
  tables.binaryLookup field.toTableField x.val y.val w.val

/-- Ternary lookup counts six coordinate operations and three width products.
The width uses explicit multiplications so the charged operations are visible. -/
@[inline] def ternaryTypedTableCosted (tables : FactTables) (field : TernaryField)
    {thingCount worldCount : Nat}
    (x y z : Fin thingCount) (w : Fin worldCount) : Complexity.Costed Bool := do
  let width ← Complexity.Costed.tick
    (tables.denseThingCount * tables.denseThingCount * tables.denseThingCount *
      tables.denseWorldCount) 3
  let coordinate ← Complexity.Costed.tick
    (ternaryCoordinate tables.denseThingCount tables.denseWorldCount
      x.val y.val z.val w.val) 6
  let fieldIndex ← Complexity.Costed.tick field.index 1
  let index ← Complexity.Costed.tick (fieldIndex * width + coordinate) 2
  let cell ← Complexity.Costed.tick tables.ternaryCells[index]? 1
  Complexity.Costed.tick (cell.getD false) 1

/-- Dense executable ternary lookup used after compiler materialization. -/
def ternaryTypedTableDense (tables : FactTables) (field : TernaryField)
    {thingCount worldCount : Nat}
    (x y z : Fin thingCount) (w : Fin worldCount) : Bool :=
  let width := tables.denseThingCount ^ 3 * tables.denseWorldCount
  let coordinate := ternaryCoordinate tables.denseThingCount tables.denseWorldCount
    x.val y.val z.val w.val
  tables.ternaryCells[field.index * width + coordinate]?.getD false

theorem ternaryTypedTableCosted_value_dense (tables : FactTables) (field : TernaryField)
    {thingCount worldCount : Nat}
    (x y z : Fin thingCount) (w : Fin worldCount) :
    (tables.ternaryTypedTableCosted field x y z w).value =
      tables.ternaryTypedTableDense field x y z w := by
  simp [ternaryTypedTableCosted, ternaryTypedTableDense, Bind.bind,
    Complexity.Costed.bind, Complexity.Costed.tick, Nat.pow_succ, Nat.mul_assoc]

def ternaryTypedTable (tables : FactTables) (field : TernaryField)
    {thingCount worldCount : Nat}
    (x y z : Fin thingCount) (w : Fin worldCount) : Bool :=
  tables.ternaryLookup field.toTableField x.val y.val z.val w.val

/-- Read a projection by its flat index. An invalid slot stops before index
arithmetic. Missing cells and out-of-range stored results return the tuple
itself, preserving the raw-table fallback. Each executed test is charged. -/
@[inline] def tupleProjectionTypedTableCosted (tables : FactTables)
    {thingCount worldCount : Nat}
    (p : Fin thingCount) (i : Nat) (w : Fin worldCount) :
    Complexity.Costed (Fin thingCount) :=
  if i < tables.denseProjectionArity then
    let coordinate := Complexity.Costed.tick
      (projectionCoordinate tables.denseProjectionArity
        tables.denseWorldCount p.val i w.val) 4
    let cell := Complexity.Costed.tick tables.projectionCells[coordinate.value]? 1
    let visitedCost := 2 + coordinate.cost + cell.cost + 1
    match cell.value with
    | none => ⟨p, visitedCost⟩
    | some entry => match entry with
      | none => ⟨p, visitedCost + 1⟩
      | some result =>
          ⟨(if h : result < thingCount then ⟨result, h⟩ else p), visitedCost + 1 + 2⟩
  else ⟨p, 2⟩

/-- Dense executable projection lookup used after compiler materialization. -/
def tupleProjectionTypedTableDense (tables : FactTables)
    {thingCount worldCount : Nat}
    (p : Fin thingCount) (i : Nat) (w : Fin worldCount) : Fin thingCount :=
  if i < tables.denseProjectionArity then
    let coordinate := projectionCoordinate tables.denseProjectionArity
      tables.denseWorldCount p.val i w.val
    match tables.projectionCells[coordinate]?.join with
    | some result => if h : result < thingCount then ⟨result, h⟩ else p
    | none => p
  else p

theorem tupleProjectionTypedTableCosted_value_dense (tables : FactTables)
    {thingCount worldCount : Nat}
    (p : Fin thingCount) (i : Nat) (w : Fin worldCount) :
    (tables.tupleProjectionTypedTableCosted p i w).value =
      tables.tupleProjectionTypedTableDense p i w := by
  unfold tupleProjectionTypedTableCosted tupleProjectionTypedTableDense
  split <;> simp_all [Complexity.Costed.tick]
  split <;> simp_all
  split <;> simp_all

def tupleProjectionTypedTable (tables : FactTables)
    {thingCount worldCount : Nat}
    (p : Fin thingCount) (i : Nat) (w : Fin worldCount) : Fin thingCount :=
  match tables.tupleProjectionResult? p.val i w.val with
  | some result => if h : result < thingCount then ⟨result, h⟩ else p
  | none => p

/-- A missing world matrix stops after its read and presence test. Otherwise
count the row-major index arithmetic, cell read, and final option test. -/
@[inline] def momentOfClosureCosted (tables : FactTables)
    (thingCount world moment bearer : Nat) : Complexity.Costed Bool :=
  Complexity.closureLookupCosted tables.inherenceClosures thingCount world moment bearer

theorem momentOfClosureCosted_cost_le (tables : FactTables)
    (thingCount world moment bearer : Nat) :
    (tables.momentOfClosureCosted thingCount world moment bearer).cost ≤ 6 :=
  Complexity.closureLookupCosted_cost_le _ _ _ _ _

/-- Typed checker queries use the stored matrix width. Diagnostic queries can
pass their explicit width to the same counted core. Equality of those widths
belongs to model-construction correspondence, not to this lookup bound. -/
@[inline] def inherenceClosureTableCosted (tables : FactTables)
    {thingCount worldCount : Nat}
    (m b : Fin thingCount) (w : Fin worldCount) : Complexity.Costed Bool :=
  tables.momentOfClosureCosted tables.denseThingCount w.val m.val b.val

def inherenceClosureTable (tables : FactTables)
    {thingCount worldCount : Nat}
    (m b : Fin thingCount) (w : Fin worldCount) : Bool :=
  match tables.inherenceClosures[w.val]? with
  | some closure =>
      closure[Complexity.matrixIndex tables.denseThingCount m.val b.val]?.getD false
  | none => false

@[simp] theorem unaryTypedTableCosted_cost (tables : FactTables) (field : UnaryField)
    {thingCount worldCount : Nat} (x : Fin thingCount) (w : Fin worldCount) :
    (tables.unaryTypedTableCosted field x w).cost = 8 := rfl

@[simp] theorem binaryTypedTableCosted_cost (tables : FactTables) (field : BinaryField)
    {thingCount worldCount : Nat} (x y : Fin thingCount) (w : Fin worldCount) :
    (tables.binaryTypedTableCosted field x y w).cost = 11 := rfl

@[simp] theorem ternaryTypedTableCosted_cost (tables : FactTables) (field : TernaryField)
    {thingCount worldCount : Nat} (x y z : Fin thingCount) (w : Fin worldCount) :
    (tables.ternaryTypedTableCosted field x y z w).cost = 14 := rfl

theorem tupleProjectionTypedTableCosted_cost_le (tables : FactTables)
    {thingCount worldCount : Nat} (p : Fin thingCount) (i : Nat) (w : Fin worldCount) :
    (tables.tupleProjectionTypedTableCosted p i w).cost ≤ 11 := by
  unfold tupleProjectionTypedTableCosted
  split <;> simp_all [Complexity.Costed.tick]
  split
  · simp
  · split <;> simp

theorem inherenceClosureTableCosted_cost_le (tables : FactTables)
    {thingCount worldCount : Nat} (m b : Fin thingCount) (w : Fin worldCount) :
    (tables.inherenceClosureTableCosted m b w).cost ≤ 6 := by
  exact momentOfClosureCosted_cost_le tables tables.denseThingCount w.val m.val b.val

theorem inherenceClosureTableCosted_value (tables : FactTables)
    {thingCount worldCount : Nat} (m b : Fin thingCount) (w : Fin worldCount) :
    (tables.inherenceClosureTableCosted m b w).value =
      tables.inherenceClosureTable m b w := by
  unfold inherenceClosureTableCosted momentOfClosureCosted inherenceClosureTable
  rw [Complexity.closureLookupCosted_value]
  split <;> simp_all

/-!
Native dense queries use the counted algorithms with their costs erased.
The compact definitions above remain available to kernel proofs. Each native
substitution has an unconditional equality, including raw tables with missing
cells. This is the implementation-correspondence requirement emphasized by
Forster et al. (ITP 2021), separate from a bound on machine instructions.
-/

private def unaryTypedTableErased (tables : FactTables) (field : UnaryField)
    {thingCount worldCount : Nat} (x : Fin thingCount) (w : Fin worldCount) : Bool :=
  (tables.unaryTypedTableCosted field x w).value

@[csimp] theorem unaryTypedTableDense_eq_erased :
    @unaryTypedTableDense = @unaryTypedTableErased := by
  funext tables field thingCount worldCount x w
  exact (unaryTypedTableCosted_value_dense tables field x w).symm

private def binaryTypedTableErased (tables : FactTables) (field : BinaryField)
    {thingCount worldCount : Nat} (x y : Fin thingCount) (w : Fin worldCount) : Bool :=
  (tables.binaryTypedTableCosted field x y w).value

@[csimp] theorem binaryTypedTableDense_eq_erased :
    @binaryTypedTableDense = @binaryTypedTableErased := by
  funext tables field thingCount worldCount x y w
  exact (binaryTypedTableCosted_value_dense tables field x y w).symm

private def ternaryTypedTableErased (tables : FactTables) (field : TernaryField)
    {thingCount worldCount : Nat} (x y z : Fin thingCount) (w : Fin worldCount) : Bool :=
  (tables.ternaryTypedTableCosted field x y z w).value

@[csimp] theorem ternaryTypedTableDense_eq_erased :
    @ternaryTypedTableDense = @ternaryTypedTableErased := by
  funext tables field thingCount worldCount x y z w
  exact (ternaryTypedTableCosted_value_dense tables field x y z w).symm

private def tupleProjectionTypedTableErased (tables : FactTables)
    {thingCount worldCount : Nat} (p : Fin thingCount) (i : Nat) (w : Fin worldCount) :
    Fin thingCount := (tables.tupleProjectionTypedTableCosted p i w).value

@[csimp] theorem tupleProjectionTypedTableDense_eq_erased :
    @tupleProjectionTypedTableDense = @tupleProjectionTypedTableErased := by
  funext tables thingCount worldCount p i w
  exact (tupleProjectionTypedTableCosted_value_dense tables p i w).symm

private def inherenceClosureTableErased (tables : FactTables)
    {thingCount worldCount : Nat} (m b : Fin thingCount) (w : Fin worldCount) : Bool :=
  (tables.inherenceClosureTableCosted m b w).value

@[csimp] theorem inherenceClosureTable_eq_erased :
    @inherenceClosureTable = @inherenceClosureTableErased := by
  funext tables thingCount worldCount m b w
  exact (inherenceClosureTableCosted_value tables m b w).symm

/-- Pure Boolean table lookup for unary fields. -/
def unaryTable (tables : FactTables) (field : String)
    {thingCount worldCount : Nat}
    (x : Fin thingCount) (w : Fin worldCount) : Bool :=
  tables.unaryLookup field x.val w.val

/-- Pure Boolean table lookup for binary fields. -/
def binaryTable (tables : FactTables) (field : String)
    {thingCount worldCount : Nat}
    (x y : Fin thingCount) (w : Fin worldCount) : Bool :=
  tables.binaryLookup field x.val y.val w.val

/-- Pure Boolean table lookup for ternary fields. -/
def ternaryTable (tables : FactTables) (field : String)
    {thingCount worldCount : Nat}
    (x y z : Fin thingCount) (w : Fin worldCount) : Bool :=
  tables.ternaryLookup field x.val y.val z.val w.val

/--
Pure Boolean table lookup for reflexive binary fields.

`Part` and `Overlap` get identity by default, matching the original DSL emitter.
-/
def identityBinaryTable (tables : FactTables) (field : String)
    {thingCount worldCount : Nat}
    (x y : Fin thingCount) (w : Fin worldCount) : Bool :=
  x == y || binaryTable tables field x y w

/--
Depth-bounded reachability in a binary table.

For a generated finite model with `thingCount` things, any acyclic path can be
shortened to at most `thingCount` edges.  This is the computational side of the
transitive-closure view of `MomentOf`; proof-producing code can later connect
this Boolean result back to the inductive relation.
-/
partial def binaryReachableFrom
    (tables : FactTables) (field : String) (thingCount : Nat) (world start target : Nat)
    (fuel : Nat) (visited : Std.HashSet Nat) : Bool :=
  match fuel with
  | 0 => false
  | fuel + 1 =>
      Id.run do
        for next in [:thingCount] do
          if tables.binaryLookup field start next world then
            if next == target then
              return true
            else if !visited.contains next then
              if binaryReachableFrom tables field thingCount world next target fuel
                  (visited.insert next) then
                return true
        return false

/-- Transitive closure of a binary table in one world. -/
def binaryClosure
    (tables : FactTables) (field : String) (thingCount : Nat)
    (world start target : Nat) : Bool :=
  binaryReachableFrom tables field thingCount world start target thingCount
    (Std.HashSet.emptyWithCapacity.insert start)

/-- `MomentOf` is the transitive closure of `InheresIn` in a fixed world. -/
def momentOfClosure
    (tables : FactTables) (thingCount : Nat) (world moment bearer : Nat) : Bool :=
  match tables.inherenceClosures[world]? with
  | some closure =>
      closure[Complexity.matrixIndex thingCount moment bearer]?.getD false
  | none => false

/-- The counted query preserves the explicit-width lookup for all raw tables,
including missing worlds or cells. This proves lookup correspondence only.
Whether the matrix represents inherence reachability is a separate theorem. -/
theorem momentOfClosureCosted_value
    (tables : FactTables) (thingCount world moment bearer : Nat) :
    (tables.momentOfClosureCosted thingCount world moment bearer).value =
      tables.momentOfClosure thingCount world moment bearer := by
  unfold momentOfClosureCosted momentOfClosure
  rw [Complexity.closureLookupCosted_value]
  split <;> simp_all

/-- A next-hop cell gives the next coordinate toward a target. Fuel limits
how many cells the helper can follow, even in a cyclic raw table. The accumulator
stores both the path and the cost before the tail call.
Each continued hop costs eleven: equality and branch (two), fuel test (one),
index arithmetic (two), bounds comparison and branch (two), array read (one),
option test (one), path append (one), and loop step (one).
The input accumulator is supplied by the caller, which charges its creation.
Cost composition follows Niu et al. (POPL 2022, doi:10.1145/3498670). -/
def nextHopPathFromCosted
    (nextHop : Array (Option Nat)) (thingCount current target fuel : Nat)
    (pathAcc : Array Nat := #[]) : Complexity.Costed (Option (Array Nat)) :=
  go nextHop thingCount target fuel current pathAcc 0
where
  go (nextHop : Array (Option Nat)) (thingCount target fuel current : Nat)
      (pathAcc : Array Nat) (cost : Nat) : Complexity.Costed (Option (Array Nat)) :=
    if current == target then
      ⟨some (pathAcc.push current), cost + 3⟩
    else match fuel with
    | 0 => ⟨none, cost + 3⟩
    | fuel + 1 =>
        let index := Complexity.matrixIndex thingCount current target
        if h : index < nextHop.size then
          match nextHop[index] with
          | none => ⟨none, cost + 9⟩
          | some next => go nextHop thingCount target fuel next (pathAcc.push current) (cost + 11)
        else ⟨none, cost + 7⟩

private theorem nextHopPathFromCosted_go_value (nextHop : Array (Option Nat))
    (thingCount target fuel current : Nat) (pathAcc : Array Nat) (a b : Nat) :
    (nextHopPathFromCosted.go nextHop thingCount target fuel current pathAcc a).value =
      (nextHopPathFromCosted.go nextHop thingCount target fuel current pathAcc b).value := by
  induction fuel generalizing current pathAcc a b with
  | zero => simp only [nextHopPathFromCosted.go]; split <;> rfl
  | succ fuel ih =>
      simp only [nextHopPathFromCosted.go]
      split
      · rfl
      · split
        · split
          · rfl
          · exact ih _ _ _ _
        · rfl

/-- Erasing the accumulated cost yields the deterministic pointer-following
recurrence. This statement also specifies behavior on malformed raw tables. -/
theorem nextHopPathFromCosted_value_step
    (nextHop : Array (Option Nat)) (thingCount current target fuel : Nat) (pathAcc : Array Nat) :
    (nextHopPathFromCosted nextHop thingCount current target fuel pathAcc).value =
      if current == target then some (pathAcc.push current)
      else match fuel with
      | 0 => none
      | fuel + 1 =>
          match nextHop[Complexity.matrixIndex thingCount current target]?.join with
          | none => none
          | some next =>
              (nextHopPathFromCosted nextHop thingCount next target fuel (pathAcc.push current)).value := by
  rw [nextHopPathFromCosted, nextHopPathFromCosted.go.eq_def]
  split
  · rfl
  · cases fuel with
    | zero => rfl
    | succ fuel =>
        simp only [getElem?_def]
        split
        · dsimp only [Option.join, Option.bind, id]
          split
          · simp_all only
          · simp_all only
            exact nextHopPathFromCosted_go_value _ _ _ _ _ _ _ _
        · rfl

private theorem nextHopPathFromCosted_go_cost_le (nextHop : Array (Option Nat))
    (thingCount target fuel current : Nat) (pathAcc : Array Nat) (cost : Nat) :
    (nextHopPathFromCosted.go nextHop thingCount target fuel current pathAcc cost).cost ≤
      cost + 11 * fuel + 3 := by
  induction fuel generalizing current pathAcc cost with
  | zero => simp only [nextHopPathFromCosted.go]; split <;> simp
  | succ fuel ih =>
      simp only [nextHopPathFromCosted.go]
      split
      · simp
      · split
        · split
          · simp; omega
          · apply Nat.le_trans (ih _ _ _)
            omega
        · simp; omega

theorem nextHopPathFromCosted_cost_le
    (nextHop : Array (Option Nat)) (thingCount current target fuel : Nat)
    (pathAcc : Array Nat) :
    (nextHopPathFromCosted nextHop thingCount current target fuel pathAcc).cost ≤
      11 * fuel + 3 := by
  simpa [nextHopPathFromCosted] using
    nextHopPathFromCosted_go_cost_le nextHop thingCount target fuel current pathAcc 0

/-- A successful call appends at most one coordinate per hop and the endpoint.
This bounds later path rendering even when the supplied table is malformed. -/
theorem nextHopPathFromCosted_some_size
    (nextHop : Array (Option Nat)) (thingCount current target fuel : Nat)
    (pathAcc path : Array Nat)
    (found : (nextHopPathFromCosted nextHop thingCount current target fuel pathAcc).value = some path) :
    path.size ≤ pathAcc.size + fuel + 1 := by
  induction fuel generalizing current pathAcc with
  | zero =>
      rw [nextHopPathFromCosted_value_step] at found
      split at found
      · cases Option.some.inj found
        simp
      · cases found
  | succ fuel ih =>
      rw [nextHopPathFromCosted_value_step] at found
      dsimp only at found
      split at found
      · cases Option.some.inj found
        simp
      · split at found
        · cases found
        · have h := ih _ _ found
          simp only [Array.size_push] at h
          omega

def nextHopPathFrom?
    (nextHop : Array (Option Nat)) (thingCount current target fuel : Nat) :
    Option (Array Nat) :=
  (nextHopPathFromCosted nextHop thingCount current target fuel).value

@[simp] theorem nextHopPathFromCosted_value
    (nextHop : Array (Option Nat)) (thingCount current target fuel : Nat) :
    (nextHopPathFromCosted nextHop thingCount current target fuel).value =
      nextHopPathFrom? nextHop thingCount current target fuel := rfl

/-- Read the world's next-hop matrix and construct a path accumulator.
The successful matrix read costs three operations, and initialization costs one.
A missing world costs only its bounds comparison and branch. -/
def momentOfPathCosted
    (tables : FactTables) (thingCount : Nat) (world moment bearer : Nat) :
    Complexity.Costed (Option (Array Nat)) :=
  if hw : world < tables.inherenceNextHops.size then
    Complexity.Costed.charge 4
      (nextHopPathFromCosted tables.inherenceNextHops[world] thingCount moment bearer thingCount)
  else .tick none 2

def momentOfPath?
    (tables : FactTables) (thingCount : Nat) (world moment bearer : Nat) :
    Option (Array Nat) :=
  (tables.momentOfPathCosted thingCount world moment bearer).value

/-- The world guard preserves optional matrix lookup, including a missing world. -/
theorem momentOfPathCosted_value_cases
    (tables : FactTables) (thingCount world moment bearer : Nat) :
    (tables.momentOfPathCosted thingCount world moment bearer).value =
      match tables.inherenceNextHops[world]? with
      | none => none
      | some nextHop => (nextHopPathFromCosted nextHop thingCount moment bearer thingCount).value := by
  simp only [momentOfPathCosted, getElem?_def]
  split <;> rfl

@[simp] theorem momentOfPathCosted_value
    (tables : FactTables) (thingCount : Nat) (world moment bearer : Nat) :
    (tables.momentOfPathCosted thingCount world moment bearer).value =
      tables.momentOfPath? thingCount world moment bearer := rfl

theorem momentOfPathCosted_cost_le
    (tables : FactTables) (thingCount : Nat) (world moment bearer : Nat) :
    (tables.momentOfPathCosted thingCount world moment bearer).cost ≤
      11 * thingCount + 7 := by
  unfold momentOfPathCosted
  split
  · have h := nextHopPathFromCosted_cost_le tables.inherenceNextHops[world]
      thingCount moment bearer thingCount #[]
    simp only [Complexity.Costed.charge_cost]
    omega
  · simp

theorem momentOfPathCosted_some_size
    (tables : FactTables) (thingCount world moment bearer : Nat) (path : Array Nat)
    (found : (tables.momentOfPathCosted thingCount world moment bearer).value = some path) :
    path.size ≤ thingCount + 1 := by
  unfold momentOfPathCosted at found
  split at found
  · simp only [Complexity.Costed.charge_value] at found
    simpa using nextHopPathFromCosted_some_size _ _ _ _ _ #[] path found
  · cases found

/-- Four primitive lookup families with fixed finite coordinate domains. -/
structure TableLookups (worldCount thingCount : Nat) where
  unary : UnaryField → Fin thingCount → Fin worldCount → Bool
  binary : BinaryField → Fin thingCount → Fin thingCount → Fin worldCount → Bool
  ternary : TernaryField → Fin thingCount → Fin thingCount → Fin thingCount →
    Fin worldCount → Bool
  projectionCosted : Fin thingCount → Nat → Fin worldCount → Complexity.Costed (Fin thingCount)
  projectionCost_le : ∀ p i w, (projectionCosted p i w).cost ≤ 11

/-- The ordinary projection uses the value from the same counted lookup. -/
def TableLookups.projection (lookups : TableLookups worldCount thingCount)
    (p : Fin thingCount) (i : Nat) (w : Fin worldCount) : Fin thingCount :=
  (lookups.projectionCosted p i w).value

def sparseLookups (worldCount thingCount : Nat) (tables : FactTables) :
    TableLookups worldCount thingCount :=
  ⟨fun field => tables.unaryTypedTable field,
    fun field => tables.binaryTypedTable field, fun field => tables.ternaryTypedTable field,
    fun p i w => ⟨tables.tupleProjectionTypedTable p i w,
      (tables.tupleProjectionTypedTableCosted p i w).cost⟩,
    fun p i w => tables.tupleProjectionTypedTableCosted_cost_le p i w⟩

def denseLookups (worldCount thingCount : Nat) (tables : FactTables) :
    TableLookups worldCount thingCount :=
  ⟨fun field => tables.unaryTypedTableDense field,
    fun field => tables.binaryTypedTableDense field,
    fun field => tables.ternaryTypedTableDense field, tables.tupleProjectionTypedTableCosted,
    fun p i w => tables.tupleProjectionTypedTableCosted_cost_le p i w⟩

/--
The proof argument makes sparse/dense agreement a precondition of native
replacement. Raw intermediate tables need not satisfy it. The coordinate
dimensions occur in the equality, so a caller cannot reuse a proof for a
different finite domain.

This follows the verified-representation principle illustrated by de Moura's
RadixExperiment: the executable replacement has a theorem at its API boundary.
It establishes equal values, not equal costs between the two representations.
The projection field carries the dense evaluator's cost in both bundles.
Native replacement returns its value and cost from one lookup. The sparse
bundle's attached counter does not measure sparse kernel reduction.
-/
def verifiedLookups (worldCount thingCount : Nat) (tables : FactTables)
    (_agreement : sparseLookups worldCount thingCount tables =
      denseLookups worldCount thingCount tables) : TableLookups worldCount thingCount :=
  sparseLookups worldCount thingCount tables

def verifiedLookupsDense (worldCount thingCount : Nat) (tables : FactTables)
    (_agreement : sparseLookups worldCount thingCount tables =
      denseLookups worldCount thingCount tables) : TableLookups worldCount thingCount :=
  denseLookups worldCount thingCount tables

/-- Compiler simplification uses a checked function equality. There is no
unproved `implemented_by` override, including for malformed raw tables. -/
@[csimp] theorem verifiedLookups_eq_dense :
    verifiedLookups = verifiedLookupsDense := by
  funext worldCount thingCount tables agreement
  exact agreement


/--
Assemble the finite-model record from converted product-family witnesses.

This pure constructor defines the finite-model record fields used by generated
DSL models. Primitive distance, set-membership, and tuple-projection tables are
read from the DSL facts; higher-arity definition-like relations that are not
primitive surface syntax remain derived in `FiniteModel4.toUFOSignature4`.
Every relation field installs a function; assembly does not call the relation.
The caller therefore charges witness conversion separately, then one fixed
record construction. Closure allocation and record projections are outside the
unit-cost model. The stored functions' query costs belong to their consumers.
-/
private def assembleFiniteModel4
    (worldCount thingCount : Nat)
    (worldPositive : 0 < worldCount)
    (thingPositive : 0 < thingCount)
    (tables : FactTables) (lookups : TableLookups worldCount thingCount)
    (families : Array (ProductFamilyWitness thingCount worldCount)) : FiniteModel4 :=
{ worldCount := worldCount
  thingCount := thingCount
  worldPositive := worldPositive
  thingPositive := thingPositive

  inst := lookups.binary .inst
  sub := lookups.binary .sub

  concreteIndividual := lookups.unary .concreteIndividual
  abstractIndividual := lookups.unary .abstractIndividual
  endurant := lookups.unary .endurant
  perdurant := lookups.unary .perdurant
  endurantType := lookups.unary .endurantType
  perdurantType := lookups.unary .perdurantType
  rigid := lookups.unary .rigid
  antiRigid := lookups.unary .antiRigid
  semiRigid := lookups.unary .semiRigid
  kind := lookups.unary .kind
  sortal := lookups.unary .sortal
  nonSortal := lookups.unary .nonSortal
  subKind := lookups.unary .subKind
  phase := lookups.unary .phase
  role := lookups.unary .role
  semiRigidSortal := lookups.unary .semiRigidSortal
  category := lookups.unary .category
  mixin := lookups.unary .mixin
  phaseMixin := lookups.unary .phaseMixin
  roleMixin := lookups.unary .roleMixin

  substantial := lookups.unary .substantial
  moment := lookups.unary .moment
  object := lookups.unary .object
  collective := lookups.unary .collective
  quantity := lookups.unary .quantity
  relator := lookups.unary .relator
  intrinsicMoment := lookups.unary .intrinsicMoment
  mode := lookups.unary .mode
  qualityKind := lookups.unary .qualityKind

  substantialType := lookups.unary .substantialType
  momentType := lookups.unary .momentType
  objectType := lookups.unary .objectType
  collectiveType := lookups.unary .collectiveType
  quantityType := lookups.unary .quantityType
  relatorType := lookups.unary .relatorType
  modeType := lookups.unary .modeType
  qualityType := lookups.unary .qualityType
  objectKind := lookups.unary .objectKind
  collectiveKind := lookups.unary .collectiveKind
  quantityKind := lookups.unary .quantityKind
  relatorKind := lookups.unary .relatorKind
  modeKind := lookups.unary .modeKind

  part := fun x y w => x == y || lookups.binary .part x y w
  overlap := fun x y w => x == y || lookups.binary .overlap x y w
  properPart := lookups.binary .properPart

  functionsAs := lookups.binary .functionsAs
  genericFunctionalDependence := tables.binaryTable "genericFunctionalDependence"
  individualFunctionalDependence := fun _ _ _ _ _ => false
  componentOf := fun _ _ _ _ _ => false

  ex := lookups.unary .ex
  constitutedBy := lookups.binary .constitutedBy
  genericConstitutionalDependence := tables.binaryTable "genericConstitutionalDependence"
  constitution := fun _ _ _ _ _ => false

  existentialDependence := tables.binaryTable "existentialDependence"
  existentialIndependence := tables.binaryTable "existentialIndependence"
  inheresIn := lookups.binary .inheresIn

  externallyDependent := tables.binaryTable "externallyDependent"
  externallyDependentMode := tables.unaryTable "externallyDependentMode"
  foundedBy := lookups.binary .foundedBy
  quaIndividualOf := lookups.binary .quaIndividualOf
  quaIndividual := tables.unaryTable "quaIndividual"
  mediates := lookups.binary .mediates

  characterization := lookups.binary .characterization

  quale := lookups.unary .quale
  set_ := lookups.unary .set_
  memberOf := lookups.binary .memberOf
  setExtension := fun s w => {x | lookups.binary .memberOf x s w = true}
  qualityDomain := lookups.unary .qualityDomain
  qualityDimension := lookups.unary .qualityDimension
  associatedWith := lookups.binary .associatedWith
  intrinsicMomentType := lookups.unary .intrinsicMomentType
  hasValue := lookups.binary .hasValue
  /- Install the counted callback directly: computing its value and cost in
  separate lookups would repeat work that the returned counter charges once.
  Verified lookup replacement preserves compact kernel reduction and runs
  the dense counted evaluator once per native query. -/
  tupleProjectionCosted := fun {_n} p i w => lookups.projectionCosted p i.val w
  tupleProjectionCost_le := fun p i w => lookups.projectionCost_le p i.val w
  productFamilies := families
  distance := lookups.ternary .distance
  distanceZero := lookups.unary .distanceZero
  distanceSum := lookups.ternary .distanceSum
  distanceGreaterEq := lookups.binary .distanceGreaterEq

  manifests := lookups.binary .manifests
  lifeOf := lookups.binary .lifeOf
  meet := lookups.binary .meet }

/-- Convert witnesses before assembling the fixed record. This counts the
array computation itself, not only its insertion into the resulting model.
The separation of cost and value follows the cost-aware semantics of Niu et al.
(POPL 2022), doi:10.1145/3498670; the value theorem below covers every field. -/
def toFiniteModel4WithLookupsCosted
    (worldCount thingCount : Nat)
    (worldPositive : 0 < worldCount) (thingPositive : 0 < thingCount)
    (tables : FactTables) (lookups : TableLookups worldCount thingCount) :
    Complexity.Costed FiniteModel4 :=
  (productFamilyWitnessesCosted worldCount thingCount tables.productFamilies).bind fun families =>
    .tick (assembleFiniteModel4 worldCount thingCount worldPositive thingPositive
      tables lookups families) 1

def toFiniteModel4WithLookups
    (worldCount thingCount : Nat)
    (worldPositive : 0 < worldCount) (thingPositive : 0 < thingCount)
    (tables : FactTables) (lookups : TableLookups worldCount thingCount) : FiniteModel4 :=
  (toFiniteModel4WithLookupsCosted worldCount thingCount worldPositive thingPositive
    tables lookups).value

/-- Instrumentation preserves the complete record assembled from the ordinary
converted witnesses, including the function-valued relation fields. -/
theorem toFiniteModel4WithLookupsCosted_value
    (W T : Nat) (hw : 0 < W) (ht : 0 < T)
    (tables : FactTables) (lookups : TableLookups W T) :
    (toFiniteModel4WithLookupsCosted W T hw ht tables lookups).value =
      assembleFiniteModel4 W T hw ht tables lookups (productFamilyWitnesses W T tables.productFamilies) := rfl

theorem toFiniteModel4WithLookupsCosted_cost
    (W T : Nat) (hw : 0 < W) (ht : 0 < T)
    (tables : FactTables) (lookups : TableLookups W T) :
    (toFiniteModel4WithLookupsCosted W T hw ht tables lookups).cost =
      (productFamilyWitnessesCosted W T tables.productFamilies).cost + 1 := rfl

/-- The sparse lookup bundle is a fixed record of four functions. Constructing
it costs one; no table lookup runs until a consumer supplies coordinates. -/
def toFiniteModel4Costed
    (worldCount thingCount : Nat)
    (worldPositive : 0 < worldCount) (thingPositive : 0 < thingCount)
    (tables : FactTables) : Complexity.Costed FiniteModel4 :=
  .charge 1 (toFiniteModel4WithLookupsCosted worldCount thingCount worldPositive thingPositive
    tables (sparseLookups worldCount thingCount tables))

/-- Interpret raw tables without assuming sparse/dense agreement. -/
def toFiniteModel4
    (worldCount thingCount : Nat)
    (worldPositive : 0 < worldCount) (thingPositive : 0 < thingCount)
    (tables : FactTables) : FiniteModel4 :=
  (toFiniteModel4Costed worldCount thingCount worldPositive thingPositive tables).value

/-- The verified lookup bundle has the same fixed construction cost as the
sparse bundle. Its equality proof authorizes dense native evaluation without
changing any field value. Proof checking is outside the execution cost. -/
def toFiniteModel4VerifiedCosted
    (worldCount thingCount : Nat)
    (worldPositive : 0 < worldCount) (thingPositive : 0 < thingCount)
    (tables : FactTables)
    (agreement : sparseLookups worldCount thingCount tables =
      denseLookups worldCount thingCount tables) : Complexity.Costed FiniteModel4 :=
  .charge 1 (toFiniteModel4WithLookupsCosted worldCount thingCount worldPositive thingPositive
    tables (verifiedLookups worldCount thingCount tables agreement))

/-- Interpret compiled tables using dense native lookup only when its agreement
with the proof-facing lookup is proved for these exact tables and dimensions. -/
def toFiniteModel4Verified
    (worldCount thingCount : Nat)
    (worldPositive : 0 < worldCount) (thingPositive : 0 < thingCount)
    (tables : FactTables)
    (agreement : sparseLookups worldCount thingCount tables =
      denseLookups worldCount thingCount tables) : FiniteModel4 :=
  (toFiniteModel4VerifiedCosted worldCount thingCount worldPositive thingPositive
    tables agreement).value

theorem toFiniteModel4VerifiedCosted_eq
    (W T : Nat) (hw : 0 < W) (ht : 0 < T) (tables : FactTables) (agreement) :
    toFiniteModel4VerifiedCosted W T hw ht tables agreement =
      toFiniteModel4Costed W T hw ht tables := rfl

/-- Witness conversion is the only input-sized construction work. The two
additional operations assemble the lookup bundle and the finite-model record. -/
theorem toFiniteModel4Costed_cost
    (W T : Nat) (hw : 0 < W) (ht : 0 < T) (tables : FactTables) :
    (toFiniteModel4Costed W T hw ht tables).cost =
      (productFamilyWitnessesCosted W T tables.productFamilies).cost + 2 := by
  simp only [toFiniteModel4Costed, Complexity.Costed.charge_cost,
    toFiniteModel4WithLookupsCosted_cost]
  omega

theorem toFiniteModel4VerifiedCosted_cost_le
    (W T : Nat) (hw : 0 < W) (ht : 0 < T) (tables : FactTables) (agreement) :
    (toFiniteModel4VerifiedCosted W T hw ht tables agreement).cost ≤
      3 + W * (7 * (tables.productFamilies.toList.map (fun family =>
        family.dimensionThings.size + family.typeThings.size)).sum +
        20 * tables.productFamilies.size) + 2 * tables.productFamilies.size := by
  rw [toFiniteModel4VerifiedCosted_eq, toFiniteModel4Costed_cost]
  have bound := productFamilyWitnessesCosted_cost_le_slots W T tables.productFamilies
  omega

theorem toFiniteModel4Verified_eq
    (worldCount thingCount : Nat)
    (worldPositive : 0 < worldCount) (thingPositive : 0 < thingCount)
    (tables : FactTables) (agreement) :
    toFiniteModel4Verified worldCount thingCount worldPositive thingPositive
      tables agreement =
    toFiniteModel4 worldCount thingCount worldPositive thingPositive tables := rfl
end FactTables

/-- Compile a resolved AST all the way to a finite UFO model. -/
def compileModel
    (ast : ModelAST)
    (worldPositive : 0 < ast.worldCount)
    (thingPositive : 0 < ast.thingCount) : FiniteModel4 :=
  (compileModelAST ast).toFiniteModel4
    ast.worldCount ast.thingCount worldPositive thingPositive

/-- Compile an already-expanded resolved AST all the way to a finite UFO model. -/
def compileExplicitModel
    (ast : ModelAST)
    (worldPositive : 0 < ast.worldCount)
    (thingPositive : 0 < ast.thingCount) : FiniteModel4 :=
  (compileExplicitModelAST ast).toFiniteModel4
    ast.worldCount ast.thingCount worldPositive thingPositive

/--
Make reflexive-specialization closure explicit at the AST level.

This function is useful for generated declarations: certificates reduce much
better when all facts are syntactically present in the AST and table lookup does
not have to evaluate `HashSet.toArray` during proof search.
-/
private def pushAll (out added : Array α) : Array α :=
  added.foldl (fun out item => out.push item) out

private theorem pushAll_size (out added : Array α) :
    (pushAll out added).size = out.size + added.size := by
  unfold pushAll
  rw [← Array.foldl_toList]
  have listSize : ∀ (xs : List α) (initial : Array α),
      (xs.foldl (fun result item => result.push item) initial).size =
        initial.size + xs.length := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih =>
        intro initial
        simp only [List.foldl_cons, List.length_cons]
        rw [ih]
        simp
        omega
  simpa using listSize added.toList out

private def reflexiveSpecializationFactsFor
    (worldCount target : Nat) : Array CompiledFact :=
  (Array.range worldCount).map fun world => .binary .sub target target world

@[simp] theorem reflexiveSpecializationFactsFor_size
    (worldCount target : Nat) :
    (reflexiveSpecializationFactsFor worldCount target).size = worldCount := by
  simp [reflexiveSpecializationFactsFor]

/-- Pure specification: keep the original facts as a prefix, then append
reflexive witnesses in input order and ascending world order. Repeated targets
remain repeated; dense-table insertion later treats those facts idempotently. -/
private def addReflexiveSpecializationFactsCore
    (worldCount : Nat) (facts : Array CompiledFact) : Array CompiledFact :=
  facts.foldl (fun out fact => match fact with
    | .binary .inst _ target _ =>
        pushAll out (reflexiveSpecializationFactsFor worldCount target)
    | _ => out) facts

theorem addReflexiveSpecializationFactsCore_size_le
    (worldCount : Nat) (facts : Array CompiledFact) :
    (addReflexiveSpecializationFactsCore worldCount facts).size ≤
      facts.size * (worldCount + 1) := by
  have listBound : ∀ (xs : List CompiledFact) (out : Array CompiledFact),
      (xs.foldl (fun out fact => match fact with
        | .binary .inst _ target _ =>
            pushAll out (reflexiveSpecializationFactsFor worldCount target)
        | _ => out) out).size ≤
        out.size + xs.length * worldCount := by
    intro xs
    induction xs with
    | nil => simp
    | cons fact facts ih =>
        intro out
        let nextOut := match fact with
          | .binary .inst _ target _ =>
              pushAll out (reflexiveSpecializationFactsFor worldCount target)
          | _ => out
        have hnext : nextOut.size ≤ out.size + worldCount := by
          cases fact with
          | binary field left right world =>
              cases field <;> simp [nextOut, pushAll_size]
          | _ => simp [nextOut]
        have htail := ih nextOut
        simp only [List.foldl_cons]
        exact htail.trans (by
          simp only [List.length_cons, Nat.succ_mul]
          omega)
  have h := listBound facts.toList facts
  simpa [addReflexiveSpecializationFactsCore, ← Array.foldl_toList, Nat.mul_add,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

/-- Test the fact constructor and, for binary facts, whether its field is
instantiation. Each emitted witness charges a numeric iteration, fact
construction, and output write. No world-range or witness array is allocated. -/
private def reflexiveSpecializationStepCosted
    (worldCount : Nat) (out : Array CompiledFact) (fact : CompiledFact) :
    Complexity.Costed (Array CompiledFact) :=
  Complexity.Costed.charge 1 <| match fact with
    | .binary field _ target _ =>
        Complexity.Costed.branch (.tick (decide (field = .inst)))
          (fun _ => Complexity.Costed.foldFin worldCount out fun output world =>
            Complexity.Costed.tick (output.push (.binary .sub target target world.val)) 2)
          (fun _ => .pure out)
    | _ => .pure out

private theorem reflexiveSpecializationStepCosted_value
    (worldCount : Nat) (out : Array CompiledFact) (fact : CompiledFact) :
    (reflexiveSpecializationStepCosted worldCount out fact).value = (match fact with
      | .binary .inst _ target _ =>
          pushAll out (reflexiveSpecializationFactsFor worldCount target)
      | _ => out) := by
  cases fact with
  | binary field left target world =>
      cases field <;> simp [reflexiveSpecializationStepCosted,
        Complexity.Costed.foldFin_value, Complexity.Costed.tick, foldFin_push_eq_append]
      have eq := Array.foldl_push_eq_append
        (as := reflexiveSpecializationFactsFor worldCount target) (bs := out) (f := id) rfl
      simpa [pushAll, reflexiveSpecializationFactsFor, Array.range, Function.comp_def] using eq.symm
  | _ => rfl

/-- Copy the original prefix with counted writes, then append witnesses to the
same output. Explicit copying accounts for the prefix without relying on an
uncharged copy-on-write clone when the input is still shared by traversal. -/
def addReflexiveSpecializationFactsCosted
    (worldCount : Nat) (facts : Array CompiledFact) :
    Complexity.Costed (Array CompiledFact) := do
  let out ← Complexity.Costed.foldArray facts #[] fun out fact =>
    Complexity.Costed.tick (out.push fact) 1
  Complexity.Costed.foldArray facts out (reflexiveSpecializationStepCosted worldCount)

private theorem addReflexiveSpecializationFactsCosted_value_eq_core
    (worldCount : Nat) (facts : Array CompiledFact) :
    (addReflexiveSpecializationFactsCosted worldCount facts).value =
      addReflexiveSpecializationFactsCore worldCount facts := by
  simp only [addReflexiveSpecializationFactsCosted, Bind.bind, Complexity.Costed.bind_value,
    Complexity.Costed.foldArray_value, Complexity.Costed.tick,
    reflexiveSpecializationStepCosted_value]
  have copy := Array.foldl_push_eq_append (as := facts) (bs := #[]) (f := id) rfl
  simp only [Array.map_id, id_eq, Array.empty_append] at copy
  rw [copy]
  rfl

def addReflexiveSpecializationFacts
    (worldCount : Nat) (facts : Array CompiledFact) : Array CompiledFact :=
  (addReflexiveSpecializationFactsCosted worldCount facts).value

@[simp] theorem addReflexiveSpecializationFactsCosted_value
    (worldCount : Nat) (facts : Array CompiledFact) :
    (addReflexiveSpecializationFactsCosted worldCount facts).value =
      addReflexiveSpecializationFacts worldCount facts := rfl

theorem addReflexiveSpecializationFactsCosted_value_size_le
    (worldCount : Nat) (facts : Array CompiledFact) :
    (addReflexiveSpecializationFactsCosted worldCount facts).value.size ≤
      facts.size * (worldCount + 1) := by
  rw [addReflexiveSpecializationFactsCosted_value_eq_core]
  exact addReflexiveSpecializationFactsCore_size_le worldCount facts

theorem addReflexiveSpecializationFactsCosted_projectionArity_le
    (worldCount : Nat) (facts : Array CompiledFact) :
    projectionArityOfFacts
      (addReflexiveSpecializationFactsCosted worldCount facts).value ≤
      projectionArityOfFacts facts := by
  have listBound : ∀ (xs : List CompiledFact) (out : Array CompiledFact)
      (bound : Nat),
      projectionArityOfFacts out ≤ bound →
      projectionArityOfFacts
        (xs.foldl (fun out fact => match fact with
          | .binary .inst _ target _ =>
              pushAll out (reflexiveSpecializationFactsFor worldCount target)
          | _ => out) out) ≤ bound := by
    intro xs
    induction xs with
    | nil => simp
    | cons fact facts ih =>
        intro out bound hOut
        simp only [List.foldl_cons]
        apply ih
        cases fact with
        | binary field left target world =>
            cases field <;> try exact hOut
            apply foldPush_projectionArity_le _ _ bound hOut
            intro emitted hEmitted
            simp [reflexiveSpecializationFactsFor] at hEmitted
            rcases hEmitted with ⟨_, ⟨_, rfl⟩⟩
            simp
        | _ => exact hOut
  rw [addReflexiveSpecializationFactsCosted_value_eq_core]
  unfold addReflexiveSpecializationFactsCore
  rw [← Array.foldl_toList]
  exact listBound facts.toList facts (projectionArityOfFacts facts) le_rfl

/-- Copying costs three operations per input. The second scan costs at most
five per input plus three per emitted world-indexed witness. -/
theorem addReflexiveSpecializationFactsCosted_cost_le
    (worldCount : Nat) (facts : Array CompiledFact) :
    (addReflexiveSpecializationFactsCosted worldCount facts).cost ≤
      facts.size * (3 * worldCount + 8) := by
  have stepBound (out : Array CompiledFact) (fact : CompiledFact) :
      (reflexiveSpecializationStepCosted worldCount out fact).cost ≤ 3 * worldCount + 3 := by
    cases fact with
    | binary field left target world =>
        have loopCost := Complexity.Costed.foldFin_cost_eq worldCount out
          (fun output world => Complexity.Costed.tick
            (output.push (CompiledFact.binary .sub target target world.val)) 2)
          2 (by intro _ _; rfl)
        cases field <;>
          simp [reflexiveSpecializationStepCosted, Complexity.Costed.branch,
            loopCost, Nat.mul_comm]
        omega
    | _ => simp [reflexiveSpecializationStepCosted]
  have copyCost := Complexity.Costed.foldArray_cost_eq facts #[]
    (fun out fact => Complexity.Costed.tick (out.push fact) 1) 1 (by intro _ _ _; rfl)
  have tailCost := Complexity.Costed.foldArray_cost_le facts
    (Complexity.Costed.foldArray facts #[]
      (fun out fact => Complexity.Costed.tick (out.push fact) 1)).value
    (reflexiveSpecializationStepCosted worldCount) (3 * worldCount + 3)
    (fun out fact _ => stepBound out fact)
  simp only [addReflexiveSpecializationFactsCosted, Bind.bind,
    Complexity.Costed.bind_cost, copyCost]
  calc
    _ ≤ facts.size * (1 + 2) + facts.size * (3 * worldCount + 3 + 2) :=
      Nat.add_le_add_left tailCost _
    _ = facts.size * (3 * worldCount + 8) := by
      simp [Nat.mul_add]
      omega

example : (addReflexiveSpecializationFactsCosted 2 #[
    .binary .inst 0 1 0, .binary .inst 2 1 1]).value.size = 6 := by
  native_decide

example : (addReflexiveSpecializationFactsCosted 2 #[
    .binary .inst 0 1 0, .binary .inst 2 1 1]).cost = 28 := by
  native_decide

/-- Finite structural taxonomy closure, independent of model coordinates. -/
def expandUnaryTaxonomyFields (field : UnaryField) : Array UnaryField :=
  Complexity.Taxonomy.ancestors field

private def appendUnaryTaxonomyCosted (field : UnaryField) (x w : Nat)
    (out : Array CompiledFact) : Complexity.Costed (Array CompiledFact) := do
  let ancestors ← Complexity.Taxonomy.ancestorsCosted field
  Complexity.Costed.foldArray ancestors out fun out ancestor =>
    Complexity.Costed.tick (out.push (.unary ancestor x w)) 1

private theorem appendUnaryTaxonomyCosted_value (field : UnaryField) (x w : Nat)
    (out : Array CompiledFact) :
    (appendUnaryTaxonomyCosted field x w out).value =
      out ++ (expandUnaryTaxonomyFields field).map (fun ancestor => .unary ancestor x w) := by
  simp only [appendUnaryTaxonomyCosted, Bind.bind, Complexity.Costed.bind_value,
    Complexity.Costed.foldArray_value, Complexity.Costed.tick]
  exact Array.foldl_push_eq_append rfl

private theorem appendUnaryTaxonomyCosted_cost (field : UnaryField) (x w : Nat)
    (out : Array CompiledFact) :
    (appendUnaryTaxonomyCosted field x w out).cost =
      (Complexity.Taxonomy.ancestorsCosted field).cost +
        3 * (expandUnaryTaxonomyFields field).size := by
  simp only [appendUnaryTaxonomyCosted, Bind.bind, Complexity.Costed.bind_cost]
  rw [Complexity.Costed.foldArray_cost_eq _ _ _ 1 (by intro _ _ _; rfl)]
  simp [expandUnaryTaxonomyFields, Nat.mul_comm]

def expandUnaryTaxonomyFactCosted (field : UnaryField) (x w : Nat) :
    Complexity.Costed (Array CompiledFact) :=
  appendUnaryTaxonomyCosted field x w #[]

/-- Expand one unary fact into itself plus deterministic taxonomy ancestors. -/
def expandUnaryTaxonomyFact (field : UnaryField) (x w : Nat) : Array CompiledFact :=
  (expandUnaryTaxonomyFactCosted field x w).value

@[simp] theorem expandUnaryTaxonomyFact_eq_map (field : UnaryField) (x w : Nat) :
    expandUnaryTaxonomyFact field x w =
      (expandUnaryTaxonomyFields field).map (fun ancestor => .unary ancestor x w) := by
  simp [expandUnaryTaxonomyFact, expandUnaryTaxonomyFactCosted,
    appendUnaryTaxonomyCosted_value]

@[simp] theorem expandUnaryTaxonomyFact_size
    (field : UnaryField) (x w : Nat) :
    (expandUnaryTaxonomyFact field x w).size =
      (expandUnaryTaxonomyFields field).size := by
  simp

def NamedScopedFact.taxonomyWeight (worldCount : Nat)
    (fact : NamedScopedFact) : Nat :=
  let multiplicity := fact.expansionWeight worldCount
  match fact.unaryField? with
  | some field => multiplicity * (expandUnaryTaxonomyFields field).size
  | none => multiplicity

def ScopedCompiledFact.taxonomyWeight (worldCount : Nat)
    (fact : ScopedCompiledFact) : Nat :=
  let multiplicity := fact.expansionWeight worldCount
  match fact.unaryField? with
  | some field => multiplicity * (expandUnaryTaxonomyFields field).size
  | none => multiplicity

theorem resolveNamedFactIndexed_preserves_weights
    (worldCount : Nat) (worlds things : NameIndex) (named : NamedScopedFact)
    (resolved : ScopedCompiledFact)
    (h : resolveNamedFactIndexed worlds things named = .ok resolved) :
    resolved.expansionWeight worldCount = named.expansionWeight worldCount ∧
      resolved.taxonomyWeight worldCount = named.taxonomyWeight worldCount := by
  have shape := resolveNamedFactIndexed_preserves_metric_shape
    worldCount worlds things named resolved h
  constructor
  · exact shape.1
  · simp [ScopedCompiledFact.taxonomyWeight, NamedScopedFact.taxonomyWeight,
      ScopedCompiledFact.expansionWeight, NamedScopedFact.expansionWeight,
      shape.1, shape.2]

set_option maxHeartbeats 800000 in
theorem resolveNamedFactIndexed_preserves_projectionArity
    (worlds things : NameIndex) (named : NamedScopedFact)
    (resolved : ScopedCompiledFact)
    (h : resolveNamedFactIndexed worlds things named = .ok resolved) :
    resolved.projectionArity = named.projectionArity := by
  unfold resolveNamedFactIndexed at h
  cases named with
  | unary field thing scope =>
      simp [resolveNamedFactIndexedCosted, exceptBindCosted,
        resolveThingIndexedCosted, resolveScopeIndexedCosted,
        resolveWorldIndexedCosted, NameIndex.findCosted] at h
      repeat' first | split at h | simp_all
      all_goals subst resolved
      all_goals simp
  | binary field left right scope =>
      simp [resolveNamedFactIndexedCosted, exceptBindCosted,
        resolveThingIndexedCosted, resolveScopeIndexedCosted,
        resolveWorldIndexedCosted, NameIndex.findCosted] at h
      repeat' first | split at h | simp_all
      all_goals subst resolved
      all_goals simp
  | ternary field first second third scope =>
      simp [resolveNamedFactIndexedCosted, exceptBindCosted,
        resolveThingIndexedCosted, resolveScopeIndexedCosted,
        resolveWorldIndexedCosted, NameIndex.findCosted] at h
      repeat' first | split at h | simp_all
      all_goals subst resolved
      all_goals simp
  | tupleProjection tuple index result scope =>
      simp [resolveNamedFactIndexedCosted, exceptBindCosted,
        resolveThingIndexedCosted, resolveScopeIndexedCosted,
        resolveWorldIndexedCosted, NameIndex.findCosted] at h
      repeat' first | split at h | simp_all
      all_goals subst resolved
      all_goals simp
  | derived fact scope =>
      cases fact <;>
        simp [resolveNamedFactIndexedCosted, resolveDerivedFactIndexedCosted,
          exceptBindCosted, resolveThingIndexedCosted,
          resolveScopeIndexedCosted, resolveWorldIndexedCosted,
          NameIndex.findCosted] at h <;>
        repeat' first | split at h | simp_all
      all_goals subst resolved
      all_goals simp

theorem resolveNamedFactsIndexed_preserves_projectionArity
    (worlds things : NameIndex)
    (named : Array NamedScopedFact) (resolved : Array ScopedCompiledFact)
    (h : (mapArrayExceptCosted named
      (resolveNamedFactIndexedCosted worlds things)).value = .ok resolved) :
    projectionArityOfScopedFacts resolved = projectionArityOfNamedFacts named := by
  have preserved := mapArrayExceptCosted_preserves_maxWeight named
    (resolveNamedFactIndexedCosted worlds things)
    NamedScopedFact.projectionArity ScopedCompiledFact.projectionArity
    (fun source result hResult =>
      resolveNamedFactIndexed_preserves_projectionArity
        worlds things source result hResult)
    resolved h
  simpa [projectionArityOfScopedFacts, projectionArityOfNamedFacts,
    Array.foldl_toList, foldl_map_maxWeight] using preserved

theorem resolveNamedFactsIndexed_preserves_weights
    (worldCount : Nat) (worlds things : NameIndex)
    (named : Array NamedScopedFact) (resolved : Array ScopedCompiledFact)
    (h : (mapArrayExceptCosted named
      (resolveNamedFactIndexedCosted worlds things)).value = .ok resolved) :
    (resolved.toList.map (ScopedCompiledFact.expansionWeight worldCount)).sum =
        (named.toList.map (NamedScopedFact.expansionWeight worldCount)).sum ∧
      (resolved.toList.map (ScopedCompiledFact.taxonomyWeight worldCount)).sum =
        (named.toList.map (NamedScopedFact.taxonomyWeight worldCount)).sum := by
  constructor
  · apply mapArrayExceptCosted_preserves_weight named
      (resolveNamedFactIndexedCosted worlds things)
      (NamedScopedFact.expansionWeight worldCount)
      (ScopedCompiledFact.expansionWeight worldCount) _ resolved h
    intro source result hResult
    exact (resolveNamedFactIndexed_preserves_weights
      worldCount worlds things source result hResult).1
  · apply mapArrayExceptCosted_preserves_weight named
      (resolveNamedFactIndexedCosted worlds things)
      (NamedScopedFact.taxonomyWeight worldCount)
      (ScopedCompiledFact.taxonomyWeight worldCount) _ resolved h
    intro source result hResult
    exact (resolveNamedFactIndexed_preserves_weights
      worldCount worlds things source result hResult).2

def CompiledFact.taxonomyEmissionCount : CompiledFact → Nat
  | .unary field x w => (expandUnaryTaxonomyFact field x w).size
  | _ => 1

private theorem sum_map_range_const (n c : Nat) :
    ((List.range n).map fun _ => c).sum = n * c := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, ih, Nat.succ_mul]

/--
The taxonomy component of the source metric is the exact number of facts that
the executable scope-expansion/taxonomy pipeline emits.  This compositional
accounting follows cost-aware semantics: the metric is recovered from the
executed intermediate values, rather than postulated as an unrelated envelope.
See Niu et al., POPL 2022, and Haslbeck, *Hoare Logics for Time Bounds*.
-/
theorem expandScopedFactCore_taxonomyEmissionCount
    (worldCount : Nat) (fact : ScopedCompiledFact) :
    ((expandScopedFactCore worldCount fact).toList.map
      CompiledFact.taxonomyEmissionCount).sum =
      fact.taxonomyWeight worldCount := by
  cases fact with
  | unary field x scope =>
      cases scope <;>
        simp [expandScopedFactCore, expandAtWorld,
          CompiledFact.taxonomyEmissionCount,
          ScopedCompiledFact.taxonomyWeight,
          ScopedCompiledFact.expansionWeight, ScopedCompiledFact.scope,
          ScopedCompiledFact.unaryField?, FactScope.worldMultiplicity,
          Function.comp_def, sum_map_range_const]
  | binary field x y scope =>
      cases scope <;>
        simp [expandScopedFactCore, expandAtWorld,
          CompiledFact.taxonomyEmissionCount,
          ScopedCompiledFact.taxonomyWeight,
          ScopedCompiledFact.expansionWeight, ScopedCompiledFact.scope,
          ScopedCompiledFact.unaryField?, FactScope.worldMultiplicity,
          Function.comp_def, sum_map_range_const]
  | ternary field x y z scope =>
      cases scope <;>
        simp [expandScopedFactCore, expandAtWorld,
          CompiledFact.taxonomyEmissionCount,
          ScopedCompiledFact.taxonomyWeight,
          ScopedCompiledFact.expansionWeight, ScopedCompiledFact.scope,
          ScopedCompiledFact.unaryField?, FactScope.worldMultiplicity,
          Function.comp_def, sum_map_range_const]
  | tupleProjection tuple index result scope =>
      cases scope <;>
        simp [expandScopedFactCore, expandAtWorld,
          CompiledFact.taxonomyEmissionCount,
          ScopedCompiledFact.taxonomyWeight,
          ScopedCompiledFact.expansionWeight, ScopedCompiledFact.scope,
          ScopedCompiledFact.unaryField?, FactScope.worldMultiplicity,
          Function.comp_def, sum_map_range_const]
  | derived prop scope =>
      cases scope <;>
        simp [expandScopedFactCore, expandAtWorld,
          CompiledFact.taxonomyEmissionCount,
          ScopedCompiledFact.taxonomyWeight,
          ScopedCompiledFact.expansionWeight, ScopedCompiledFact.scope,
          ScopedCompiledFact.unaryField?, FactScope.worldMultiplicity,
          Function.comp_def, sum_map_range_const]


/--
Batch scope expansion preserves the exact taxonomy-emission weight.  Together
with `addTaxonomyFactsCore_size`, this connects source syntax directly to the
number of concrete table facts constructed by the production compiler.
-/
theorem expandScopedFactsCosted_taxonomyEmissionCount
    (worldCount : Nat) (facts : Array ScopedCompiledFact) :
    (((expandScopedFactsCosted worldCount facts).value.toList.map
      CompiledFact.taxonomyEmissionCount).sum) =
      (facts.toList.map (ScopedCompiledFact.taxonomyWeight worldCount)).sum := by
  have listValue : ∀ (xs : List ScopedCompiledFact)
      (out : Array CompiledFact),
      ((xs.foldl (fun out fact => out ++ expandScopedFactCore worldCount fact) out).toList.map
        CompiledFact.taxonomyEmissionCount).sum =
        (out.toList.map CompiledFact.taxonomyEmissionCount).sum +
          (xs.map (ScopedCompiledFact.taxonomyWeight worldCount)).sum := by
    intro xs
    induction xs with
    | nil => simp
    | cons fact facts ih =>
        intro out
        simp only [List.foldl_cons]
        rw [ih]
        simp only [Array.toList_append, List.map_append, List.sum_append]
        rw [expandScopedFactCore_taxonomyEmissionCount]
        simp
        omega
  rw [expandScopedFactsCosted_value_eq_foldl, ← Array.foldl_toList]
  simpa using listValue facts.toList #[]

/-- Pure fold specification for emission order and output metrics. Production
uses the counted fold below, appending directly to one output array. -/
private def addTaxonomyFactsCore (facts : Array CompiledFact) : Array CompiledFact :=
  facts.foldl (fun out fact => match fact with
    | .unary field x w => pushAll out (expandUnaryTaxonomyFact field x w)
    | _ => out.push fact) #[]

theorem addTaxonomyFactsCore_size (facts : Array CompiledFact) :
    (addTaxonomyFactsCore facts).size =
      (facts.toList.map CompiledFact.taxonomyEmissionCount).sum := by
  have listSize : ∀ (xs : List CompiledFact) (out : Array CompiledFact),
      (xs.foldl (fun out fact => match fact with
        | .unary field x w => pushAll out (expandUnaryTaxonomyFact field x w)
        | _ => out.push fact) out).size = out.size +
        (xs.map CompiledFact.taxonomyEmissionCount).sum := by
    intro xs
    induction xs with
    | nil => simp
    | cons fact facts ih =>
        intro out
        rw [List.foldl_cons, ih]
        cases fact <;>
          simp [CompiledFact.taxonomyEmissionCount,
            pushAll_size] <;> omega
  simpa [addTaxonomyFactsCore, ← Array.foldl_toList] using listSize facts.toList #[]

/-- Charge the input tag test, then execute the ancestor traversal and each
output write. Non-unary facts need only their unchanged output write. -/
private def taxonomyStepCosted (out : Array CompiledFact) (fact : CompiledFact) :
    Complexity.Costed (Array CompiledFact) :=
  Complexity.Costed.charge 1 <| match fact with
    | .unary field x w => appendUnaryTaxonomyCosted field x w out
    | _ => Complexity.Costed.tick (out.push fact) 1

private theorem taxonomyStepCosted_value (out : Array CompiledFact) (fact : CompiledFact) :
    (taxonomyStepCosted out fact).value = (match fact with
      | .unary field x w => pushAll out (expandUnaryTaxonomyFact field x w)
      | _ => out.push fact) := by
  cases fact with
  | unary field x w =>
      simp only [taxonomyStepCosted, Complexity.Costed.charge_value,
        appendUnaryTaxonomyCosted_value, expandUnaryTaxonomyFact_eq_map]
      have eq := Array.foldl_push_eq_append
        (as := (expandUnaryTaxonomyFields field).map (fun ancestor => CompiledFact.unary ancestor x w))
        (bs := out) (f := id) rfl
      simpa [pushAll] using eq.symm
  | _ => rfl

def addTaxonomyFactsCosted (facts : Array CompiledFact) :
    Complexity.Costed (Array CompiledFact) :=
  Complexity.Costed.foldArray facts #[] taxonomyStepCosted

private theorem addTaxonomyFactsCosted_value_eq_core (facts : Array CompiledFact) :
    (addTaxonomyFactsCosted facts).value = addTaxonomyFactsCore facts := by
  simp [addTaxonomyFactsCosted, addTaxonomyFactsCore, taxonomyStepCosted_value]

theorem addTaxonomyFactsCosted_value_size (facts : Array CompiledFact) :
    (addTaxonomyFactsCosted facts).value.size =
      (facts.toList.map CompiledFact.taxonomyEmissionCount).sum := by
  simpa [addTaxonomyFactsCosted_value_eq_core] using addTaxonomyFactsCore_size facts

theorem addTaxonomyFactsCosted_projectionArity_le
    (facts : Array CompiledFact) :
    projectionArityOfFacts (addTaxonomyFactsCosted facts).value ≤
      projectionArityOfFacts facts := by
  have listBound : ∀ (xs : List CompiledFact) (out : Array CompiledFact)
      (bound : Nat),
      projectionArityOfFacts out ≤ bound →
      (∀ fact ∈ xs, fact.projectionArity ≤ bound) →
      projectionArityOfFacts (xs.foldl (fun out fact => match fact with
        | .unary field x w => pushAll out (expandUnaryTaxonomyFact field x w)
        | _ => out.push fact) out) ≤ bound := by
    intro xs
    induction xs with
    | nil => simp
    | cons fact facts ih =>
        intro out bound hOut hFacts
        simp only [List.foldl_cons]
        apply ih
        · cases fact with
          | unary field x w =>
              apply foldPush_projectionArity_le _ _ bound hOut
              intro emitted hEmitted
              simp only [expandUnaryTaxonomyFact_eq_map, Array.mem_map] at hEmitted
              rcases hEmitted with ⟨_, ⟨_, rfl⟩⟩
              simp
          | binary field x y w =>
              rw [projectionArityOfFacts_push]
              exact max_le hOut (hFacts _ (by simp))
          | ternary field x y z w =>
              rw [projectionArityOfFacts_push]
              exact max_le hOut (hFacts _ (by simp))
          | tupleProjection tuple index result w =>
              rw [projectionArityOfFacts_push]
              exact max_le hOut (hFacts _ (by simp))
          | derived prop =>
              rw [projectionArityOfFacts_push]
              exact max_le hOut (hFacts _ (by simp))
        · intro tailFact hTail
          exact hFacts tailFact (by simp [hTail])
  rw [addTaxonomyFactsCosted_value_eq_core]
  unfold addTaxonomyFactsCore
  rw [← Array.foldl_toList]
  apply listBound facts.toList #[] (projectionArityOfFacts facts)
  · simp [projectionArityOfFacts]
  · intro fact hFact
    exact fact.projectionArity_le_of_mem facts (by simpa using hFact)

def addTaxonomyFacts (facts : Array CompiledFact) : Array CompiledFact :=
  (addTaxonomyFactsCosted facts).value

@[simp] theorem addTaxonomyFactsCosted_value (facts : Array CompiledFact) :
    (addTaxonomyFactsCosted facts).value = addTaxonomyFacts facts := rfl

/-- Each input costs at most 229 operations: two for traversal/read, one tag
test, at most 202 for the fixed taxonomy search, and three per emitted ancestor
(at most eight). The counter records actual work, including earlier exits in
visited-field scans; 229 is an upper bound, not an assigned per-fact charge. -/
theorem addTaxonomyFactsCosted_cost_le (facts : Array CompiledFact) :
    (addTaxonomyFactsCosted facts).cost ≤ 229 * facts.size := by
  have stepBound (out : Array CompiledFact) (fact : CompiledFact) :
      (taxonomyStepCosted out fact).cost ≤ 227 := by
    cases fact with
    | unary field x w =>
        have hCost := Complexity.Taxonomy.ancestorsCosted_cost_le field
        have hSize := Complexity.Taxonomy.ancestors_size_le field
        simp only [taxonomyStepCosted, Complexity.Costed.charge_cost,
          appendUnaryTaxonomyCosted_cost, expandUnaryTaxonomyFields]
        omega
    | _ => simp [taxonomyStepCosted, Complexity.Costed.tick]
  simpa [addTaxonomyFactsCosted, Nat.mul_comm] using
    Complexity.Costed.foldArray_cost_le facts #[] taxonomyStepCosted 227
      (fun out fact _ => stepBound out fact)

def exceptOkCosted (result : Complexity.Costed α) :
    Complexity.Costed (Except ε α) :=
  result.map Except.ok

def buildWorldNameIndexCosted (source : ModelSource) :
    Complexity.Costed (Except ResolveError NameIndex) :=
  Complexity.Costed.charge 1 <|
  (buildNameIndexCosted source.worlds).map fun
    | .ok index => .ok index
    | .error name => .error (.duplicateWorld name)

def buildThingNameIndexCosted (source : ModelSource) :
    Complexity.Costed (Except ResolveError NameIndex) :=
  Complexity.Costed.charge 1 <|
  (buildNameIndexCosted source.things).map fun
    | .ok index => .ok index
    | .error name => .error (.duplicateThing name)

def resolveSourceFactsCosted (source : ModelSource)
    (worldIndex thingIndex : NameIndex) :
    Complexity.Costed (Except ResolveError (Array ScopedCompiledFact)) :=
  mapArrayExceptCosted source.facts
    (resolveNamedFactIndexedCosted worldIndex thingIndex)

def resolveSourceProductFamiliesCosted (source : ModelSource)
    (thingIndex : NameIndex) :
    Complexity.Costed (Except ResolveError (Array ProductFamilySpec)) :=
  mapArrayExceptCosted source.productFamilies
    (resolveNamedProductFamilyIndexedCosted thingIndex)

def materializeResolvedFactsCosted (source : ModelSource)
    (scopedFacts : Array ScopedCompiledFact) :
    Complexity.Costed (Array CompiledFact) :=
  let expanded := expandScopedFactsCosted source.worlds.size scopedFacts
  let taxonomy := addTaxonomyFactsCosted expanded.value
  let specialized := addReflexiveSpecializationFactsCosted
    source.worlds.size taxonomy.value
  ⟨specialized.value, expanded.cost + taxonomy.cost + specialized.cost⟩

@[simp] theorem materializeResolvedFactsCosted_value
    (source : ModelSource) (scopedFacts : Array ScopedCompiledFact) :
    (materializeResolvedFactsCosted source scopedFacts).value =
      (addReflexiveSpecializationFactsCosted source.worlds.size
        (addTaxonomyFactsCosted
          (expandScopedFactsCosted source.worlds.size scopedFacts).value).value).value := rfl

theorem materializeResolvedFactsCosted_cost
    (source : ModelSource) (scopedFacts : Array ScopedCompiledFact) :
    (materializeResolvedFactsCosted source scopedFacts).cost =
      (expandScopedFactsCosted source.worlds.size scopedFacts).cost +
      (addTaxonomyFactsCosted
        (expandScopedFactsCosted source.worlds.size scopedFacts).value).cost +
      (addReflexiveSpecializationFactsCosted source.worlds.size
        (addTaxonomyFactsCosted
          (expandScopedFactsCosted source.worlds.size scopedFacts).value).value).cost := rfl

/--
Named production tail after successful source-name resolution.  Keeping this
as an executable stage preserves short-circuiting while making its operational
cost theorem compositional, following the staged verified-compiler style used
as engineering inspiration by RadixExperiment.
-/
def compileResolvedSourceCosted (source : ModelSource)
    (scopedFacts : Array ScopedCompiledFact)
    (productFamilies : Array ProductFamilySpec) :
    Complexity.Costed (Except ResolveError CompiledModelSource) :=
  exceptBindCosted
    (exceptOkCosted (materializeResolvedFactsCosted source scopedFacts))
      fun expandedFacts =>
  exceptBindCosted
    (validateTupleProjectionsCosted source.worlds.size source.things.size expandedFacts)
      fun _ =>
  let ast : ModelAST :=
    { worldCount := source.worlds.size
      thingCount := source.things.size
      facts := expandedFacts
      productFamilies := productFamilies }
  (compileExplicitModelASTCosted ast).map fun tables => .ok
    { scopedFacts := scopedFacts
      productFamilies := productFamilies
      expandedFacts := expandedFacts
      ast := ast
      tables := tables }

/--
Counted source-to-table compiler. Every production stage is invoked here and
its cost is accumulated only when control reaches that stage; errors preserve
the exact short-circuit order of the executable compiler.
-/
def compileModelSourceCosted (source : ModelSource) :
    Complexity.Costed (Except ResolveError CompiledModelSource) :=
  exceptBindCosted (buildWorldNameIndexCosted source) fun worldIndex =>
  exceptBindCosted (buildThingNameIndexCosted source) fun thingIndex =>
  exceptBindCosted
    (resolveSourceFactsCosted source worldIndex thingIndex) fun scopedFacts =>
  exceptBindCosted
    (resolveSourceProductFamiliesCosted source thingIndex) fun productFamilies =>
  compileResolvedSourceCosted source scopedFacts productFamilies

/-- Production source compilation is exactly cost erasure. -/
def compileModelSource (source : ModelSource) :
    Except ResolveError CompiledModelSource :=
  (compileModelSourceCosted source).value

@[simp] theorem compileModelSourceCosted_value (source : ModelSource) :
    (compileModelSourceCosted source).value = compileModelSource source := rfl

/-- Clause theorem for unary fact compilation. -/
theorem compileFact_unary_eq
    (tables : FactTables) (field : UnaryField) (x w : Nat) :
    compileFact tables (.unary field x w) =
      addUnaryWithTaxonomy tables field.toTableField x w :=
  rfl

/-- Clause theorem for binary fact compilation. -/
theorem compileFact_binary_eq
    (tables : FactTables) (field : BinaryField) (x y w : Nat) :
    compileFact tables (.binary field x y w) = addBinary tables field.toTableField x y w :=
  rfl

/-- Clause theorem for ternary fact compilation. -/
theorem compileFact_ternary_eq
    (tables : FactTables) (field : TernaryField) (x y z w : Nat) :
    compileFact tables (.ternary field x y z w) = addTernary tables field.toTableField x y z w :=
  rfl

/-- Clause theorem for tuple-projection fact compilation. -/
theorem compileFact_tupleProjection_eq
    (tables : FactTables) (tuple index result w : Nat) :
    compileFact tables (.tupleProjection tuple index result w) =
      addTupleProjection tables tuple index result w :=
  rfl

/-- Clause theorem for asserted derived-relation facts. -/
theorem compileFact_derived_eq
    (tables : FactTables) (prop : String) :
    compileFact tables (.derived prop) = addDerivedProp tables prop :=
  rfl

/-- The resolved compiler folds facts, closes specialization, then materializes dense tables. -/
theorem compileModelAST_eq (ast : ModelAST) :
    compileModelAST ast =
      let sparse := closeReflexiveSpecialization ast.worldCount (compileFacts ast.facts)
      let tables := ast.productFamilies.foldl addProductFamily sparse
      tables.withDenseFacts ast.worldCount ast.thingCount tables.sparseFacts :=
  rfl

end LeanUfo.UFO.DSL
