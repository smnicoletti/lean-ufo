import Lean
import LeanUfo.UFO.DSL.FiniteModel
import LeanUfo.UFO.DSL.Compiler.AST
import LeanUfo.UFO.DSL.Complexity.CostModel
import LeanUfo.UFO.DSL.Complexity.Closure

/-!
# Pure compiler core for the finite UFO DSL

This module separates the semantic DSL compiler from Lean command elaboration.
The parser in `Syntax.lean` is metaprogramming, but it only constructs named
facts and emits the final Lean declarations. The pipeline implemented by this
module and its `Compiler/` support modules is ordinary Lean code:

```text
NamedScopedFact
  → resolveNamedFacts
  → ScopedCompiledFact
  → expandScopedFacts
  → CompiledFact
  → addTaxonomyFacts
  → addReflexiveSpecializationFacts
  → ModelAST
  → compileExplicitModelAST
  → FactTables
  → compileExplicitModel
  → FiniteModel4
```

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
abstract cost. Production functions erase only that cost field. This is why the
complexity results describe the compiler that actually executes, rather than a
separate mathematical envelope. Full references and the limits of the unit-cost
model are documented in `docs/dsl/complexity.md`.
-/

namespace LeanUfo.UFO.DSL

/--
Locate a name and count the string-equality probes actually performed.

String equality is one abstract operation at this layer. The unit-cost theorem
does not count characters. A machine model that treats source-name length as
an input must add that cost.
-/
private def nameIndexListCosted? (x : String) : List String → Nat →
    Complexity.Costed (Option Nat)
  | .nil, _ => ⟨none, 0⟩
  | .cons candidate rest, index =>
      if candidate == x then ⟨some index, 1⟩
      else
        let result := nameIndexListCosted? x rest (index + 1)
        ⟨result.value, result.cost + 1⟩

def nameIndexCosted? (xs : Array String) (x : String) : Complexity.Costed (Option Nat) :=
  nameIndexListCosted? x xs.toList 0

/-- Production name lookup is the erasure of the counted executable scan. -/
def nameIndex? (xs : Array String) (x : String) : Option Nat :=
  (nameIndexCosted? xs x).value

@[simp] theorem nameIndexCosted_value (xs : Array String) (x : String) :
    (nameIndexCosted? xs x).value = nameIndex? xs x := rfl

theorem nameIndexCosted_cost_le_size (xs : Array String) (x : String) :
    (nameIndexCosted? xs x).cost ≤ xs.size := by
  unfold nameIndexCosted?
  have aux : ∀ (ys : List String) (i : Nat),
      (nameIndexListCosted? x ys i).cost ≤ ys.length := by
    intro ys
    induction ys with
    | nil => intro i; simp [nameIndexListCosted?]
    | cons candidate rest ih =>
        intro i
        simp only [nameIndexListCosted?]
        split
        · simp
        · dsimp
          simpa using Nat.add_le_add_right (ih (i + 1)) 1
  simpa using aux xs.toList 0

example : nameIndexCosted? #["a", "b", "c"] "b" = ⟨some 1, 2⟩ := by
  native_decide

example : nameIndexCosted? #["a", "b", "c"] "z" = ⟨none, 3⟩ := by
  native_decide

/--
Reusable source-name index. Each `HashMap` lookup/insert is one abstract map
operation; this interface does not claim a verified character-level or native
hash-table bound. The combined theorem exposes `mapOps` separately. This is the
implementation-correspondence discipline emphasized by Forster et al. (ITP
2021): the machine primitive must be named instead of hidden in an envelope.
-/
structure NameIndex where
  entries : Std.HashMap String Nat := {}
deriving Inhabited

private def buildNameIndexListCosted :
    List String → Nat → Std.HashMap String Nat →
      Complexity.Costed (Except String NameIndex)
  | [], _, entries => .pure (.ok ⟨entries⟩)
  | List.cons x xs, index, entries =>
      if entries.contains x then
        .tick (.error x) 1
      else
        Complexity.Costed.charge 2
          (buildNameIndexListCosted xs (index + 1) (entries.insert x index))

/--
Build the reusable name index by structurally consuming the source array.
This is the same executable recursion used for the cost proof;
there is no unrelated post-hoc recurrence or envelope.
-/
def buildNameIndexCosted (names : Array String) :
    Complexity.Costed (Except String NameIndex) :=
  buildNameIndexListCosted names.toList 0 {}

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
Name-index construction performs at most one membership test and one insertion
per declared name.  A duplicate stops before its insertion, so early failure
only lowers the abstract `mapOps` charge.
-/
theorem buildNameIndexCosted_cost_le (names : Array String) :
    (buildNameIndexCosted names).cost ≤ 2 * names.size := by
  have listBound : ∀ (xs : List String) (index : Nat)
      (entries : Std.HashMap String Nat),
      (buildNameIndexListCosted xs index entries).cost ≤ 2 * xs.length := by
    intro xs
    induction xs with
    | nil => simp [buildNameIndexListCosted]
    | cons name names ih =>
        intro index entries
        by_cases h : entries.contains name
        · simp [buildNameIndexListCosted, h]
          omega
        · simp [buildNameIndexListCosted, h, Complexity.Costed.charge]
          have htail := ih (index + 1) (entries.insert name index)
          omega
  simpa [buildNameIndexCosted] using listBound names.toList 0 {}

example : (buildNameIndexCosted #["w0", "w1", "w2"]).cost = 6 := by
  native_decide

example : (buildNameIndexCosted #["x", "y", "x", "unreached"]).cost = 5 := by
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

def exceptBindCosted
    (result : Complexity.Costed (Except ε α))
    (next : α → Complexity.Costed (Except ε β)) :
    Complexity.Costed (Except ε β) :=
  match result.value with
  | .error error => ⟨.error error, result.cost⟩
  | .ok value =>
      let following := next value
      ⟨following.value, result.cost + following.cost⟩

theorem exceptBindCosted_cost_le_add
    (result : Complexity.Costed (Except ε α))
    (next : α → Complexity.Costed (Except ε β)) (left right : Nat)
    (hLeft : result.cost ≤ left) (hRight : ∀ value, (next value).cost ≤ right) :
    (exceptBindCosted result next).cost ≤ left + right := by
  cases hValue : result.value with
  | error error =>
      simp [exceptBindCosted, hValue]
      omega
  | ok value =>
      simp [exceptBindCosted, hValue]
      exact Nat.add_le_add hLeft (hRight value)

private def mapListExceptCosted
    (f : α → Complexity.Costed (Except ε β)) : List α →
    Complexity.Costed (Except ε (List β))
  | [] => Complexity.Costed.pure (.ok [])
  | List.cons x xs =>
      exceptBindCosted (Complexity.Costed.charge 1 (f x)) fun y =>
      exceptBindCosted (mapListExceptCosted f xs) fun ys =>
        Complexity.Costed.pure (.ok (y :: ys))

def mapArrayExceptCosted
    (xs : Array α) (f : α → Complexity.Costed (Except ε β)) :
    Complexity.Costed (Except ε (Array β)) :=
  (mapListExceptCosted f xs.toList).map (Except.map List.toArray)

def mapArrayExcept
    (xs : Array α) (f : α → Complexity.Costed (Except ε β)) :
    Except ε (Array β) :=
  (mapArrayExceptCosted xs f).value

@[simp] theorem mapArrayExceptCosted_value
    (xs : Array α) (f : α → Complexity.Costed (Except ε β)) :
    (mapArrayExceptCosted xs f).value = mapArrayExcept xs f := rfl

theorem mapArrayExceptCosted_cost_le
    (xs : Array α) (f : α → Complexity.Costed (Except ε β)) (perItem : Nat)
    (hCost : ∀ x ∈ xs, (f x).cost ≤ perItem) :
    (mapArrayExceptCosted xs f).cost ≤ xs.size * (perItem + 1) := by
  unfold mapArrayExceptCosted
  have aux : ∀ (ys : List α), (∀ x ∈ ys, (f x).cost ≤ perItem) →
      (mapListExceptCosted f ys).cost ≤ ys.length * (perItem + 1) := by
    intro ys h
    induction ys with
    | nil => simp [mapListExceptCosted]
    | cons x xs ih =>
        have hx := h x (by simp)
        have hxs : ∀ y ∈ xs, (f y).cost ≤ perItem := by
          intro y hy
          exact h y (by simp [hy])
        specialize ih hxs
        cases hfx : (f x).value with
        | error error =>
            simp [mapListExceptCosted, exceptBindCosted,
              Complexity.Costed.charge, hfx, Nat.succ_mul]
            omega
        | ok value =>
            cases hrest : (mapListExceptCosted f xs).value with
            | error error =>
                simp [mapListExceptCosted, exceptBindCosted,
                  Complexity.Costed.charge, hfx, hrest, Nat.succ_mul]
                omega
            | ok values =>
                simp [mapListExceptCosted, exceptBindCosted,
                  Complexity.Costed.charge, hfx, hrest, Nat.succ_mul]
                omega
  simpa only [Complexity.Costed.map_cost, Array.length_toList] using
    aux xs.toList (by simpa using hCost)

private theorem mapListExceptCosted_preserves_weight
    (f : α → Complexity.Costed (Except ε β))
    (sourceWeight : α → Nat) (resultWeight : β → Nat)
    (hItem : ∀ x y, (f x).value = .ok y → resultWeight y = sourceWeight x) :
    ∀ (xs : List α) (ys : List β),
      (mapListExceptCosted f xs).value = .ok ys →
      (ys.map resultWeight).sum = (xs.map sourceWeight).sum := by
  intro xs
  induction xs with
  | nil =>
      intro ys h
      simp [mapListExceptCosted] at h
      subst ys
      simp
  | cons x xs ih =>
      intro ys h
      cases hHead : (f x).value with
      | error error =>
          simp [mapListExceptCosted, exceptBindCosted,
            Complexity.Costed.charge, hHead] at h
      | ok y =>
          cases hTail : (mapListExceptCosted f xs).value with
          | error error =>
              simp [mapListExceptCosted, exceptBindCosted,
                Complexity.Costed.charge, hHead, hTail] at h
          | ok tail =>
              simp [mapListExceptCosted, exceptBindCosted,
                Complexity.Costed.charge, hHead, hTail] at h
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
  unfold mapArrayExceptCosted at h
  cases hMapped : (mapListExceptCosted f xs.toList).value with
  | error error => simp [hMapped, Except.map] at h
  | ok values =>
      simp [hMapped, Except.map] at h
      subst ys
      simpa using mapListExceptCosted_preserves_weight
        f sourceWeight resultWeight hItem xs.toList values hMapped

private theorem mapListExceptCosted_preserves_maxWeight
    (f : α → Complexity.Costed (Except ε β))
    (sourceWeight : α → Nat) (resultWeight : β → Nat)
    (hItem : ∀ x y, (f x).value = .ok y → resultWeight y = sourceWeight x) :
    ∀ (xs : List α) (ys : List β) (initial : Nat),
      (mapListExceptCosted f xs).value = .ok ys →
      (ys.map resultWeight).foldl max initial =
        (xs.map sourceWeight).foldl max initial := by
  intro xs
  induction xs with
  | nil =>
      intro ys initial h
      simp [mapListExceptCosted] at h
      subst ys
      simp
  | cons x xs ih =>
      intro ys initial h
      cases hHead : (f x).value with
      | error error =>
          simp [mapListExceptCosted, exceptBindCosted,
            Complexity.Costed.charge, hHead] at h
      | ok y =>
          cases hTail : (mapListExceptCosted f xs).value with
          | error error =>
              simp [mapListExceptCosted, exceptBindCosted,
                Complexity.Costed.charge, hHead, hTail] at h
          | ok tail =>
              simp [mapListExceptCosted, exceptBindCosted,
                Complexity.Costed.charge, hHead, hTail] at h
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
  unfold mapArrayExceptCosted at h
  cases hMapped : (mapListExceptCosted f xs.toList).value with
  | error error => simp [hMapped, Except.map] at h
  | ok values =>
      simp [hMapped, Except.map] at h
      subst ys
      simpa using mapListExceptCosted_preserves_maxWeight
        f sourceWeight resultWeight hItem xs.toList values 0 hMapped

/-- A successful short-circuiting map produces exactly one result per input. -/
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

private def foldListCosted (step : β → α → β) (charge : Nat) :
    List α → β → Complexity.Costed β
  | [], initial => Complexity.Costed.pure initial
  | List.cons x xs, initial =>
      Complexity.Costed.charge charge
        (foldListCosted step charge xs (step initial x))

def foldArrayCosted
    (xs : Array α) (initial : β) (step : β → α → β) (charge : Nat) :
    Complexity.Costed β :=
  foldListCosted step charge xs.toList initial

@[simp] theorem foldArrayCosted_cost
    (xs : Array α) (initial : β) (step : β → α → β) (charge : Nat) :
    (foldArrayCosted xs initial step charge).cost = xs.size * charge := by
  unfold foldArrayCosted
  have aux : ∀ (ys : List α) (state : β),
      (foldListCosted step charge ys state).cost = ys.length * charge := by
    intro ys
    induction ys with
    | nil => intro state; simp [foldListCosted]
    | cons x xs ih =>
        intro state
        simp [foldListCosted, ih, Nat.succ_mul, Nat.add_comm]
  simpa using aux xs.toList initial

theorem foldArrayCosted_value
    (xs : Array α) (initial : β) (step : β → α → β) (charge : Nat) :
    (foldArrayCosted xs initial step charge).value = xs.foldl step initial := by
  unfold foldArrayCosted
  have aux : ∀ (ys : List α) (state : β),
      (foldListCosted step charge ys state).value = ys.foldl step state := by
    intro ys
    induction ys with
    | nil => intro state; simp [foldListCosted]
    | cons x xs ih =>
        intro state
        simpa [foldListCosted] using ih (step state x)
  simpa using aux xs.toList initial

def resolveThingIndexedCosted (things : NameIndex) (thing : String) :
    Complexity.Costed (Except ResolveError Nat) :=
  (things.findCosted thing).map fun
    | some idx => .ok idx
    | none => .error (.unknownThing thing)

def resolveWorldIndexedCosted (worlds : NameIndex) (world : String) :
    Complexity.Costed (Except ResolveError Nat) :=
  (worlds.findCosted world).map fun
    | some idx => .ok idx
    | none => .error (.unknownWorld world)

def resolveScopeIndexedCosted (worlds : NameIndex) :
    NamedFactScope → Complexity.Costed (Except ResolveError FactScope)
  | .everywhere => Complexity.Costed.pure (.ok .everywhere)
  | .at world =>
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

private def finThingSource (idx : Nat) : String :=
  s!"(⟨{idx}, by decide⟩ : Fin data.thingCount)"

private def finWorldSource (idx : Nat) : String :=
  s!"(⟨{idx}, by decide⟩ : Fin data.worldCount)"

private def definedUnaryPredicate? (field : String) : Option (String × String) :=
  match field with
  | "Quality" => some ("Quality", "sig.toUFOSignature3_3")
  | "NonEmptySet" => some ("NonEmptySet", "sig.toUFOSignature3_12")
  | "QualityStructure" => some ("QualityStructure", "sig.toUFOSignature3_12")
  | "SimpleQuality" => some ("SimpleQuality", "sig.toUFOSignature3_12")
  | "ComplexQuality" => some ("ComplexQuality", "sig.toUFOSignature3_12")
  | "SimpleQualityType" => some ("SimpleQualityType", "sig.toUFOSignature3_12")
  | "ComplexQualityType" => some ("ComplexQualityType", "sig.toUFOSignature3_12")
  | _ => none

private def definedBinaryPredicate? (field : String) : Option (String × String) :=
  match field with
  | "ProperSub" => some ("ProperSub", "sig.toUFOSignature3_1")
  | "UltimateBearerOf" => some ("UltimateBearerOf", "sig.toUFOSignature3_9")
  | "SubsetOf" => some ("SubsetOf", "sig.toUFOSignature3_12")
  | "ProperSubsetOf" => some ("ProperSubsetOf", "sig.toUFOSignature3_12")
  | _ => none

private def resolveDerivedFact
    (things : Array String) (fact : NamedDerivedFact) :
    Except ResolveError (Nat → String) := do
  match fact with
  | .unary field thing =>
      let idx ← resolveThing things thing
      match definedUnaryPredicate? field with
      | some (definition, sigSource) =>
          pure fun w => s!"{definition} {sigSource} {finThingSource idx} {finWorldSource w}"
      | none =>
          pure fun w => s!"sig.{field} {finThingSource idx} {finWorldSource w}"
  | .binary field left right =>
      let leftIdx ← resolveThing things left
      let rightIdx ← resolveThing things right
      match definedBinaryPredicate? field with
      | some (definition, sigSource) =>
          pure fun w =>
            s!"{definition} {sigSource} {finThingSource leftIdx} {finThingSource rightIdx} {finWorldSource w}"
      | none =>
          pure fun w =>
            s!"sig.{field} {finThingSource leftIdx} {finThingSource rightIdx} {finWorldSource w}"
  | .ternary field first second third =>
      let firstIdx ← resolveThing things first
      let secondIdx ← resolveThing things second
      let thirdIdx ← resolveThing things third
      pure fun w =>
        s!"sig.{field} {finThingSource firstIdx} {finThingSource secondIdx} {finThingSource thirdIdx} {finWorldSource w}"
  | .quaternary field first second third fourth =>
      let firstIdx ← resolveThing things first
      let secondIdx ← resolveThing things second
      let thirdIdx ← resolveThing things third
      let fourthIdx ← resolveThing things fourth
      pure fun w =>
        s!"sig.{field} {finThingSource firstIdx} {finThingSource secondIdx} {finThingSource thirdIdx} {finThingSource fourthIdx} {finWorldSource w}"

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
      let propAtWorld ← resolveDerivedFact things fact
      let scope ← resolveScope worlds scope
      pure (.derived propAtWorld scope)

private def resolveDerivedFactIndexed
    (things : NameIndex) (fact : NamedDerivedFact) :
    Except ResolveError (Nat → String) := do
      match fact with
        | .unary field thing =>
            let idx ← resolveThingIndexed things thing
            pure fun w =>
              match definedUnaryPredicate? field with
              | some (definition, sigSource) =>
                  s!"{definition} {sigSource} {finThingSource idx} {finWorldSource w}"
              | none => s!"sig.{field} {finThingSource idx} {finWorldSource w}"
        | .binary field left right =>
            let leftIdx ← resolveThingIndexed things left
            let rightIdx ← resolveThingIndexed things right
            pure fun w =>
              match definedBinaryPredicate? field with
              | some (definition, sigSource) =>
                  s!"{definition} {sigSource} {finThingSource leftIdx} {finThingSource rightIdx} {finWorldSource w}"
              | none =>
                  s!"sig.{field} {finThingSource leftIdx} {finThingSource rightIdx} {finWorldSource w}"
        | .ternary field first second third =>
            let firstIdx ← resolveThingIndexed things first
            let secondIdx ← resolveThingIndexed things second
            let thirdIdx ← resolveThingIndexed things third
            pure fun w =>
              s!"sig.{field} {finThingSource firstIdx} {finThingSource secondIdx} {finThingSource thirdIdx} {finWorldSource w}"
        | .quaternary field first second third fourth =>
            let firstIdx ← resolveThingIndexed things first
            let secondIdx ← resolveThingIndexed things second
            let thirdIdx ← resolveThingIndexed things third
            let fourthIdx ← resolveThingIndexed things fourth
            pure fun w =>
              s!"sig.{field} {finThingSource firstIdx} {finThingSource secondIdx} {finThingSource thirdIdx} {finThingSource fourthIdx} {finWorldSource w}"

/-- Specification retained for clause comparison during the counted migration. -/
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
      -- Derived facts still build generated proposition strings, but all names
      -- are resolved through the shared thing index.
      let propAtWorld ← resolveDerivedFactIndexed things fact
      pure (.derived propAtWorld (← resolveScopeIndexed worlds scope))

private def resolveDerivedFactIndexedCosted
    (things : NameIndex) : NamedDerivedFact →
    Complexity.Costed (Except ResolveError (Nat → String))
  | .unary field thing =>
      exceptBindCosted (resolveThingIndexedCosted things thing) fun idx =>
        Complexity.Costed.pure (.ok fun w =>
          match definedUnaryPredicate? field with
          | some (definition, sigSource) =>
              s!"{definition} {sigSource} {finThingSource idx} {finWorldSource w}"
          | none => s!"sig.{field} {finThingSource idx} {finWorldSource w}")
  | .binary field left right =>
      exceptBindCosted (resolveThingIndexedCosted things left) fun leftIdx =>
      exceptBindCosted (resolveThingIndexedCosted things right) fun rightIdx =>
        Complexity.Costed.pure (.ok fun w =>
          match definedBinaryPredicate? field with
          | some (definition, sigSource) =>
              s!"{definition} {sigSource} {finThingSource leftIdx} {finThingSource rightIdx} {finWorldSource w}"
          | none =>
              s!"sig.{field} {finThingSource leftIdx} {finThingSource rightIdx} {finWorldSource w}")
  | .ternary field first second third =>
      exceptBindCosted (resolveThingIndexedCosted things first) fun firstIdx =>
      exceptBindCosted (resolveThingIndexedCosted things second) fun secondIdx =>
      exceptBindCosted (resolveThingIndexedCosted things third) fun thirdIdx =>
        Complexity.Costed.pure (.ok fun w =>
          s!"sig.{field} {finThingSource firstIdx} {finThingSource secondIdx} {finThingSource thirdIdx} {finWorldSource w}")
  | .quaternary field first second third fourth =>
      exceptBindCosted (resolveThingIndexedCosted things first) fun firstIdx =>
      exceptBindCosted (resolveThingIndexedCosted things second) fun secondIdx =>
      exceptBindCosted (resolveThingIndexedCosted things third) fun thirdIdx =>
      exceptBindCosted (resolveThingIndexedCosted things fourth) fun fourthIdx =>
        Complexity.Costed.pure (.ok fun w =>
          s!"sig.{field} {finThingSource firstIdx} {finThingSource secondIdx} {finThingSource thirdIdx} {finThingSource fourthIdx} {finWorldSource w}")

/-- Counted production resolver; failed references stop later lookups. -/
def resolveNamedFactIndexedCosted
    (worlds things : NameIndex) : NamedScopedFact →
    Complexity.Costed (Except ResolveError ScopedCompiledFact)
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
      exceptBindCosted (resolveDerivedFactIndexedCosted things fact) fun propAtWorld =>
      exceptBindCosted (resolveScopeIndexedCosted worlds scope) fun resolvedScope =>
        Complexity.Costed.pure (.ok (.derived propAtWorld resolvedScope))

/-- Production resolution is the erasure of the counted, short-circuiting pass. -/
def resolveNamedFactIndexed
    (worlds things : NameIndex) (fact : NamedScopedFact) :
    Except ResolveError ScopedCompiledFact :=
  (resolveNamedFactIndexedCosted worlds things fact).value

theorem resolveNamedFactIndexedCosted_cost_le_five
    (worlds things : NameIndex) (fact : NamedScopedFact) :
    (resolveNamedFactIndexedCosted worlds things fact).cost ≤ 5 := by
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
      (resolveNamedFactIndexedCosted worlds things)).cost ≤ 6 * facts.size := by
  have h := mapArrayExceptCosted_cost_le facts
    (resolveNamedFactIndexedCosted worlds things) 5
    (by
      intro fact _
      exact resolveNamedFactIndexedCosted_cost_le_five worlds things fact)
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

def resolveNamedProductFamilyIndexedCosted
    (things : NameIndex) (family : NamedProductFamily) :
    Complexity.Costed (Except ResolveError ProductFamilySpec) :=
  if family.dimensionThings.size != family.typeThings.size then
    .tick (.error (.productFamilyArityMismatch
      family.domain family.qualityType family.dimensionThings.size
        family.typeThings.size)) 1
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
      2 * (family.dimensionThings.size + family.typeThings.size) + 3 := by
  unfold resolveNamedProductFamilyIndexedCosted
  split
  · simp
  · refine (exceptBindCosted_cost_le_add _ _ 1
        (2 * (family.dimensionThings.size + family.typeThings.size) + 2)
        (by rfl) ?_).trans (by omega)
    intro domain
    refine (exceptBindCosted_cost_le_add _ _ 1
        (2 * (family.dimensionThings.size + family.typeThings.size) + 1)
        (by rfl) ?_).trans (by omega)
    intro qualityType
    refine (exceptBindCosted_cost_le_add _ _
        (2 * family.dimensionThings.size)
        (2 * family.typeThings.size + 1) ?_ ?_).trans (by omega)
    · simpa [Nat.mul_comm] using
        (mapArrayExceptCosted_cost_le family.dimensionThings
          (resolveThingIndexedCosted things) 1 (by intro name _; rfl))
    · intro dimensionThings
      apply exceptBindCosted_cost_le_add _ _
          (2 * family.typeThings.size) 1
      · simpa [Nat.mul_comm] using
          (mapArrayExceptCosted_cost_le family.typeThings
            (resolveThingIndexedCosted things) 1 (by intro name _; rfl))
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
        (2 * (families.toList.map NamedProductFamily.slotCount).sum + 4) := by
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
compact view for generated certificate proofs. Native `FiniteModel4` execution
uses the typed dense arrays below and does not traverse closure chains.
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
Immediate unary taxonomy implications used to make the surface DSL lighter.

The map follows only the encoded classification hierarchy where a child
predicate has a unique positive parent path. It avoids inferences
that require choosing between disjoint alternatives.
-/
def unaryTaxonomyParents (field : String) : Array String :=
  match field with
  | "object" => #["substantial"]
  | "collective" => #["substantial"]
  | "quantity" => #["substantial"]
  | "relator" => #["moment"]
  | "intrinsicMoment" => #["moment"]
  | "mode" => #["intrinsicMoment"]
  | "substantial" => #["endurant"]
  | "moment" => #["endurant"]
  | "endurant" => #["concreteIndividual"]
  | "perdurant" => #["concreteIndividual"]
  | "quale" => #["abstractIndividual"]
  | "set_" => #["abstractIndividual"]
  | "externallyDependentMode" => #["mode"]
  | "quaIndividual" => #["externallyDependentMode"]

  | "subKind" => #["rigid", "sortal"]
  | "phase" => #["antiRigid", "sortal"]
  | "role" => #["antiRigid", "sortal"]
  | "semiRigidSortal" => #["semiRigid", "sortal"]
  | "category" => #["rigid", "nonSortal"]
  | "mixin" => #["semiRigid", "nonSortal"]
  | "phaseMixin" => #["antiRigid", "nonSortal"]
  | "roleMixin" => #["antiRigid", "nonSortal"]
  | "kind" => #["rigid", "sortal"]
  | "sortal" => #["endurantType"]
  | "nonSortal" => #["endurantType"]

  | "objectKind" => #["objectType", "kind"]
  | "collectiveKind" => #["collectiveType", "kind"]
  | "quantityKind" => #["quantityType", "kind"]
  | "relatorKind" => #["relatorType", "kind"]
  | "modeKind" => #["modeType", "kind"]
  | "qualityKind" => #["qualityType", "kind"]
  | "objectType" => #["substantialType"]
  | "collectiveType" => #["substantialType"]
  | "quantityType" => #["substantialType"]
  | "relatorType" => #["momentType"]
  | "modeType" => #["intrinsicMomentType", "momentType"]
  | "qualityType" => #["intrinsicMomentType", "momentType"]
  | "intrinsicMomentType" => #["momentType"]
  | "substantialType" => #["endurantType"]
  | "momentType" => #["endurantType"]
  | _ => #[]

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

/-- Allocate and charge every cell of the explicit production representation. -/
def FactTables.initializeDenseCosted
    (tables : FactTables) (worldCount thingCount maxProjectionArity : Nat) :
    Complexity.Costed FactTables :=
  let unaryCount := UnaryField.count * thingCount * worldCount
  let binaryCount := BinaryField.count * thingCount * thingCount * worldCount
  let ternaryCount := TernaryField.count * thingCount * thingCount * thingCount * worldCount
  let projectionCount := thingCount * maxProjectionArity * worldCount
  ⟨{ tables with
      denseWorldCount := worldCount
      denseThingCount := thingCount
      denseProjectionArity := maxProjectionArity
      unaryCells := Array.replicate unaryCount false
      binaryCells := Array.replicate binaryCount false
      ternaryCells := Array.replicate ternaryCount false
      projectionCells := Array.replicate projectionCount none },
    unaryCount + binaryCount + ternaryCount + projectionCount⟩

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
      tables.initializeDense worldCount thingCount maxProjectionArity := rfl

@[simp] theorem FactTables.initializeDenseCosted_cost
    (tables : FactTables) (worldCount thingCount maxProjectionArity : Nat) :
    (tables.initializeDenseCosted worldCount thingCount maxProjectionArity).cost =
      UnaryField.count * thingCount * worldCount +
      BinaryField.count * thingCount * thingCount * worldCount +
      TernaryField.count * thingCount * thingCount * thingCount * worldCount +
      thingCount * maxProjectionArity * worldCount := rfl

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

def FactTables.inherenceEdgeAt (tables : FactTables) (world : Nat)
    (left right : Fin tables.denseThingCount) : Bool :=
  let width := tables.denseThingCount * tables.denseThingCount * tables.denseWorldCount
  let coordinate := binaryCoordinate tables.denseThingCount tables.denseWorldCount
    left.val right.val world
  tables.binaryCells[BinaryField.inheresIn.index * width + coordinate]?.getD false

structure InherenceClosureData where
  reachable : Array Bool
  nextHop : Array (Option Nat)
deriving Repr, Inhabited

/-- Build one row-major closure and its first-hop evidence in one counted pass. -/
def FactTables.inherenceClosureAtCosted
    (tables : FactTables) (world : Nat) : Complexity.Costed InherenceClosureData :=
  let closure := Complexity.warshallStateCosted tables.denseThingCount
    (tables.inherenceEdgeAt world)
  ⟨{ reachable := closure.value.reachable.flatten.toArray
     nextHop := closure.value.nextHop.flatten.toArray.map (Option.map Fin.val) },
    closure.cost⟩

@[simp] theorem FactTables.inherenceClosureAtCosted_cost
    (tables : FactTables) (world : Nat) :
    (tables.inherenceClosureAtCosted world).cost =
      13 * tables.denseThingCount ^ 3 + 9 * tables.denseThingCount ^ 2 := rfl

/-- Every stored coordinate denotes the proved reachability recurrence. -/
theorem FactTables.inherenceClosureAtCosted_lookup
    (tables : FactTables) (world : Nat)
    (source target : Fin tables.denseThingCount) :
    (tables.inherenceClosureAtCosted world).value.reachable[
        Complexity.matrixIndex tables.denseThingCount source.val target.val]?.getD false =
      Complexity.reachableVia
        (tables.inherenceEdgeAt world)
        (List.finRange tables.denseThingCount) source target := by
  unfold FactTables.inherenceClosureAtCosted
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
      cost := cost + closure.cost + 1
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

private theorem foldl_snd_snd_const_add
    (xs : List α) (initial : β × γ × Nat)
    (step₁ : β → α → β) (step₂ : γ → α → γ) (charge : Nat) :
    (xs.foldl (fun state x =>
      (step₁ state.1 x, step₂ state.2.1 x, state.2.2 + charge)) initial).2.2 =
      initial.2.2 + xs.length * charge := by
  induction xs generalizing initial with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons, ih]
      simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.succ_mul]

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
    (fun cost _ => cost +
      (13 * tables.denseThingCount ^ 3 + 9 * tables.denseThingCount ^ 2) + 1)
  simpa [FactTables.buildInherenceClosuresCosted,
    FactTables.buildInherenceClosures, FactTables.inherenceClosureAtCosted,
    Complexity.warshallStateCosted, Complexity.warshallState, reach, hops] using h

@[simp] theorem FactTables.buildInherenceClosuresCosted_cost (tables : FactTables) :
    (tables.buildInherenceClosuresCosted).cost =
      tables.denseWorldCount *
        (13 * tables.denseThingCount ^ 3 + 9 * tables.denseThingCount ^ 2 + 1) := by
  let charge := 13 * tables.denseThingCount ^ 3 + 9 * tables.denseThingCount ^ 2 + 1
  let produce := fun world => (tables.inherenceClosureAtCosted world).value
  have h := foldl_snd_snd_const_add (List.range' 0 tables.denseWorldCount)
    (#[], #[], 0)
    (fun closures world => closures.push (produce world).reachable)
    (fun nextHops world => nextHops.push (produce world).nextHop) charge
  simpa [FactTables.buildInherenceClosuresCosted, produce, charge,
    Nat.mul_comm, Nat.add_assoc] using h

def projectionArityOfFacts (facts : Array CompiledFact) : Nat :=
  facts.foldl (fun arity fact => max arity fact.projectionArity) 0

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
Reject non-functional tuple projections with one deterministic dense pass.
Identical duplicate facts are idempotent.
-/
private def validateTupleProjectionsCore
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

def validateTupleProjectionsCosted
    (worldCount thingCount : Nat) (facts : Array CompiledFact) :
    Complexity.Costed (Except ResolveError Unit) :=
  let initializedCells := thingCount * projectionArityOfFacts facts * worldCount
  ⟨validateTupleProjectionsCore worldCount thingCount facts,
    initializedCells + facts.size⟩

def validateTupleProjections
    (worldCount thingCount : Nat) (facts : Array CompiledFact) :
    Except ResolveError Unit :=
  (validateTupleProjectionsCosted worldCount thingCount facts).value

@[simp] theorem validateTupleProjectionsCosted_value
    (worldCount thingCount : Nat) (facts : Array CompiledFact) :
    (validateTupleProjectionsCosted worldCount thingCount facts).value =
      validateTupleProjections worldCount thingCount facts := rfl

@[simp] theorem validateTupleProjectionsCosted_cost
    (worldCount thingCount : Nat) (facts : Array CompiledFact) :
    (validateTupleProjectionsCosted worldCount thingCount facts).cost =
      thingCount * projectionArityOfFacts facts * worldCount + facts.size := rfl

example : validateTupleProjections 1 2 #[
    .tupleProjection 0 0 1 0, .tupleProjection 0 0 1 0] = .ok () := by
  native_decide

example : validateTupleProjections 1 2 #[
    .tupleProjection 0 0 1 0, .tupleProjection 0 0 0 0] =
      .error (.conflictingTupleProjection 0 0 0 1 0) := by
  native_decide

/-- Populate dense tables from the already-expanded fact stream. -/
def FactTables.withDenseFactsCosted
    (tables : FactTables) (worldCount thingCount : Nat)
    (facts : Array CompiledFact) : Complexity.Costed FactTables :=
  let initialized := tables.initializeDenseCosted
    worldCount thingCount (projectionArityOfFacts facts)
  let populated := foldArrayCosted facts initialized.value
    FactTables.writeDenseFact 2
  let closures := populated.value.buildInherenceClosuresCosted
  ⟨{ populated.value with
      inherenceClosures := closures.value.reachable
      inherenceNextHops := closures.value.nextHop },
    initialized.cost + populated.cost + closures.cost⟩

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
    foldArrayCosted_value]

theorem FactTables.withDenseFactsCosted_cost
    (tables : FactTables) (worldCount thingCount : Nat)
    (facts : Array CompiledFact) :
    (tables.withDenseFactsCosted worldCount thingCount facts).cost =
      UnaryField.count * thingCount * worldCount +
      BinaryField.count * thingCount * thingCount * worldCount +
      TernaryField.count * thingCount * thingCount * thingCount * worldCount +
      thingCount * projectionArityOfFacts facts * worldCount +
      2 * facts.size +
      worldCount * (13 * thingCount ^ 3 + 9 * thingCount ^ 2 + 1) := by
  simp [FactTables.withDenseFactsCosted, Nat.mul_comm, Nat.add_assoc,
    FactTables.buildInherenceClosuresCosted_cost, foldArrayCosted_value,
    FactTables.foldl_writeDenseFact_denseWorldCount,
    FactTables.foldl_writeDenseFact_denseThingCount,
    FactTables.initializeDenseCosted]

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
  | .derived propAtWorld _ => .derived (propAtWorld world)

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

def expandScopedFactCosted
    (worldCount : Nat) (fact : ScopedCompiledFact) :
    Complexity.Costed (Array CompiledFact) :=
  let expanded := expandScopedFactCore worldCount fact
  ⟨expanded, expanded.size + 1⟩

def expandScopedFact (worldCount : Nat) (fact : ScopedCompiledFact) :
    Array CompiledFact :=
  (expandScopedFactCosted worldCount fact).value

@[simp] theorem expandScopedFactCosted_value
    (worldCount : Nat) (fact : ScopedCompiledFact) :
    (expandScopedFactCosted worldCount fact).value =
      expandScopedFact worldCount fact := rfl

/-- Expand all scoped resolved facts into ordinary world-indexed facts. -/
private def expandScopedFactsListCosted
    (worldCount : Nat) : List ScopedCompiledFact → Array CompiledFact → Nat →
      Complexity.Costed (Array CompiledFact)
  | [], out, cost => ⟨out, cost⟩
  | List.cons fact facts, out, cost =>
      let expanded := expandScopedFactCosted worldCount fact
      let out := expanded.value.foldl (fun out compiled => out.push compiled) out
      expandScopedFactsListCosted worldCount facts out (cost + expanded.cost)

def expandScopedFactsCosted
    (worldCount : Nat) (facts : Array ScopedCompiledFact) :
    Complexity.Costed (Array CompiledFact) :=
  expandScopedFactsListCosted worldCount facts.toList #[] 0

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
  have listBound : ∀ (xs : List ScopedCompiledFact)
      (out : Array CompiledFact) (initialCost bound : Nat),
      projectionArityOfFacts out ≤ bound →
      (∀ fact ∈ xs, fact.projectionArity ≤ bound) →
      projectionArityOfFacts
        (expandScopedFactsListCosted worldCount xs out initialCost).value ≤
          bound := by
    intro xs
    induction xs with
    | nil => simp [expandScopedFactsListCosted]
    | cons fact facts ih =>
        intro out initialCost bound hOut hFacts
        simp only [expandScopedFactsListCosted]
        apply ih
        · apply foldPush_projectionArity_le _ _ bound hOut
          intro compiled hCompiled
          exact (compiled.projectionArity_le_of_mem
            (expandScopedFactCore worldCount fact) hCompiled).trans
            ((expandScopedFactCore_projectionArity_le worldCount fact).trans
              (hFacts fact (by simp)))
        · intro tailFact hTail
          exact hFacts tailFact (by simp [hTail])
  apply listBound facts.toList #[] 0 (projectionArityOfScopedFacts facts)
  · simp [projectionArityOfFacts]
  · intro fact hFact
    exact fact.projectionArity_le_of_mem facts (by simpa using hFact)

def ScopedCompiledFact.expansionCharge
    (worldCount : Nat) (fact : ScopedCompiledFact) : Nat :=
  match fact with
  | .unary _ _ scope | .binary _ _ _ scope | .ternary _ _ _ _ scope
  | .tupleProjection _ _ _ scope | .derived _ scope =>
      scope.worldMultiplicity worldCount + 1

theorem expandScopedFactCosted_cost
    (worldCount : Nat) (fact : ScopedCompiledFact) :
    (expandScopedFactCosted worldCount fact).cost =
      fact.expansionCharge worldCount := by
  cases fact <;>
    simp [expandScopedFactCosted, ScopedCompiledFact.expansionCharge,
      expandScopedFactCore_size]

theorem expandScopedFactsCosted_cost
    (worldCount : Nat) (facts : Array ScopedCompiledFact) :
    (expandScopedFactsCosted worldCount facts).cost =
      (facts.toList.map (ScopedCompiledFact.expansionCharge worldCount)).sum := by
  have listCost : ∀ (xs : List ScopedCompiledFact) (out : Array CompiledFact)
      (initialCost : Nat),
      (expandScopedFactsListCosted worldCount xs out initialCost).cost =
        initialCost + (xs.map (ScopedCompiledFact.expansionCharge worldCount)).sum := by
    intro xs
    induction xs with
    | nil => simp [expandScopedFactsListCosted]
    | cons fact facts ih =>
        intro out initialCost
        simp only [expandScopedFactsListCosted]
        rw [ih]
        rw [expandScopedFactCosted_cost]
        simp
        omega
  simpa [expandScopedFactsCosted] using listCost facts.toList #[] 0

theorem expandScopedFactsCosted_value_size
    (worldCount : Nat) (facts : Array ScopedCompiledFact) :
    (expandScopedFactsCosted worldCount facts).value.size =
      (facts.toList.map (ScopedCompiledFact.expansionWeight worldCount)).sum := by
  have appendSize : ∀ (added : Array CompiledFact) (out : Array CompiledFact),
      (added.foldl (fun out compiled => out.push compiled) out).size =
        out.size + added.size := by
    intro added out
    rw [← Array.foldl_toList]
    have listSize : ∀ (xs : List CompiledFact) (initial : Array CompiledFact),
        (xs.foldl (fun result item => result.push item) initial).size =
          initial.size + xs.length := by
      intro xs
      induction xs with
      | nil => simp
      | cons x xs ih =>
          intro initial
          simp only [List.foldl_cons, List.length_cons]
          rw [ih]
          rw [Array.size_push]
          omega
    simpa using listSize added.toList out
  have listValue : ∀ (xs : List ScopedCompiledFact)
      (out : Array CompiledFact) (initialCost : Nat),
      (expandScopedFactsListCosted worldCount xs out initialCost).value.size =
        out.size + (xs.map (ScopedCompiledFact.expansionWeight worldCount)).sum := by
    intro xs
    induction xs with
    | nil => simp [expandScopedFactsListCosted]
    | cons fact facts ih =>
        intro out initialCost
        simp only [expandScopedFactsListCosted]
        rw [ih]
        rw [appendSize]
        change out.size + (expandScopedFactCore worldCount fact).size +
          (facts.map (ScopedCompiledFact.expansionWeight worldCount)).sum = _
        rw [expandScopedFactCore_size]
        cases fact <;>
          simp [ScopedCompiledFact.expansionWeight, ScopedCompiledFact.scope] <;>
          omega
  simpa [expandScopedFactsCosted] using listValue facts.toList #[] 0

theorem ScopedCompiledFact.expansionCharge_le
    (worldCount : Nat) (fact : ScopedCompiledFact) :
    fact.expansionCharge worldCount ≤ worldCount + 2 := by
  cases fact with
  | unary field x scope => cases scope <;>
      simp [ScopedCompiledFact.expansionCharge, FactScope.worldMultiplicity]
  | binary field x y scope => cases scope <;>
      simp [ScopedCompiledFact.expansionCharge, FactScope.worldMultiplicity]
  | ternary field x y z scope => cases scope <;>
      simp [ScopedCompiledFact.expansionCharge, FactScope.worldMultiplicity]
  | tupleProjection tuple index result scope => cases scope <;>
      simp [ScopedCompiledFact.expansionCharge, FactScope.worldMultiplicity]
  | derived prop scope => cases scope <;>
      simp [ScopedCompiledFact.expansionCharge, FactScope.worldMultiplicity]

/-- Coarse source-only scope-expansion bound, including zero-world sources. -/
theorem expandScopedFactsCosted_cost_le
    (worldCount : Nat) (facts : Array ScopedCompiledFact) :
    (expandScopedFactsCosted worldCount facts).cost ≤
      facts.size * (worldCount + 2) := by
  rw [expandScopedFactsCosted_cost]
  have listBound : ∀ xs : List ScopedCompiledFact,
      (xs.map (ScopedCompiledFact.expansionCharge worldCount)).sum ≤
        xs.length * (worldCount + 2) := by
    intro xs
    induction xs with
    | nil => simp
    | cons fact facts ih =>
        simp [Nat.succ_mul]
        have hhead := fact.expansionCharge_le worldCount
        omega
  simpa using listBound facts.toList

example : (expandScopedFactsCosted 3 #[
    .unary .ex 0 .everywhere,
    .binary .inst 0 1 (.at 0)]).cost = 6 := by
  native_decide

example : (expandScopedFactsCosted 0 #[.unary .ex 0 .everywhere]).cost = 1 := by
  native_decide

/-- Counted explicit AST compiler used by generated certificate models. -/
def compileExplicitModelASTCosted (ast : ModelAST) : Complexity.Costed FactTables :=
  let facts := foldArrayCosted ast.facts ({} : FactTables) compileExplicitFact 2
  let families := foldArrayCosted ast.productFamilies facts.value addProductFamily 1
  let dense := families.value.withDenseFactsCosted
    ast.worldCount ast.thingCount ast.facts
  ⟨dense.value, facts.cost + families.cost + dense.cost⟩

/--
Compact production compiler used by generated certificate declarations.

Cost instrumentation is kept out of this definition so certificate
simplification sees only table construction. The following correspondence
theorem connects it to the counted compiler used by complexity proofs.
-/
def compileExplicitModelAST (ast : ModelAST) : FactTables :=
  let tables := ast.facts.foldl compileExplicitFact {}
  let tables := ast.productFamilies.foldl addProductFamily tables
  tables.withDenseFacts ast.worldCount ast.thingCount ast.facts

/-- The counted explicit compiler computes the compact production result. -/
theorem compileExplicitModelASTCosted_value (ast : ModelAST) :
    (compileExplicitModelASTCosted ast).value = compileExplicitModelAST ast := by
  simp only [compileExplicitModelASTCosted, foldArrayCosted_value]
  exact FactTables.withDenseFactsCosted_value _ _ _ _

theorem compileExplicitModelASTCosted_cost (ast : ModelAST) :
    (compileExplicitModelASTCosted ast).cost =
      2 * ast.facts.size + ast.productFamilies.size +
        ((ast.productFamilies.foldl addProductFamily
          (ast.facts.foldl compileExplicitFact {})).withDenseFactsCosted
            ast.worldCount ast.thingCount ast.facts).cost := by
  simp [compileExplicitModelASTCosted, foldArrayCosted_value,
    Nat.mul_comm, Nat.add_assoc]

theorem compileExplicitModelASTCosted_cost_polynomial (ast : ModelAST) :
    (compileExplicitModelASTCosted ast).cost =
      4 * ast.facts.size + ast.productFamilies.size +
      UnaryField.count * ast.thingCount * ast.worldCount +
      BinaryField.count * ast.thingCount * ast.thingCount * ast.worldCount +
      TernaryField.count * ast.thingCount * ast.thingCount * ast.thingCount * ast.worldCount +
      ast.thingCount * projectionArityOfFacts ast.facts * ast.worldCount +
      ast.worldCount *
        (13 * ast.thingCount ^ 3 + 9 * ast.thingCount ^ 2 + 1) := by
  rw [compileExplicitModelASTCosted_cost]
  rw [FactTables.withDenseFactsCosted_cost]
  omega

namespace FactTables

/-- Counted lookup in the explicit unary array. -/
def unaryTypedTableCosted (tables : FactTables) (field : UnaryField)
    {thingCount worldCount : Nat}
    (x : Fin thingCount) (w : Fin worldCount) : Complexity.Costed Bool :=
  let width := tables.denseThingCount * tables.denseWorldCount
  let coordinate := unaryCoordinate x.val tables.denseWorldCount w.val
  .tick (tables.unaryCells[field.index * width + coordinate]?.getD false) 2

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
Proof-facing unary lookup over the inspectable fact stream. Native execution
uses the corresponding constant-time dense lookup. Table-correctness theorems
justify this replacement for compiled tables.
-/
@[implemented_by unaryTypedTableDense]
def unaryTypedTable (tables : FactTables) (field : UnaryField)
    {thingCount worldCount : Nat}
    (x : Fin thingCount) (w : Fin worldCount) : Bool :=
  tables.unaryLookup field.toTableField x.val w.val

/-- Constant-unit-cost lookup in the explicit binary array. -/
def binaryTypedTableCosted (tables : FactTables) (field : BinaryField)
    {thingCount worldCount : Nat}
    (x y : Fin thingCount) (w : Fin worldCount) : Complexity.Costed Bool :=
  let width := tables.denseThingCount * tables.denseThingCount * tables.denseWorldCount
  let coordinate := binaryCoordinate tables.denseThingCount tables.denseWorldCount
    x.val y.val w.val
  .tick (tables.binaryCells[field.index * width + coordinate]?.getD false) 2

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

@[implemented_by binaryTypedTableDense]
def binaryTypedTable (tables : FactTables) (field : BinaryField)
    {thingCount worldCount : Nat}
    (x y : Fin thingCount) (w : Fin worldCount) : Bool :=
  tables.binaryLookup field.toTableField x.val y.val w.val

/-- Constant-unit-cost lookup in the explicit ternary array. -/
def ternaryTypedTableCosted (tables : FactTables) (field : TernaryField)
    {thingCount worldCount : Nat}
    (x y z : Fin thingCount) (w : Fin worldCount) : Complexity.Costed Bool :=
  let width := tables.denseThingCount ^ 3 * tables.denseWorldCount
  let coordinate := ternaryCoordinate tables.denseThingCount tables.denseWorldCount
    x.val y.val z.val w.val
  .tick (tables.ternaryCells[field.index * width + coordinate]?.getD false) 2

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
      tables.ternaryTypedTableDense field x y z w := rfl

@[implemented_by ternaryTypedTableDense]
def ternaryTypedTable (tables : FactTables) (field : TernaryField)
    {thingCount worldCount : Nat}
    (x y z : Fin thingCount) (w : Fin worldCount) : Bool :=
  tables.ternaryLookup field.toTableField x.val y.val z.val w.val

/-- Direct projection lookup; no scan over candidate things is performed. -/
def tupleProjectionTypedTableCosted (tables : FactTables)
    {thingCount worldCount : Nat}
    (p : Fin thingCount) (i : Nat) (w : Fin worldCount) :
    Complexity.Costed (Fin thingCount) :=
  .tick (if i < tables.denseProjectionArity then
    let coordinate := projectionCoordinate tables.denseProjectionArity
      tables.denseWorldCount p.val i w.val
    match tables.projectionCells[coordinate]?.join with
    | some result => if h : result < thingCount then ⟨result, h⟩ else p
    | none => p
  else p) 2

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
      tables.tupleProjectionTypedTableDense p i w := rfl

@[implemented_by tupleProjectionTypedTableDense]
def tupleProjectionTypedTable (tables : FactTables)
    {thingCount worldCount : Nat}
    (p : Fin thingCount) (i : Nat) (w : Fin worldCount) : Fin thingCount :=
  match tables.tupleProjectionResult? p.val i w.val with
  | some result => if h : result < thingCount then ⟨result, h⟩ else p
  | none => p

/-- Constant-unit-cost lookup in the precomputed inherence closure. -/
def inherenceClosureTableCosted (tables : FactTables)
    {thingCount worldCount : Nat}
    (m b : Fin thingCount) (w : Fin worldCount) : Complexity.Costed Bool :=
  .tick (match tables.inherenceClosures[w.val]? with
  | some closure =>
      closure[Complexity.matrixIndex tables.denseThingCount m.val b.val]?.getD false
  | none => false) 3

def inherenceClosureTable (tables : FactTables)
    {thingCount worldCount : Nat}
    (m b : Fin thingCount) (w : Fin worldCount) : Bool :=
  match tables.inherenceClosures[w.val]? with
  | some closure =>
      closure[Complexity.matrixIndex tables.denseThingCount m.val b.val]?.getD false
  | none => false

@[simp] theorem unaryTypedTableCosted_cost (tables : FactTables) (field : UnaryField)
    {thingCount worldCount : Nat} (x : Fin thingCount) (w : Fin worldCount) :
    (tables.unaryTypedTableCosted field x w).cost = 2 := rfl

@[simp] theorem binaryTypedTableCosted_cost (tables : FactTables) (field : BinaryField)
    {thingCount worldCount : Nat} (x y : Fin thingCount) (w : Fin worldCount) :
    (tables.binaryTypedTableCosted field x y w).cost = 2 := rfl

@[simp] theorem ternaryTypedTableCosted_cost (tables : FactTables) (field : TernaryField)
    {thingCount worldCount : Nat} (x y z : Fin thingCount) (w : Fin worldCount) :
    (tables.ternaryTypedTableCosted field x y z w).cost = 2 := rfl

@[simp] theorem tupleProjectionTypedTableCosted_cost (tables : FactTables)
    {thingCount worldCount : Nat} (p : Fin thingCount) (i : Nat) (w : Fin worldCount) :
    (tables.tupleProjectionTypedTableCosted p i w).cost = 2 := rfl

@[simp] theorem inherenceClosureTableCosted_cost (tables : FactTables)
    {thingCount worldCount : Nat} (m b : Fin thingCount) (w : Fin worldCount) :
    (tables.inherenceClosureTableCosted m b w).cost = 3 := rfl

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

/--
Follow deterministic first-hop cells. Fuel makes malformed external tables
total; compiled tables need at most `thingCount` hops. Each recursion performs
one indexed lookup rather than scanning all possible adjacent things.
-/
def nextHopPathFromCosted
    (nextHop : Array (Option Nat)) (thingCount current target fuel : Nat)
    (pathAcc : Array Nat := #[]) : Complexity.Costed (Option (Array Nat)) :=
  if current == target then
    .tick (some (pathAcc.push current)) 2
  else match fuel with
  | 0 => .tick none 1
  | fuel + 1 =>
      match nextHop[Complexity.matrixIndex thingCount current target]?.join with
      | none => .tick none 2
      | some next =>
          Complexity.Costed.charge 4
            (nextHopPathFromCosted nextHop thingCount next target fuel
              (pathAcc.push current))

def nextHopPathFrom?
    (nextHop : Array (Option Nat)) (thingCount current target fuel : Nat) :
    Option (Array Nat) :=
  (nextHopPathFromCosted nextHop thingCount current target fuel).value

@[simp] theorem nextHopPathFromCosted_value
    (nextHop : Array (Option Nat)) (thingCount current target fuel : Nat) :
    (nextHopPathFromCosted nextHop thingCount current target fuel).value =
      nextHopPathFrom? nextHop thingCount current target fuel := rfl

theorem nextHopPathFromCosted_cost_le
    (nextHop : Array (Option Nat)) (thingCount current target fuel : Nat)
    (pathAcc : Array Nat) :
    (nextHopPathFromCosted nextHop thingCount current target fuel pathAcc).cost ≤
      4 * fuel + 2 := by
  induction fuel generalizing current pathAcc with
  | zero =>
      simp only [nextHopPathFromCosted]
      split <;> simp
  | succ fuel ih =>
      simp only [nextHopPathFromCosted]
      split
      · simp
      · split
        · simp
        · simp only [Complexity.Costed.charge]
          apply Nat.le_trans (Nat.add_le_add_left (ih _ _) 4)
          omega

private def threeNodeNextHop : Array (Option Nat) :=
  #[some 0, some 1, some 1,
    none, some 1, some 2,
    none, none, some 2]

example : nextHopPathFrom? threeNodeNextHop 3 0 2 3 = some #[0, 1, 2] := by
  native_decide

example : nextHopPathFromCosted threeNodeNextHop 3 0 2 3 =
    ⟨some #[0, 1, 2], 10⟩ := by
  native_decide

example : nextHopPathFrom? threeNodeNextHop 3 2 0 3 = none := by
  native_decide

/-- A concrete inherence path reconstructed from the compiled next-hop matrix. -/
def momentOfPathCosted
    (tables : FactTables) (thingCount : Nat) (world moment bearer : Nat) :
    Complexity.Costed (Option (Array Nat)) :=
  match tables.inherenceNextHops[world]? with
  | some nextHop => Complexity.Costed.charge 1
      (nextHopPathFromCosted nextHop thingCount moment bearer thingCount)
  | none => .tick none 1

def momentOfPath?
    (tables : FactTables) (thingCount : Nat) (world moment bearer : Nat) :
    Option (Array Nat) :=
  (tables.momentOfPathCosted thingCount world moment bearer).value

@[simp] theorem momentOfPathCosted_value
    (tables : FactTables) (thingCount : Nat) (world moment bearer : Nat) :
    (tables.momentOfPathCosted thingCount world moment bearer).value =
      tables.momentOfPath? thingCount world moment bearer := rfl

theorem momentOfPathCosted_cost_le
    (tables : FactTables) (thingCount : Nat) (world moment bearer : Nat) :
    (tables.momentOfPathCosted thingCount world moment bearer).cost ≤
      4 * thingCount + 3 := by
  unfold FactTables.momentOfPathCosted
  split
  · simp only [Complexity.Costed.charge]
    apply Nat.le_trans (Nat.add_le_add_left
      (nextHopPathFromCosted_cost_le _ thingCount moment bearer thingCount #[]) 1)
    omega
  · simp

private def natToFin? (n x : Nat) : Option (Fin n) :=
  if h : x < n then some ⟨x, h⟩ else none

private def natArrayToFinArray? (n : Nat) (xs : Array Nat) : Option (Array (Fin n)) :=
  xs.foldl
    (fun acc? x =>
      match acc?, natToFin? n x with
      | some acc, some x => some (acc.push x)
      | _, _ => none)
    (some #[])

private def productFamilyWitnesses
    (worldCount thingCount : Nat) (families : Array ProductFamilySpec) :
    Array (ProductFamilyWitness thingCount worldCount) :=
  Id.run do
    let mut out := #[]
    for family in families do
      for w in [:worldCount] do
        match natToFin? thingCount family.domain,
            natToFin? thingCount family.qualityType,
            natToFin? worldCount w,
            natArrayToFinArray? thingCount family.dimensionThings,
            natArrayToFinArray? thingCount family.typeThings with
        | some domain, some qualityType, some world, some dimensionThings, some typeThings =>
            if h : dimensionThings.size = typeThings.size then
              out := out.push
                { domain := domain
                  qualityType := qualityType
                  world := world
                  dimensionThings := dimensionThings
                  typeThings := typeThings
                  sameSize := h }
        | _, _, _, _, _ => pure ()
    pure out

/--
Compile finite tables into a `FiniteModel4`.

This pure constructor defines the finite-model record fields used by generated
DSL models. Primitive distance, set-membership, and tuple-projection tables are
read from the DSL facts; higher-arity definition-like relations that are not
primitive surface syntax remain derived in `FiniteModel4.toUFOSignature4`.
-/
def toFiniteModel4
    (worldCount thingCount : Nat)
    (worldPositive : 0 < worldCount)
    (thingPositive : 0 < thingCount)
    (tables : FactTables) : FiniteModel4 :=
{ worldCount := worldCount
  thingCount := thingCount
  worldPositive := worldPositive
  thingPositive := thingPositive

  inst := tables.binaryTypedTable .inst
  sub := tables.binaryTypedTable .sub

  concreteIndividual := tables.unaryTypedTable .concreteIndividual
  abstractIndividual := tables.unaryTypedTable .abstractIndividual
  endurant := tables.unaryTypedTable .endurant
  perdurant := tables.unaryTypedTable .perdurant
  endurantType := tables.unaryTypedTable .endurantType
  perdurantType := tables.unaryTypedTable .perdurantType
  rigid := tables.unaryTypedTable .rigid
  antiRigid := tables.unaryTypedTable .antiRigid
  semiRigid := tables.unaryTypedTable .semiRigid
  kind := tables.unaryTypedTable .kind
  sortal := tables.unaryTypedTable .sortal
  nonSortal := tables.unaryTypedTable .nonSortal
  subKind := tables.unaryTypedTable .subKind
  phase := tables.unaryTypedTable .phase
  role := tables.unaryTypedTable .role
  semiRigidSortal := tables.unaryTypedTable .semiRigidSortal
  category := tables.unaryTypedTable .category
  mixin := tables.unaryTypedTable .mixin
  phaseMixin := tables.unaryTypedTable .phaseMixin
  roleMixin := tables.unaryTypedTable .roleMixin

  substantial := tables.unaryTypedTable .substantial
  moment := tables.unaryTypedTable .moment
  object := tables.unaryTypedTable .object
  collective := tables.unaryTypedTable .collective
  quantity := tables.unaryTypedTable .quantity
  relator := tables.unaryTypedTable .relator
  intrinsicMoment := tables.unaryTypedTable .intrinsicMoment
  mode := tables.unaryTypedTable .mode
  qualityKind := tables.unaryTypedTable .qualityKind

  substantialType := tables.unaryTypedTable .substantialType
  momentType := tables.unaryTypedTable .momentType
  objectType := tables.unaryTypedTable .objectType
  collectiveType := tables.unaryTypedTable .collectiveType
  quantityType := tables.unaryTypedTable .quantityType
  relatorType := tables.unaryTypedTable .relatorType
  modeType := tables.unaryTypedTable .modeType
  qualityType := tables.unaryTypedTable .qualityType
  objectKind := tables.unaryTypedTable .objectKind
  collectiveKind := tables.unaryTypedTable .collectiveKind
  quantityKind := tables.unaryTypedTable .quantityKind
  relatorKind := tables.unaryTypedTable .relatorKind
  modeKind := tables.unaryTypedTable .modeKind

  part := fun x y w => x == y || tables.binaryTypedTable .part x y w
  overlap := fun x y w => x == y || tables.binaryTypedTable .overlap x y w
  properPart := tables.binaryTypedTable .properPart

  functionsAs := tables.binaryTypedTable .functionsAs
  genericFunctionalDependence := tables.binaryTable "genericFunctionalDependence"
  individualFunctionalDependence := fun _ _ _ _ _ => false
  componentOf := fun _ _ _ _ _ => false

  ex := tables.unaryTypedTable .ex
  constitutedBy := tables.binaryTypedTable .constitutedBy
  genericConstitutionalDependence := tables.binaryTable "genericConstitutionalDependence"
  constitution := fun _ _ _ _ _ => false

  existentialDependence := tables.binaryTable "existentialDependence"
  existentialIndependence := tables.binaryTable "existentialIndependence"
  inheresIn := tables.binaryTypedTable .inheresIn

  externallyDependent := tables.binaryTable "externallyDependent"
  externallyDependentMode := tables.unaryTable "externallyDependentMode"
  foundedBy := tables.binaryTypedTable .foundedBy
  quaIndividualOf := tables.binaryTypedTable .quaIndividualOf
  quaIndividual := tables.unaryTable "quaIndividual"
  mediates := tables.binaryTypedTable .mediates

  characterization := tables.binaryTypedTable .characterization

  quale := tables.unaryTypedTable .quale
  set_ := tables.unaryTypedTable .set_
  memberOf := tables.binaryTypedTable .memberOf
  setExtension := fun s w => {x | tables.binaryTypedTable .memberOf x s w = true}
  qualityDomain := tables.unaryTypedTable .qualityDomain
  qualityDimension := tables.unaryTypedTable .qualityDimension
  associatedWith := tables.binaryTypedTable .associatedWith
  intrinsicMomentType := tables.unaryTypedTable .intrinsicMomentType
  hasValue := tables.binaryTypedTable .hasValue
  tupleProjection := fun {_n} p i w => tables.tupleProjectionTypedTable p i.val w
  productFamilies := productFamilyWitnesses worldCount thingCount tables.productFamilies
  distance := tables.ternaryTypedTable .distance
  distanceZero := tables.unaryTypedTable .distanceZero
  distanceSum := tables.ternaryTypedTable .distanceSum
  distanceGreaterEq := tables.binaryTypedTable .distanceGreaterEq

  manifests := tables.binaryTypedTable .manifests
  lifeOf := tables.binaryTypedTable .lifeOf
  meet := tables.binaryTypedTable .meet }

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

/--
Append reflexive specialization witnesses while consuming the fact stream
once. Repeated instantiation targets may emit identical witnesses; dense-table
materialization is idempotent for those duplicates. Avoiding a hash-set here
keeps the source bound deterministic and comparison-free.
-/
private def addReflexiveSpecializationFactsList
    (worldCount : Nat) : List CompiledFact → Array CompiledFact → Array CompiledFact
  | [], out => out
  | List.cons fact facts, out =>
      let out := match fact with
        | .binary .inst _ target _ =>
            pushAll out (reflexiveSpecializationFactsFor worldCount target)
        | _ => out
      addReflexiveSpecializationFactsList worldCount facts out

private def addReflexiveSpecializationFactsCore
    (worldCount : Nat) (facts : Array CompiledFact) : Array CompiledFact :=
  addReflexiveSpecializationFactsList worldCount facts.toList facts

theorem addReflexiveSpecializationFactsCore_size_le
    (worldCount : Nat) (facts : Array CompiledFact) :
    (addReflexiveSpecializationFactsCore worldCount facts).size ≤
      facts.size * (worldCount + 1) := by
  have listBound : ∀ (xs : List CompiledFact) (out : Array CompiledFact),
      (addReflexiveSpecializationFactsList worldCount xs out).size ≤
        out.size + xs.length * worldCount := by
    intro xs
    induction xs with
    | nil => simp [addReflexiveSpecializationFactsList]
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
        simp only [addReflexiveSpecializationFactsList]
        exact htail.trans (by
          simp only [List.length_cons, Nat.succ_mul]
          omega)
  have h := listBound facts.toList facts
  simpa [addReflexiveSpecializationFactsCore, Nat.mul_add,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

def addReflexiveSpecializationFactsCosted
    (worldCount : Nat) (facts : Array CompiledFact) :
    Complexity.Costed (Array CompiledFact) :=
  let expanded := addReflexiveSpecializationFactsCore worldCount facts
  ⟨expanded, facts.size + expanded.size⟩

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
  simpa [addReflexiveSpecializationFactsCosted] using
    addReflexiveSpecializationFactsCore_size_le worldCount facts

theorem addReflexiveSpecializationFactsCosted_projectionArity_le
    (worldCount : Nat) (facts : Array CompiledFact) :
    projectionArityOfFacts
      (addReflexiveSpecializationFactsCosted worldCount facts).value ≤
      projectionArityOfFacts facts := by
  have listBound : ∀ (xs : List CompiledFact) (out : Array CompiledFact)
      (bound : Nat),
      projectionArityOfFacts out ≤ bound →
      projectionArityOfFacts
        (addReflexiveSpecializationFactsList worldCount xs out) ≤ bound := by
    intro xs
    induction xs with
    | nil => simp [addReflexiveSpecializationFactsList]
    | cons fact facts ih =>
        intro out bound hOut
        simp only [addReflexiveSpecializationFactsList]
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
  change projectionArityOfFacts
    (addReflexiveSpecializationFactsList worldCount facts.toList facts) ≤ _
  exact listBound facts.toList facts (projectionArityOfFacts facts) le_rfl

theorem addReflexiveSpecializationFactsCosted_cost_le
    (worldCount : Nat) (facts : Array CompiledFact) :
    (addReflexiveSpecializationFactsCosted worldCount facts).cost ≤
      facts.size * (worldCount + 2) := by
  unfold addReflexiveSpecializationFactsCosted
  have h := addReflexiveSpecializationFactsCore_size_le worldCount facts
  calc
    facts.size + (addReflexiveSpecializationFactsCore worldCount facts).size ≤
        facts.size + facts.size * (worldCount + 1) := Nat.add_le_add_left h _
    _ = facts.size * (worldCount + 2) := by
      simp [Nat.mul_add, Nat.mul_two]
      omega

example : (addReflexiveSpecializationFactsCosted 2 #[
    .binary .inst 0 1 0, .binary .inst 2 1 1]).value.size = 6 := by
  native_decide

example : (addReflexiveSpecializationFactsCosted 2 #[
    .binary .inst 0 1 0, .binary .inst 2 1 1]).cost = 8 := by
  native_decide

private partial def expandUnaryTaxonomyFieldsAux
    (field : UnaryField) (seen : Std.HashSet String) :
    Array UnaryField × Std.HashSet String :=
  let tableField := field.toTableField
  if seen.contains tableField then
    (#[], seen)
  else
    let seen := seen.insert tableField
    let init := (#[field], seen)
    unaryTaxonomyParents tableField |>.foldl
      (fun (acc : Array UnaryField × Std.HashSet String) parent =>
        match UnaryField.fromTableField? parent with
        | some parentField =>
            let expanded := expandUnaryTaxonomyFieldsAux parentField acc.2
            (acc.1 ++ expanded.1, expanded.2)
        | none => acc)
      init

/-- Finite structural taxonomy closure, independent of model coordinates. -/
def expandUnaryTaxonomyFields (field : UnaryField) : Array UnaryField :=
  (expandUnaryTaxonomyFieldsAux field {}).1

/-- Expand one unary fact into itself plus deterministic taxonomy ancestors. -/
def expandUnaryTaxonomyFact (field : UnaryField) (x w : Nat) : Array CompiledFact :=
  (expandUnaryTaxonomyFields field).map fun expandedField =>
    .unary expandedField x w

@[simp] theorem expandUnaryTaxonomyFact_size
    (field : UnaryField) (x w : Nat) :
    (expandUnaryTaxonomyFact field x w).size =
      (expandUnaryTaxonomyFields field).size := by
  simp [expandUnaryTaxonomyFact]

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
          expandUnaryTaxonomyFact_size, Function.comp_def, sum_map_range_const]
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

private theorem foldPush_taxonomyEmissionCount
    (added out : Array CompiledFact) :
    (((added.foldl (fun result fact => result.push fact) out).toList.map
      CompiledFact.taxonomyEmissionCount).sum) =
      (out.toList.map CompiledFact.taxonomyEmissionCount).sum +
        (added.toList.map CompiledFact.taxonomyEmissionCount).sum := by
  rw [← Array.foldl_toList]
  induction added.toList generalizing out with
  | nil => simp
  | cons fact facts ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp
      omega

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
      (out : Array CompiledFact) (initialCost : Nat),
      ((expandScopedFactsListCosted worldCount xs out initialCost).value.toList.map
        CompiledFact.taxonomyEmissionCount).sum =
        (out.toList.map CompiledFact.taxonomyEmissionCount).sum +
          (xs.map (ScopedCompiledFact.taxonomyWeight worldCount)).sum := by
    intro xs
    induction xs with
    | nil => simp [expandScopedFactsListCosted]
    | cons fact facts ih =>
        intro out initialCost
        simp only [expandScopedFactsListCosted]
        rw [ih, foldPush_taxonomyEmissionCount]
        simp only [expandScopedFactCosted]
        rw [expandScopedFactCore_taxonomyEmissionCount]
        simp
        omega
  simpa [expandScopedFactsCosted] using listValue facts.toList #[] 0

/--
Accumulator form avoids repeated array concatenation while preserving the
left-to-right order of taxonomy consequences.
-/
private def addTaxonomyFactsList :
    List CompiledFact → Array CompiledFact → Array CompiledFact
  | [], out => out
  | List.cons fact facts, out =>
      let out := match fact with
        | .unary field x w => pushAll out (expandUnaryTaxonomyFact field x w)
        | _ => out.push fact
      addTaxonomyFactsList facts out

/-- Make all deterministic unary taxonomy consequences explicit in an AST fact list. -/
private def addTaxonomyFactsCore (facts : Array CompiledFact) : Array CompiledFact :=
  addTaxonomyFactsList facts.toList #[]

theorem addTaxonomyFactsCore_size (facts : Array CompiledFact) :
    (addTaxonomyFactsCore facts).size =
      (facts.toList.map CompiledFact.taxonomyEmissionCount).sum := by
  have listSize : ∀ (xs : List CompiledFact) (out : Array CompiledFact),
      (addTaxonomyFactsList xs out).size = out.size +
        (xs.map CompiledFact.taxonomyEmissionCount).sum := by
    intro xs
    induction xs with
    | nil => simp [addTaxonomyFactsList]
    | cons fact facts ih =>
        intro out
        cases fact <;>
          simp [addTaxonomyFactsList, ih, CompiledFact.taxonomyEmissionCount,
            pushAll_size] <;> omega
  simpa [addTaxonomyFactsCore] using listSize facts.toList #[]

def addTaxonomyFactsCosted (facts : Array CompiledFact) :
    Complexity.Costed (Array CompiledFact) :=
  let expanded := addTaxonomyFactsCore facts
  ⟨expanded, facts.size + expanded.size⟩

theorem addTaxonomyFactsCosted_value_size (facts : Array CompiledFact) :
    (addTaxonomyFactsCosted facts).value.size =
      (facts.toList.map CompiledFact.taxonomyEmissionCount).sum := by
  simpa [addTaxonomyFactsCosted] using addTaxonomyFactsCore_size facts

theorem addTaxonomyFactsCosted_projectionArity_le
    (facts : Array CompiledFact) :
    projectionArityOfFacts (addTaxonomyFactsCosted facts).value ≤
      projectionArityOfFacts facts := by
  have listBound : ∀ (xs : List CompiledFact) (out : Array CompiledFact)
      (bound : Nat),
      projectionArityOfFacts out ≤ bound →
      (∀ fact ∈ xs, fact.projectionArity ≤ bound) →
      projectionArityOfFacts (addTaxonomyFactsList xs out) ≤ bound := by
    intro xs
    induction xs with
    | nil => simp [addTaxonomyFactsList]
    | cons fact facts ih =>
        intro out bound hOut hFacts
        simp only [addTaxonomyFactsList]
        apply ih
        · cases fact with
          | unary field x w =>
              apply foldPush_projectionArity_le _ _ bound hOut
              intro emitted hEmitted
              simp [expandUnaryTaxonomyFact] at hEmitted
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
  change projectionArityOfFacts (addTaxonomyFactsList facts.toList #[]) ≤ _
  apply listBound facts.toList #[] (projectionArityOfFacts facts)
  · simp [projectionArityOfFacts]
  · intro fact hFact
    exact fact.projectionArity_le_of_mem facts (by simpa using hFact)

def addTaxonomyFacts (facts : Array CompiledFact) : Array CompiledFact :=
  (addTaxonomyFactsCosted facts).value

@[simp] theorem addTaxonomyFactsCosted_value (facts : Array CompiledFact) :
    (addTaxonomyFactsCosted facts).value = addTaxonomyFacts facts := rfl

/--
Exact operational charge for taxonomy materialization: one visit per input fact
and one emitted-item charge per explicit consequence.  This output-sensitive
form avoids pretending that the finite taxonomy traversal is free; its later
source theorem connects the emitted size to `SourceMetrics.taxonomyFacts`.
-/
theorem addTaxonomyFactsCosted_cost (facts : Array CompiledFact) :
    (addTaxonomyFactsCosted facts).cost =
      facts.size + (addTaxonomyFacts facts).size := rfl

def exceptOkCosted (result : Complexity.Costed α) :
    Complexity.Costed (Except ε α) :=
  result.map Except.ok

def buildWorldNameIndexCosted (source : ModelSource) :
    Complexity.Costed (Except ResolveError NameIndex) :=
  (buildNameIndexCosted source.worlds).map fun
    | .ok index => .ok index
    | .error name => .error (.duplicateWorld name)

def buildThingNameIndexCosted (source : ModelSource) :
    Complexity.Costed (Except ResolveError NameIndex) :=
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
