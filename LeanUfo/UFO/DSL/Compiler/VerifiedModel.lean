import LeanUfo.UFO.DSL.Complexity.Tables

/-!
# Verified native model interpretation

Compiled facts justify the equality required by `FactTables.verifiedLookups`.
The frontend passes this proof and cache correctness to
`FactTables.toFiniteModel4Cached`. Its underlying verified constructor uses
dense tables for native checking and compact sparse definitions for kernel
reduction. The proofs cover the exact tables, cache, and finite dimensions
passed to the constructor. The cache changes execution, not UFO semantics.
The source invariants also bound the ordered metadata rows used by reuse
planning. Dense materialization preserves those rows, including duplicates.
-/

namespace LeanUfo.UFO.DSL

open Complexity.Production

/-!
## Source-name coordinate bounds

The index builder assigns consecutive coordinates. After a successful scan,
every stored coordinate is smaller than the input name count. The map itself
allows arbitrary natural numbers, so resolvers must carry this invariant from
index construction rather than assume it for every hand-built `NameIndex`.
-/

/-- Every successful lookup stays within the declared coordinate domain. -/
def NameIndex.InBounds (index : NameIndex) (size : Nat) : Prop :=
  ∀ name coordinate, index.find? name = some coordinate → coordinate < size

private theorem nameIndexFold_inBounds (names : List String)
    (start : Nat) (entries : Std.HashMap String Nat)
    (bounded : ∀ (name : String) (coordinate : Nat),
      entries[name]? = some coordinate → coordinate < start)
    (out : Nat × Std.HashMap String Nat)
    (success : names.foldlM
      (fun (index, entries) name =>
        if entries.contains name then .error name
        else .ok (index + 1, entries.insert name index))
      (start, entries) = Except.ok out) :
    out.1 = start + names.length ∧
      ∀ (name : String) (coordinate : Nat),
        out.2[name]? = some coordinate → coordinate < out.1 := by
  induction names generalizing start entries with
  | nil =>
      simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at success
      subst out
      exact ⟨rfl, bounded⟩
  | cons name names ih =>
      simp only [List.foldlM_cons] at success
      by_cases duplicate : entries.contains name
      · simp only [duplicate, ↓reduceIte, Bind.bind, Except.bind] at success
        cases success
      · simp only [duplicate, Bind.bind, Except.bind] at success
        have inserted : ∀ (key : String) (coordinate : Nat),
            (entries.insert name start)[key]? = some coordinate → coordinate < start + 1 := by
          intro key coordinate found
          rw [Std.HashMap.getElem?_insert] at found
          split at found
          · have := Option.some.inj found
            omega
          · exact Nat.lt_succ_of_lt (bounded key coordinate found)
        have tail := ih (start + 1) (entries.insert name start) inserted success
        exact ⟨by simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using tail.1, tail.2⟩

/-- A successful production index contains only valid source coordinates.
The proof follows the existing ordered-fold specification. Inserting the next
coordinate preserves the strict bound after incrementing the counter. -/
theorem buildNameIndex_ok_inBounds (names : Array String) (index : NameIndex)
    (success : buildNameIndex names = .ok index) : index.InBounds names.size := by
  rw [← buildNameIndexCosted_value, buildNameIndexCosted_value_eq_foldlM] at success
  cases scanned : names.foldlM
      (fun (index, entries) name =>
        if entries.contains name then Except.error name
        else Except.ok (index + 1, entries.insert name index))
      (0, ({} : Std.HashMap String Nat)) with
  | error error =>
      rw [scanned] at success
      cases success
  | ok out =>
      simp only [scanned, Except.map, Except.ok.injEq] at success
      subst index
      have bounded := nameIndexFold_inBounds names.toList 0 {}
        (by intro name coordinate found; simp at found) out
        (by simpa only [Array.foldlM_toList] using scanned)
      intro name coordinate found
      have result := bounded.2 name coordinate found
      simpa [bounded.1] using result

theorem buildWorldNameIndexCosted_ok_inBounds (source : ModelSource) (index : NameIndex)
    (success : (buildWorldNameIndexCosted source).value = .ok index) :
    index.InBounds source.worlds.size := by
  unfold buildWorldNameIndexCosted at success
  simp only [Complexity.Costed.charge_value, Complexity.Costed.map_value] at success
  cases built : (buildNameIndexCosted source.worlds).value with
  | error error =>
      rw [built] at success
      cases success
  | ok result =>
      simp only [built, Except.ok.injEq] at success
      subst index
      exact buildNameIndex_ok_inBounds source.worlds result built

theorem buildThingNameIndexCosted_ok_inBounds (source : ModelSource) (index : NameIndex)
    (success : (buildThingNameIndexCosted source).value = .ok index) :
    index.InBounds source.things.size := by
  unfold buildThingNameIndexCosted at success
  simp only [Complexity.Costed.charge_value, Complexity.Costed.map_value] at success
  cases built : (buildNameIndexCosted source.things).value with
  | error error =>
      rw [built] at success
      cases success
  | ok result =>
      simp only [built, Except.ok.injEq] at success
      subst index
      exact buildNameIndex_ok_inBounds source.things result built

/-- Resolution preserves the domain bound supplied by index construction. -/
theorem resolveThingIndexed_ok_lt (index : NameIndex) (size : Nat)
    (bounded : index.InBounds size) (name : String) (coordinate : Nat)
    (success : resolveThingIndexed index name = .ok coordinate) : coordinate < size := by
  unfold resolveThingIndexed at success
  cases found : index.find? name with
  | none => simp [found] at success
  | some value =>
      simp [found] at success
      have equal := Except.ok.inj success
      subst coordinate
      exact bounded name value found

theorem resolveWorldIndexed_ok_lt (index : NameIndex) (size : Nat)
    (bounded : index.InBounds size) (name : String) (coordinate : Nat)
    (success : resolveWorldIndexed index name = .ok coordinate) : coordinate < size := by
  unfold resolveWorldIndexed at success
  cases found : index.find? name with
  | none => simp [found] at success
  | some value =>
      simp [found] at success
      have equal := Except.ok.inj success
      subst coordinate
      exact bounded name value found

/-- An explicit world is in range; an everywhere scope needs no coordinate. -/
def FactScope.InBounds (scope : FactScope) (worldCount : Nat) : Prop :=
  match scope with
  | .at world => world < worldCount
  | .everywhere => True

/-- Bounds for explicit coordinates before scope expansion. Projection slots
are independent of thing count. A derived proposition builder is opaque here;
its generated term needs the separate derived-fact interpretation proof. -/
def ScopedCompiledFact.InBounds (fact : ScopedCompiledFact) (W T : Nat) : Prop :=
  match fact with
  | .unary _ thing scope => thing < T ∧ scope.InBounds W
  | .binary _ left right scope => left < T ∧ right < T ∧ scope.InBounds W
  | .ternary _ first second third scope =>
      first < T ∧ second < T ∧ third < T ∧ scope.InBounds W
  | .tupleProjection tuple _ result scope => tuple < T ∧ result < T ∧ scope.InBounds W
  | .derived _ scope => scope.InBounds W

theorem resolveScopeIndexed_ok_inBounds (index : NameIndex) (W : Nat)
    (bounded : index.InBounds W) (scope : NamedFactScope) (resolved : FactScope)
    (success : resolveScopeIndexed index scope = .ok resolved) : resolved.InBounds W := by
  cases scope with
  | everywhere =>
      have equal : FactScope.everywhere = resolved := Except.ok.inj success
      subst resolved
      trivial
  | «at» name =>
      unfold resolveScopeIndexed at success
      cases found : resolveWorldIndexed index name with
      | error error => simp [found, Bind.bind, Except.bind] at success
      | ok world =>
          simp only [found, Bind.bind, Except.bind] at success
          have equal := Except.ok.inj success
          subst resolved
          exact resolveWorldIndexed_ok_lt index W bounded name world found

/-!
## Successful source compilation

The compiler returns several views of its result. Pipeline proofs must connect
those views to the same execution before combining compiler and checker costs.
The construction invariant records equality between the stored views. Separate
proofs below derive coordinate bounds from successful name resolution and show
that each expansion pass preserves them. Family readback connects the converted
witnesses to the resolved source families. The counted finite-model constructor
has separate value and cost proofs; source-to-checker costs still need to compose.
As in the staged correspondence proofs illustrated by RadixExperiment, each
boundary states its own invariant rather than assuming an unrelated later input.
-/

/-- Construction invariant for the record returned by source compilation.
The expanded facts come from this record's resolved facts, and the stored tables
come from this record's explicit AST. These equalities keep the stored views
consistent. `compileModelSource_ok_wellBounded` supplies the coordinate bounds
for primitive facts. Neither result interprets the generated derived strings. -/
structure CompiledModelSource.ConstructionInvariant (source : ModelSource)
    (compiled : CompiledModelSource) : Prop where
  worldCount : compiled.ast.worldCount = source.worlds.size
  thingCount : compiled.ast.thingCount = source.things.size
  facts : compiled.ast.facts = compiled.expandedFacts
  families : compiled.ast.productFamilies = compiled.productFamilies
  tables : compiled.tables = compileExplicitModelAST compiled.ast
  expansion : compiled.expandedFacts =
    (materializeResolvedFactsCosted source compiled.scopedFacts).value

private theorem exceptBindCosted_ok_iff
    (result : Complexity.Costed (Except ε α))
    (next : α → Complexity.Costed (Except ε β)) (out : β) :
    (exceptBindCosted result next).value = .ok out ↔
      ∃ input, result.value = .ok input ∧ (next input).value = .ok out := by
  cases h : result.value <;> simp [exceptBindCosted, h]

/-- Every successful fact-resolution branch inherits the thing and scope
bounds from its input indices. The proof follows each successful bind, without
evaluating proposition strings or imposing a thing-count bound on tuple slots. -/
theorem resolveNamedFactIndexedCosted_ok_inBounds
    (worlds things : NameIndex) (W T : Nat)
    (worldsBounded : worlds.InBounds W) (thingsBounded : things.InBounds T)
    (fact : NamedScopedFact) (resolved : ScopedCompiledFact)
    (success : (resolveNamedFactIndexedCosted worlds things fact).value = .ok resolved) :
    resolved.InBounds W T := by
  have thingBound (name : String) (coordinate : Nat)
      (h : (resolveThingIndexedCosted things name).value = .ok coordinate) : coordinate < T :=
    resolveThingIndexed_ok_lt things T thingsBounded name coordinate h
  have scopeBound (scope : NamedFactScope) (value : FactScope)
      (h : (resolveScopeIndexedCosted worlds scope).value = .ok value) : value.InBounds W :=
    resolveScopeIndexed_ok_inBounds worlds W worldsBounded scope value
      (by simpa only [resolveScopeIndexedCosted_value] using h)
  cases fact <;>
    simp only [resolveNamedFactIndexedCosted, Complexity.Costed.charge_value] at success
  all_goals
    repeat' (rw [exceptBindCosted_ok_iff] at success; obtain ⟨_, _, success⟩ := success)
    simp only [Complexity.Costed.pure_value, Except.ok.injEq] at success
    subst resolved
    simp only [ScopedCompiledFact.InBounds]
    repeat' first | apply And.intro | solve_by_elim [thingBound, scopeBound]

private theorem mapArrayExceptCosted_ok_forall
    (xs : Array α) (f : α → Complexity.Costed (Except ε β)) (property : β → Prop)
    (each : ∀ x y, (f x).value = .ok y → property y)
    (ys : Array β) (success : (mapArrayExceptCosted xs f).value = .ok ys) :
    ∀ y ∈ ys, property y := by
  have listPreserves : ∀ (xs : List α) (ys : List β),
      xs.mapM (fun x => (f x).value) = .ok ys → ∀ y ∈ ys, property y := by
    intro xs
    induction xs with
    | nil =>
        intro ys h
        simp [Pure.pure, Except.pure] at h
        subst ys
        simp
    | cons x xs ih =>
        intro ys h
        cases headResult : (f x).value with
        | error error => simp [List.mapM_cons, headResult, Bind.bind, Except.bind] at h
        | ok y =>
            cases tailResult : xs.mapM (fun x => (f x).value) with
            | error error =>
                simp [List.mapM_cons, headResult, tailResult, Bind.bind, Except.bind] at h
            | ok tail =>
                simp [List.mapM_cons, headResult, tailResult, Bind.bind, Except.bind,
                  Pure.pure, Except.pure] at h
                subst ys
                intro value member
                rcases List.mem_cons.mp member with equal | rest
                · subst value
                  exact each x y headResult
                · exact ih tail tailResult value rest
  rw [mapArrayExceptCosted_value_eq_mapM, Array.mapM_eq_mapM_toList] at success
  cases mapped : xs.toList.mapM (fun x => (f x).value) with
  | error error => simp [mapped] at success
  | ok results =>
      simp [mapped] at success
      subst ys
      simpa using listPreserves xs.toList results mapped

/-- The batch resolver preserves coordinate bounds for every returned fact.
Successful name-index construction supplies the two index premises. -/
theorem resolveSourceFactsCosted_ok_inBounds
    (source : ModelSource) (worlds things : NameIndex)
    (worldsBounded : worlds.InBounds source.worlds.size)
    (thingsBounded : things.InBounds source.things.size)
    (resolved : Array ScopedCompiledFact)
    (success : (resolveSourceFactsCosted source worlds things).value = .ok resolved) :
    ∀ fact ∈ resolved, fact.InBounds source.worlds.size source.things.size := by
  exact mapArrayExceptCosted_ok_forall source.facts
    (resolveNamedFactIndexedCosted worlds things) _
    (resolveNamedFactIndexedCosted_ok_inBounds worlds things
      source.worlds.size source.things.size worldsBounded thingsBounded) resolved success

/-- Successful family resolution validates every coordinate and preserves the
two source-array lengths. The initial length check therefore supplies the
equal-length premise required by finite witness conversion. -/
theorem resolveNamedProductFamilyIndexedCosted_ok_wellFormed
    (things : NameIndex) (T : Nat) (bounded : things.InBounds T)
    (family : NamedProductFamily) (resolved : ProductFamilySpec)
    (success : (resolveNamedProductFamilyIndexedCosted things family).value = .ok resolved) :
    resolved.WellFormed T := by
  have coordinateBound (name : String) (coordinate : Nat)
      (h : (resolveThingIndexedCosted things name).value = .ok coordinate) : coordinate < T :=
    resolveThingIndexed_ok_lt things T bounded name coordinate h
  unfold resolveNamedProductFamilyIndexedCosted at success
  simp only [Complexity.Costed.charge_value] at success
  split at success
  · cases success
  · rename_i sameSize
    have lengths : family.dimensionThings.size = family.typeThings.size := by
      simpa using sameSize
    rw [exceptBindCosted_ok_iff] at success
    obtain ⟨domain, domainResolved, success⟩ := success
    rw [exceptBindCosted_ok_iff] at success
    obtain ⟨qualityType, typeResolved, success⟩ := success
    rw [exceptBindCosted_ok_iff] at success
    obtain ⟨dimensions, dimensionsResolved, success⟩ := success
    rw [exceptBindCosted_ok_iff] at success
    obtain ⟨types, typesResolved, success⟩ := success
    simp only [Complexity.Costed.pure_value, Except.ok.injEq] at success
    subst resolved
    refine ⟨coordinateBound _ _ domainResolved, coordinateBound _ _ typeResolved, ?_, ?_, ?_⟩
    · exact mapArrayExceptCosted_ok_forall family.dimensionThings
        (resolveThingIndexedCosted things) (fun x => x < T)
        coordinateBound dimensions dimensionsResolved
    · exact mapArrayExceptCosted_ok_forall family.typeThings
        (resolveThingIndexedCosted things) (fun x => x < T)
        coordinateBound types typesResolved
    · rw [mapArrayExceptCosted_ok_size _ _ dimensions dimensionsResolved,
        mapArrayExceptCosted_ok_size _ _ types typesResolved]
      exact lengths

/-- Name resolution preserves both witness-array lengths, including repeated
names. These equalities connect conversion costs to source slot counts. -/
theorem resolveNamedProductFamilyIndexedCosted_ok_sizes
    (things : NameIndex) (family : NamedProductFamily) (resolved : ProductFamilySpec)
    (success : (resolveNamedProductFamilyIndexedCosted things family).value = .ok resolved) :
    resolved.dimensionThings.size = family.dimensionThings.size ∧
      resolved.typeThings.size = family.typeThings.size := by
  unfold resolveNamedProductFamilyIndexedCosted at success
  simp only [Complexity.Costed.charge_value] at success
  split at success
  · cases success
  · rw [exceptBindCosted_ok_iff] at success
    obtain ⟨domain, _, success⟩ := success
    rw [exceptBindCosted_ok_iff] at success
    obtain ⟨qualityType, _, success⟩ := success
    rw [exceptBindCosted_ok_iff] at success
    obtain ⟨dimensions, dimensionsResolved, success⟩ := success
    rw [exceptBindCosted_ok_iff] at success
    obtain ⟨types, typesResolved, success⟩ := success
    simp only [Complexity.Costed.pure_value, Except.ok.injEq] at success
    subst resolved
    exact ⟨mapArrayExceptCosted_ok_size _ _ dimensions dimensionsResolved,
      mapArrayExceptCosted_ok_size _ _ types typesResolved⟩

/-- Batch resolution inherits the index invariant from source-name validation. -/
theorem resolveSourceProductFamiliesCosted_ok_wellFormed
    (source : ModelSource) (things : NameIndex)
    (bounded : things.InBounds source.things.size) (families : Array ProductFamilySpec)
    (success : (resolveSourceProductFamiliesCosted source things).value = .ok families) :
    ∀ family ∈ families, family.WellFormed source.things.size := by
  exact mapArrayExceptCosted_ok_forall source.productFamilies
    (resolveNamedProductFamilyIndexedCosted things) _
    (resolveNamedProductFamilyIndexedCosted_ok_wellFormed things source.things.size bounded)
    families success

/-- Exact record returned by the resolved-source tail. Projection validation
can reject the tail but cannot change its facts or resolved inputs. -/
theorem compileResolvedSourceCosted_ok_result
    (source : ModelSource) (scopedFacts : Array ScopedCompiledFact)
    (families : Array ProductFamilySpec) (compiled : CompiledModelSource)
    (success : (compileResolvedSourceCosted source scopedFacts families).value = .ok compiled) :
    compiled =
      let expanded := (materializeResolvedFactsCosted source scopedFacts).value
      let ast : ModelAST :=
        { worldCount := source.worlds.size, thingCount := source.things.size,
          facts := expanded, productFamilies := families }
      { scopedFacts := scopedFacts, productFamilies := families,
        expandedFacts := expanded, ast := ast, tables := compileExplicitModelAST ast } := by
  unfold compileResolvedSourceCosted at success
  rw [exceptBindCosted_ok_iff] at success
  obtain ⟨expanded, hexpanded, success⟩ := success
  simp only [exceptOkCosted, Complexity.Costed.map_value, Except.ok.injEq] at hexpanded
  subst expanded
  rw [exceptBindCosted_ok_iff] at success
  obtain ⟨validated, _, success⟩ := success
  simp only [Complexity.Costed.map_value, compileExplicitModelASTCosted_value,
    Except.ok.injEq] at success
  exact success.symm

/-- Construction consistency follows from the exact returned record, without
positivity or coordinate-boundedness assumptions. -/
theorem compileResolvedSourceCosted_ok_constructionInvariant
    (source : ModelSource) (scopedFacts : Array ScopedCompiledFact)
    (families : Array ProductFamilySpec) (compiled : CompiledModelSource)
    (success : (compileResolvedSourceCosted source scopedFacts families).value = .ok compiled) :
    compiled.ConstructionInvariant source := by
  rw [compileResolvedSourceCosted_ok_result source scopedFacts families compiled success]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Successful source compilation produces internally consistent dimensions,
facts, families, and tables. The hypothesis names the actual returned record;
an arbitrary finite model cannot stand in for that result. -/
theorem compileModelSource_ok_constructionInvariant
    (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled) :
    compiled.ConstructionInvariant source := by
  unfold compileModelSource compileModelSourceCosted at success
  rw [exceptBindCosted_ok_iff] at success
  obtain ⟨worldIndex, _, success⟩ := success
  rw [exceptBindCosted_ok_iff] at success
  obtain ⟨thingIndex, _, success⟩ := success
  rw [exceptBindCosted_ok_iff] at success
  obtain ⟨scopedFacts, _, success⟩ := success
  rw [exceptBindCosted_ok_iff] at success
  obtain ⟨families, _, success⟩ := success
  exact compileResolvedSourceCosted_ok_constructionInvariant source scopedFacts families compiled success

/-- Primitive thing coordinates and explicit worlds in the returned scoped
facts are in bounds. Both index premises come from the same compiler execution.
The tail-record equality identifies the returned array with the resolver output. -/
theorem compileModelSource_ok_scopedFacts_inBounds
    (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled) :
    ∀ fact ∈ compiled.scopedFacts, fact.InBounds source.worlds.size source.things.size := by
  unfold compileModelSource compileModelSourceCosted at success
  rw [exceptBindCosted_ok_iff] at success
  obtain ⟨worlds, worldBuilt, success⟩ := success
  rw [exceptBindCosted_ok_iff] at success
  obtain ⟨things, thingBuilt, success⟩ := success
  rw [exceptBindCosted_ok_iff] at success
  obtain ⟨scopedFacts, factsResolved, success⟩ := success
  rw [exceptBindCosted_ok_iff] at success
  obtain ⟨families, _, success⟩ := success
  rw [compileResolvedSourceCosted_ok_result source scopedFacts families compiled success]
  exact resolveSourceFactsCosted_ok_inBounds source worlds things
    (buildWorldNameIndexCosted_ok_inBounds source worlds worldBuilt)
    (buildThingNameIndexCosted_ok_inBounds source things thingBuilt) scopedFacts factsResolved

/-- Families in a successful source result have valid coordinates and equal
array lengths. The proof uses the actual thing index and family resolver from
that execution, not an independently supplied collection of witnesses. -/
theorem compileModelSource_ok_families_wellFormed
    (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled) :
    ∀ family ∈ compiled.productFamilies, family.WellFormed source.things.size := by
  unfold compileModelSource compileModelSourceCosted at success
  rw [exceptBindCosted_ok_iff] at success
  obtain ⟨worlds, _, success⟩ := success
  rw [exceptBindCosted_ok_iff] at success
  obtain ⟨things, thingsBuilt, success⟩ := success
  rw [exceptBindCosted_ok_iff] at success
  obtain ⟨scopedFacts, _, success⟩ := success
  rw [exceptBindCosted_ok_iff] at success
  obtain ⟨families, familiesResolved, success⟩ := success
  rw [compileResolvedSourceCosted_ok_result source scopedFacts families compiled success]
  exact resolveSourceProductFamiliesCosted_ok_wellFormed source things
    (buildThingNameIndexCosted_ok_inBounds source things thingsBuilt) families familiesResolved

/-- Successful compilation preserves the number of families and the total
number of slots in their two arrays. No deduplication occurs in these arrays.
The proof follows the executed resolver and final record construction. -/
theorem compileModelSource_ok_familySizes
    (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled) :
    compiled.productFamilies.size = source.productFamilies.size ∧
      (compiled.productFamilies.toList.map (fun family =>
        family.dimensionThings.size + family.typeThings.size)).sum =
      (source.productFamilies.toList.map NamedProductFamily.slotCount).sum := by
  unfold compileModelSource compileModelSourceCosted at success
  rw [exceptBindCosted_ok_iff] at success
  obtain ⟨worlds, _, success⟩ := success
  rw [exceptBindCosted_ok_iff] at success
  obtain ⟨things, _, success⟩ := success
  rw [exceptBindCosted_ok_iff] at success
  obtain ⟨scopedFacts, _, success⟩ := success
  rw [exceptBindCosted_ok_iff] at success
  obtain ⟨families, familiesResolved, success⟩ := success
  rw [compileResolvedSourceCosted_ok_result source scopedFacts families compiled success]
  refine ⟨mapArrayExceptCosted_ok_size _ _ families familiesResolved, ?_⟩
  apply mapArrayExceptCosted_preserves_weight source.productFamilies
    (resolveNamedProductFamilyIndexedCosted things) NamedProductFamily.slotCount
    (fun family => family.dimensionThings.size + family.typeThings.size) ?_
    families familiesResolved
  intro family resolved resolvedOk
  obtain ⟨dimensions, types⟩ :=
    resolveNamedProductFamilyIndexedCosted_ok_sizes things family resolved resolvedOk
  simp only [NamedProductFamily.slotCount, dimensions, types]

open private expandAtWorld expandScopedFactCore expandScopedFactsCosted_value_eq_foldl
  pushAll addTaxonomyFactsCore addTaxonomyFactsCosted_value_eq_core
  reflexiveSpecializationFactsFor addReflexiveSpecializationFactsCore
  addReflexiveSpecializationFactsCosted_value_eq_core
  from LeanUfo.UFO.DSL.Compiler

private theorem expandScopedFactCore_inBounds (W T : Nat) (fact : ScopedCompiledFact)
    (bounded : fact.InBounds W T) :
    ∀ result ∈ expandScopedFactCore W fact, factWellBounded W T result := by
  cases fact <;> rename_i scope <;> cases scope <;>
    simp_all [expandScopedFactCore, expandAtWorld, ScopedCompiledFact.InBounds,
      FactScope.InBounds, factWellBounded]

/-- Scope expansion emits only the validated explicit world or a coordinate
from the finite world range. It preserves all thing coordinates. -/
theorem expandScopedFactsCosted_inBounds (W T : Nat) (facts : Array ScopedCompiledFact)
    (bounded : ∀ fact ∈ facts, fact.InBounds W T) :
    ∀ result ∈ (expandScopedFactsCosted W facts).value, factWellBounded W T result := by
  rw [expandScopedFactsCosted_value_eq_foldl]
  apply Array.foldl_induction (fun _ out => ∀ result ∈ out, factWellBounded W T result)
    (by simp)
  intro i out previous result member
  rcases Array.mem_append.mp member with old | added
  · exact previous result old
  · exact expandScopedFactCore_inBounds W T facts[i] (bounded facts[i] (by simp)) result added

private theorem pushAll_forall (property : α → Prop) (out added : Array α)
    (previous : ∀ x ∈ out, property x) (newItems : ∀ x ∈ added, property x) :
    ∀ x ∈ pushAll out added, property x := by
  unfold pushAll
  apply Array.foldl_induction (fun _ out => ∀ x ∈ out, property x) previous
  intro i out previous x member
  rcases Array.mem_push.mp member with old | equal
  · exact previous x old
  · subst x
    exact newItems added[i] (by simp)

/-- Taxonomy expansion changes the unary field, never its coordinates. -/
theorem addTaxonomyFactsCosted_inBounds (W T : Nat) (facts : Array CompiledFact)
    (bounded : ∀ fact ∈ facts, factWellBounded W T fact) :
    ∀ result ∈ (addTaxonomyFactsCosted facts).value, factWellBounded W T result := by
  rw [addTaxonomyFactsCosted_value_eq_core]
  unfold addTaxonomyFactsCore
  apply Array.foldl_induction (fun _ out => ∀ result ∈ out, factWellBounded W T result)
    (by simp)
  intro i out previous
  have inputBound := bounded facts[i] (by simp)
  cases entry : facts[i] with
  | unary field x w =>
      apply pushAll_forall _ _ _ previous
      intro result member
      rw [expandUnaryTaxonomyFact_eq_map] at member
      obtain ⟨ancestor, _, equal⟩ := Array.mem_map.mp member
      subst result
      simpa only [entry, factWellBounded] using inputBound
  | _ =>
      intro result member
      rcases Array.mem_push.mp member with old | equal
      · exact previous result old
      · subst result
        simpa only [entry] using inputBound

/-- Each added specialization uses a validated instance target twice and a
world from the finite range. Keeping the original prefix preserves its bounds. -/
theorem addReflexiveSpecializationFactsCosted_inBounds
    (W T : Nat) (facts : Array CompiledFact)
    (bounded : ∀ fact ∈ facts, factWellBounded W T fact) :
    ∀ result ∈ (addReflexiveSpecializationFactsCosted W facts).value,
      factWellBounded W T result := by
  rw [addReflexiveSpecializationFactsCosted_value_eq_core]
  unfold addReflexiveSpecializationFactsCore
  apply Array.foldl_induction (fun _ out => ∀ result ∈ out, factWellBounded W T result) bounded
  intro i out previous
  have inputBound := bounded facts[i] (by simp)
  cases entry : facts[i] with
  | binary field x y w =>
      have targetBound : y < T := by
        rw [entry] at inputBound
        exact inputBound.2.1
      cases field <;> try exact previous
      apply pushAll_forall _ _ _ previous
      intro result member
      simp only [reflexiveSpecializationFactsFor, Array.mem_map, Array.mem_range] at member
      obtain ⟨world, worldBound, equal⟩ := member
      subst result
      exact ⟨targetBound, targetBound, worldBound⟩
  | _ => exact previous

/-- Successful source compilation produces bounded explicit table facts.
The proof composes name resolution with the three fact-expansion passes.
It does not assume boundedness of the output it is meant to justify. -/
theorem compileModelSource_ok_wellBounded
    (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled) :
    explicitModelWellBounded compiled.ast := by
  have correspondence := compileModelSource_ok_constructionInvariant source compiled success
  have resolved := compileModelSource_ok_scopedFacts_inBounds source compiled success
  have expanded := expandScopedFactsCosted_inBounds source.worlds.size source.things.size
    compiled.scopedFacts resolved
  have taxonomy := addTaxonomyFactsCosted_inBounds source.worlds.size source.things.size _ expanded
  have specialized := addReflexiveSpecializationFactsCosted_inBounds
    source.worlds.size source.things.size _ taxonomy
  unfold explicitModelWellBounded
  rw [correspondence.worldCount, correspondence.thingCount, correspondence.facts,
    correspondence.expansion, materializeResolvedFactsCosted_value]
  exact specialized

instance (worldCount thingCount : Nat) (fact : CompiledFact) :
    Decidable (factWellBounded worldCount thingCount fact) := by
  cases fact <;> unfold factWellBounded <;> infer_instance

instance (ast : ModelAST) : Decidable (explicitModelWellBounded ast) := by
  unfold explicitModelWellBounded
  infer_instance

private theorem foldFamilies_eq (families : Array ProductFamilySpec) (tables : FactTables) :
    families.foldl addProductFamily tables =
      { tables with productFamilies :=
          (families.foldl (fun out family => out.push family) tables.productFamilies) } := by
  simp only [← Array.foldl_toList]
  generalize families.toList = items
  induction items generalizing tables with
  | nil => rfl
  | cons family items ih => simp only [List.foldl_cons, ih, addProductFamily]

private theorem writeDenseFact_families (tables : FactTables)
    (families : Array ProductFamilySpec) (fact : CompiledFact) :
    FactTables.writeDenseFact { tables with productFamilies := families } fact =
      { FactTables.writeDenseFact tables fact with productFamilies := families } := by
  cases fact <;> rfl

private theorem foldDense_families (facts : Array CompiledFact) (tables : FactTables)
    (families : Array ProductFamilySpec) :
    facts.foldl FactTables.writeDenseFact { tables with productFamilies := families } =
      { facts.foldl FactTables.writeDenseFact tables with productFamilies := families } := by
  simp only [← Array.foldl_toList]
  generalize facts.toList = items
  induction items generalizing tables with
  | nil => rfl
  | cons fact items ih => simp only [List.foldl_cons, writeDenseFact_families, ih]

private theorem withDenseFacts_families (tables : FactTables)
    (families : Array ProductFamilySpec) (worldCount thingCount : Nat)
    (facts : Array CompiledFact) :
    FactTables.withDenseFacts { tables with productFamilies := families }
        worldCount thingCount facts =
      { tables.withDenseFacts worldCount thingCount facts with productFamilies := families } := by
  unfold FactTables.withDenseFacts
  have hinit :
      FactTables.initializeDense { tables with productFamilies := families }
          worldCount thingCount (projectionArityOfFacts facts) =
        { tables.initializeDense worldCount thingCount (projectionArityOfFacts facts)
          with productFamilies := families } := rfl
  simp only [hinit, foldDense_families]
  rfl

private theorem foldExplicitFacts_preserves_families
    (facts : Array CompiledFact) (tables : FactTables) :
    (facts.foldl compileExplicitFact tables).productFamilies = tables.productFamilies := by
  apply Array.foldl_induction (fun _ (out : FactTables) => out.productFamilies = tables.productFamilies) rfl
  intro i out previous
  cases facts[i] <;> exact previous

private theorem foldDenseFacts_preserves_families
    (facts : Array CompiledFact) (tables : FactTables) :
    (facts.foldl FactTables.writeDenseFact tables).productFamilies = tables.productFamilies := by
  apply Array.foldl_induction (fun _ (out : FactTables) => out.productFamilies = tables.productFamilies) rfl
  intro i out previous
  cases facts[i] <;> exact previous

/-- Compilation stores the complete family array unchanged. Fact writes and
dense-table initialization cannot remove, reorder, or add family records. -/
theorem compileExplicitModelAST_productFamilies (ast : ModelAST) :
    (compileExplicitModelAST ast).productFamilies = ast.productFamilies := by
  simp only [compileExplicitModelAST, FactTables.withDenseFacts,
    foldDenseFacts_preserves_families, FactTables.initializeDense, foldFamilies_eq]
  rw [foldExplicitFacts_preserves_families]
  simpa using (Array.foldl_push_eq_append (as := ast.productFamilies)
    (bs := (#[] : Array ProductFamilySpec)) (f := id) rfl)

/-- Each explicit fact appends at most one derived proposition. Primitive
facts do not append one, and family registration and dense/cache construction
preserve the array. Duplicate assertions remain separate stored entries, so
this size bound does not assume deduplication or bounded string length. -/
theorem compileExplicitModelAST_derivedProps_size_le (ast : ModelAST) :
    (compileExplicitModelAST ast).derivedProps.size ≤ ast.facts.size := by
  have stored : (ast.facts.foldl compileExplicitFact ({} : FactTables)).derivedProps.size ≤
      ast.facts.size := by
    apply Array.foldl_induction
      (fun i (out : FactTables) => out.derivedProps.size ≤ i) (by simp)
    intro i out previous
    cases ast.facts[i] <;>
      simp only [compileExplicitFact, addUnary, addBinary, addTernary,
        addTupleProjection, addDerivedProp, Array.size_push] <;> omega
  have families (tables : FactTables) :
      (ast.productFamilies.foldl addProductFamily tables).derivedProps = tables.derivedProps := by
    apply Array.foldl_induction
      (fun _ (out : FactTables) => out.derivedProps = tables.derivedProps) rfl
    intro i out previous
    exact previous
  have dense (facts : Array CompiledFact) (tables : FactTables) :
      (facts.foldl FactTables.writeDenseFact tables).derivedProps = tables.derivedProps := by
    apply Array.foldl_induction
      (fun _ (out : FactTables) => out.derivedProps = tables.derivedProps) rfl
    intro i out previous
    cases facts[i] <;> exact previous
  simpa only [compileExplicitModelAST, FactTables.withDenseFacts, dense,
    FactTables.initializeDense, families] using stored

/-- Each ordered metadata array has at most `n` entries. Reuse planning scans
these arrays, which retain duplicate facts independently of dense-table cells. -/
def FactTables.RowSizesBoundedBy (tables : FactTables) (n : Nat) : Prop :=
  (∀ field, (tables.unary.getD field #[]).size ≤ n) ∧
  (∀ field, (tables.binary.getD field #[]).size ≤ n) ∧
  (∀ field, (tables.ternary.getD field #[]).size ≤ n) ∧
  tables.tupleProjection.size ≤ n

private theorem insert_row_size_le (rows : Std.HashMap String (Array α))
    (key : String) (row : α) (n : Nat)
    (bounded : ∀ field, (rows.getD field #[]).size ≤ n) (field : String) :
    ((rows.insert key ((rows.getD key #[]).push row)).getD field #[]).size ≤ n + 1 := by
  have hk := bounded key
  have hf := bounded field
  simp only [Std.HashMap.getD_insert]
  split <;> (try simp only [Array.size_push]) <;> omega

/-- Each expanded fact adds at most one row. Family registration, dense-table
writes, and closure construction preserve the ordered metadata arrays used
by reuse planning. The bound includes duplicates and needs no valid coordinates. -/
theorem compileExplicitModelAST_rowSizes (ast : ModelAST) :
    (compileExplicitModelAST ast).RowSizesBoundedBy ast.facts.size := by
  have stored : (ast.facts.foldl compileExplicitFact ({} : FactTables)).RowSizesBoundedBy
      ast.facts.size := by
    apply Array.foldl_induction (fun i (out : FactTables) => out.RowSizesBoundedBy i)
      (by simp [FactTables.RowSizesBoundedBy])
    intro i out previous
    rcases previous with ⟨hu, hb, ht, hp⟩
    have hu' : ∀ f, (out.unary.getD f #[]).size ≤ i + 1 := fun f => Nat.le.step (hu f)
    have hb' : ∀ f, (out.binary.getD f #[]).size ≤ i + 1 := fun f => Nat.le.step (hb f)
    have ht' : ∀ f, (out.ternary.getD f #[]).size ≤ i + 1 := fun f => Nat.le.step (ht f)
    have hp' : out.tupleProjection.size ≤ i + 1 := Nat.le.step hp
    cases ast.facts[i] with
    | unary field x w => exact ⟨insert_row_size_le _ _ _ i hu, hb', ht', hp'⟩
    | binary field x y w => exact ⟨hu', insert_row_size_le _ _ _ i hb, ht', hp'⟩
    | ternary field x y z w => exact ⟨hu', hb', insert_row_size_le _ _ _ i ht, hp'⟩
    | tupleProjection tuple index result w =>
        exact ⟨hu', hb', ht', by
          simpa [compileExplicitFact, addTupleProjection] using (Nat.add_le_add_right hp 1)⟩
    | derived prop => exact ⟨hu', hb', ht', hp'⟩
  have families (tables : FactTables) (n : Nat) (h : tables.RowSizesBoundedBy n) :
      (ast.productFamilies.foldl addProductFamily tables).RowSizesBoundedBy n := by
    apply Array.foldl_induction (fun _ (out : FactTables) => out.RowSizesBoundedBy n) h
    intro i out previous
    exact previous
  have dense (facts : Array CompiledFact) (tables : FactTables) (n : Nat)
      (h : tables.RowSizesBoundedBy n) :
      (facts.foldl FactTables.writeDenseFact tables).RowSizesBoundedBy n := by
    apply Array.foldl_induction (fun _ (out : FactTables) => out.RowSizesBoundedBy n) h
    intro i out previous
    cases facts[i] <;> exact previous
  apply dense ast.facts _ _
  exact families _ _ stored

/-- The returned table registry is exactly the successful source result's
resolved family array. -/
theorem compileModelSource_ok_tableFamilies
    (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled) :
    compiled.tables.productFamilies = compiled.productFamilies := by
  have invariant := compileModelSource_ok_constructionInvariant source compiled success
  rw [invariant.tables, compileExplicitModelAST_productFamilies, invariant.families]

/-- Source success supplies the premises for exact witness readback. Every
resolved family survives at every world, in family-major order. This states
coordinate preservation, not satisfaction of axiom 99's relation conditions. -/
theorem compileModelSource_ok_familyWitnesses_readback
    (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled) :
    ((FactTables.productFamilyWitnessesCosted source.worlds.size source.things.size
      compiled.tables.productFamilies).value.map
        (fun witness => (witness.toSpec, witness.world.val))) =
      (compiled.productFamilies.toList.flatMap (fun family =>
        (List.range source.worlds.size).map (fun world => (family, world)))).toArray := by
  rw [compileModelSource_ok_tableFamilies source compiled success]
  exact FactTables.productFamilyWitnessesCosted_readback _ _ _
    (compileModelSource_ok_families_wellFormed source compiled success)

/-- Product-family storage does not alter any primitive table lookup. -/
theorem compiledLookups_agree (ast : ModelAST)
    (bounded : explicitModelWellBounded ast) :
    FactTables.sparseLookups ast.worldCount ast.thingCount (compileExplicitModelAST ast) =
      FactTables.denseLookups ast.worldCount ast.thingCount (compileExplicitModelAST ast) := by
  have correspondence := explicitCompilationTableCorrespondence ast bounded
  simp only [compileExplicitModelAST, foldFamilies_eq, withDenseFacts_families,
    FactTables.sparseLookups, FactTables.denseLookups]
  congr 1
  · funext field x w
    exact correspondence.unary field x w
  · funext field x y w
    exact correspondence.binary field x y w
  · funext field x y z w
    exact correspondence.ternary field x y z w
  · funext p slot w
    have pairEquality (tables : FactTables)
        (hv : tables.tupleProjectionTypedTable p slot w =
          tables.tupleProjectionTypedTableDense p slot w) :
        (⟨tables.tupleProjectionTypedTable p slot w,
          (tables.tupleProjectionTypedTableCosted p slot w).cost⟩ :
          Complexity.Costed (Fin ast.thingCount)) =
          tables.tupleProjectionTypedTableCosted p slot w := by
      rw [hv, ← FactTables.tupleProjectionTypedTableCosted_value_dense]
    apply pairEquality
    exact correspondence.projection p slot w

/-- Source success supplies both construction consistency and coordinate bounds
for the native/kernel lookup bridge. No separate bounded-output premise is
required. Positivity is needed only when constructing a `FiniteModel4`. -/
theorem compileModelSource_ok_lookups_agree
    (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled) :
    compiled.tables.sparseLookups source.worlds.size source.things.size =
      compiled.tables.denseLookups source.worlds.size source.things.size := by
  have correspondence := compileModelSource_ok_constructionInvariant source compiled success
  rw [← correspondence.worldCount, ← correspondence.thingCount, correspondence.tables]
  exact compiledLookups_agree compiled.ast (compileModelSource_ok_wellBounded source compiled success)


open private FactTables.buildInherenceClosures from LeanUfo.UFO.DSL.Compiler

/-!
## Stored closure correspondence

Cache reuse needs a proof about the arrays stored by the compiler, not just
the standalone Warshall algorithm. The world loop appends one result at each
ascending coordinate. Projecting its two accumulators recovers the independent
array maps below. These maps are proof specifications, not extra runtime passes.
-/

private theorem buildInherenceClosures_reachable (tables : FactTables) :
    (FactTables.buildInherenceClosures tables).reachable =
      ((List.range' 0 tables.denseWorldCount).map (fun world =>
        (Complexity.warshallState tables.denseThingCount
          (tables.inherenceEdgeAt world)).reachable.flatten.toArray)).toArray := by
  simp [FactTables.buildInherenceClosures]
  rw [← List.foldl_hom Prod.fst (g₂ := fun out world => out.push
    (Complexity.warshallState tables.denseThingCount
      (tables.inherenceEdgeAt world)).reachable.flatten.toArray) (fun _ _ => rfl)]
  simp

private theorem buildInherenceClosures_nextHop (tables : FactTables) :
    (FactTables.buildInherenceClosures tables).nextHop =
      ((List.range' 0 tables.denseWorldCount).map (fun world =>
        (Complexity.warshallState tables.denseThingCount
          (tables.inherenceEdgeAt world)).nextHop.flatten.toArray.map (Option.map Fin.val))).toArray := by
  simp [FactTables.buildInherenceClosures]
  rw [← List.foldl_hom Prod.snd (g₂ := fun out world => out.push
    ((Complexity.warshallState tables.denseThingCount
      (tables.inherenceEdgeAt world)).nextHop.flatten.toArray.map
        (Option.map Fin.val))) (fun _ _ => rfl)]
  simp

/-- Both stored arrays are the complete per-world results of Warshall over
these exact dense edges. Equality fixes their sizes, world order, reachability
cells, and deterministic first hops. It does not assert that arbitrary table
contents agree with source facts or with an independently supplied model. -/
def FactTables.InherenceCacheValid (tables : FactTables) : Prop :=
  tables.inherenceClosures =
    ((List.range' 0 tables.denseWorldCount).map (fun world =>
      (Complexity.warshallState tables.denseThingCount
        (tables.inherenceEdgeAt world)).reachable.flatten.toArray)).toArray ∧
  tables.inherenceNextHops =
    ((List.range' 0 tables.denseWorldCount).map (fun world =>
      (Complexity.warshallState tables.denseThingCount
        (tables.inherenceEdgeAt world)).nextHop.flatten.toArray.map (Option.map Fin.val))).toArray

/-- Dense materialization overwrites any incoming cache with results computed
from the populated relation cells. No invariant on the incoming cache is needed. -/
theorem FactTables.withDenseFacts_inherenceCacheValid
    (tables : FactTables) (W T : Nat) (facts : Array CompiledFact) :
    (tables.withDenseFacts W T facts).InherenceCacheValid := by
  let populated := facts.foldl FactTables.writeDenseFact
    (tables.initializeDense W T (projectionArityOfFacts facts))
  exact ⟨buildInherenceClosures_reachable populated, buildInherenceClosures_nextHop populated⟩

/-- Every explicit AST produces a cache for its actual dense relation cells.
Coordinate bounds are needed later to connect those cells to source semantics,
but not to prove which graph the closure builder executed. -/
theorem compileExplicitModelAST_inherenceCacheValid (ast : ModelAST) :
    (compileExplicitModelAST ast).InherenceCacheValid := by
  unfold compileExplicitModelAST
  exact FactTables.withDenseFacts_inherenceCacheValid _ _ _ _

theorem compileModelSource_ok_inherenceCacheValid
    (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled) :
    compiled.tables.InherenceCacheValid := by
  rw [(compileModelSource_ok_constructionInvariant source compiled success).tables]
  exact compileExplicitModelAST_inherenceCacheValid _

/-- An in-range world selects its own complete reachability array. -/
theorem FactTables.InherenceCacheValid.reachableAt
    (tables : FactTables) (valid : tables.InherenceCacheValid)
    (world : Fin tables.denseWorldCount) :
    tables.inherenceClosures[world.val]? = some
      (Complexity.warshallState tables.denseThingCount
        (tables.inherenceEdgeAt world.val)).reachable.flatten.toArray := by
  rw [valid.1]
  simp [world.isLt]

/-- First-hop storage follows the same world indexing as reachability. -/
theorem FactTables.InherenceCacheValid.nextHopAt
    (tables : FactTables) (valid : tables.InherenceCacheValid)
    (world : Fin tables.denseWorldCount) :
    tables.inherenceNextHops[world.val]? = some
      ((Complexity.warshallState tables.denseThingCount
        (tables.inherenceEdgeAt world.val)).nextHop.flatten.toArray.map (Option.map Fin.val)) := by
  rw [valid.2]
  simp [world.isLt]

/-- A valid cache answers the reachability recurrence for the exact dense
binary relation. The dimension equalities prevent interpreting a row with a
different width or selecting a world outside the compiled domain. -/
theorem FactTables.inherenceCache_lookup
    (tables : FactTables) (valid : tables.InherenceCacheValid)
    (W T : Nat) (worlds : tables.denseWorldCount = W) (things : tables.denseThingCount = T)
    (source target : Fin T) (world : Fin W) :
    tables.inherenceClosureTable source target world =
      Complexity.reachableVia (fun x y => tables.binaryTypedTableDense .inheresIn x y world)
        (List.finRange T) source target := by
  subst W
  subst T
  unfold FactTables.inherenceClosureTable
  rw [valid.reachableAt tables world]
  dsimp only
  rw [Complexity.flatten_toArray_getElem?_matrixIndex]
  simp only [Option.getD_some]
  exact Complexity.warshallState_reachable_get _ _ _ _

/-- Successful compilation fixes the dimensions used to index every cached
world row and relation cell. Consumers share this proof before reusing caches. -/
theorem compileModelSource_ok_tableDimensions
    (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled) :
    compiled.tables.denseWorldCount = source.worlds.size ∧
      compiled.tables.denseThingCount = source.things.size := by
  have invariant := compileModelSource_ok_constructionInvariant source compiled success
  rw [invariant.tables]
  simpa [compileExplicitModelAST] using And.intro invariant.worldCount invariant.thingCount


/-- Cache correctness must describe the same relation functions as the finite
model. Primitive lookup agreement alone does not constrain stored closures. -/
theorem FactTables.verifiedModel_cacheLookup (tables : FactTables)
    (W T : Nat) (hw : 0 < W) (ht : 0 < T)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (valid : tables.InherenceCacheValid)
    (worlds : tables.denseWorldCount = W) (things : tables.denseThingCount = T)
    (start target : Fin T) (world : Fin W) :
    let M := tables.toFiniteModel4Verified W T hw ht agreement
    (Complexity.closureLookupCosted tables.inherenceClosures T
      world.val start.val target.val).value =
        Complexity.reachableVia (fun x y => M.inheresIn x y world)
          (List.finRange T) start target := by
  have lookup := tables.inherenceCache_lookup valid W T worlds things start target world
  have edges := congrArg
    (fun lookups : FactTables.TableLookups W T =>
      fun x y => lookups.binary .inheresIn x y world) agreement.symm
  change (fun x y => tables.binaryTypedTableDense .inheresIn x y world) = _ at edges
  rw [edges] at lookup
  calc
    _ = tables.inherenceClosureTable start target world := by
      rw [← FactTables.inherenceClosureTableCosted_value]
      unfold FactTables.inherenceClosureTableCosted FactTables.momentOfClosureCosted
      rw [things]
    _ = _ := lookup

/-- Install the existing arrays with their correctness proof. No cells are
copied or recomputed. The extra operation constructs the model record with its
cache field; witness conversion retains the original constructor's cost.
Proof-carrying reuse follows the pass-correspondence discipline illustrated by
de Moura's RadixExperiment: a cached answer needs a proof about this model. -/
def FactTables.toFiniteModel4CachedCosted (tables : FactTables)
    (W T : Nat) (hw : 0 < W) (ht : 0 < T)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (valid : tables.InherenceCacheValid)
    (worlds : tables.denseWorldCount = W) (things : tables.denseThingCount = T) :
    Complexity.Costed FiniteModel4 :=
  let built := tables.toFiniteModel4VerifiedCosted W T hw ht agreement
  Complexity.Costed.charge built.cost <| Complexity.Costed.tick
    { built.value with inherenceCache := some ⟨tables.inherenceClosures,
        tables.verifiedModel_cacheLookup W T hw ht agreement valid worlds things⟩ } 1

def FactTables.toFiniteModel4Cached (tables : FactTables)
    (W T : Nat) (hw : 0 < W) (ht : 0 < T)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (valid : tables.InherenceCacheValid)
    (worlds : tables.denseWorldCount = W) (things : tables.denseThingCount = T) : FiniteModel4 :=
  (tables.toFiniteModel4CachedCosted W T hw ht agreement valid worlds things).value

theorem FactTables.toFiniteModel4CachedCosted_cost (tables : FactTables)
    (W T : Nat) (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    (tables.toFiniteModel4CachedCosted W T hw ht agreement valid worlds things).cost =
      (tables.toFiniteModel4VerifiedCosted W T hw ht agreement).cost + 1 := rfl

theorem FactTables.toFiniteModel4CachedCosted_cost_le (tables : FactTables)
    (W T : Nat) (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    (tables.toFiniteModel4CachedCosted W T hw ht agreement valid worlds things).cost ≤
      4 + W * (7 * (tables.productFamilies.toList.map (fun family =>
        family.dimensionThings.size + family.typeThings.size)).sum +
        20 * tables.productFamilies.size) + 2 * tables.productFamilies.size := by
  rw [FactTables.toFiniteModel4CachedCosted_cost]
  have h := FactTables.toFiniteModel4VerifiedCosted_cost_le W T hw ht tables agreement
  omega

/-- The cache changes execution, not the UFO signature or its interpretation. -/
theorem FactTables.toFiniteModel4Cached_signature (tables : FactTables)
    (W T : Nat) (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    (tables.toFiniteModel4Cached W T hw ht agreement valid worlds things).toUFOSignature4 =
      (tables.toFiniteModel4Verified W T hw ht agreement).toUFOSignature4 := rfl

/-- Cache installation preserves the witness registry itself, including its
order and duplicate records. These witnesses are not fields of the interpreted
UFO signature, so signature equality alone does not supply this guarantee. -/
theorem FactTables.toFiniteModel4Cached_productFamilies (tables : FactTables)
    (W T : Nat) (hw : 0 < W) (ht : 0 < T) (agreement valid worlds things) :
    (tables.toFiniteModel4Cached W T hw ht agreement valid worlds things).productFamilies =
      (tables.toFiniteModel4Verified W T hw ht agreement).productFamilies := rfl

/-!
## Source-to-model correspondence

These readbacks use the same cached constructor as generated declarations.
The cache and family proofs preserve their respective stored data without
executing extra conversion or graph passes.
-/

/-- The production finite-model field has the same exact family/world
readback. Positivity is a model-construction premise, separate from source
success. Source success supplies both family validity and lookup agreement. -/
theorem compileModelSource_ok_modelFamilies_readback
    (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled)
    (hw : 0 < source.worlds.size) (ht : 0 < source.things.size) :
    ((compiled.tables.toFiniteModel4Cached source.worlds.size source.things.size hw ht
      (compileModelSource_ok_lookups_agree source compiled success)
      (compileModelSource_ok_inherenceCacheValid source compiled success)
      (compileModelSource_ok_tableDimensions source compiled success).1
      (compileModelSource_ok_tableDimensions source compiled success).2).productFamilies.map
        (fun witness => (witness.toSpec, witness.world.val))) =
      (compiled.productFamilies.toList.flatMap (fun family =>
        (List.range source.worlds.size).map (fun world => (family, world)))).toArray := by
  dsimp only [FactTables.toFiniteModel4Cached, FactTables.toFiniteModel4CachedCosted,
    Complexity.Costed.charge, Complexity.Costed.tick]
  exact compileModelSource_ok_familyWitnesses_readback source compiled success

/-- A resolved family occurs in the produced registry exactly when a finite
witness reads back to it at the selected world. This follows from the ordered
family/world readback, so duplicate records require no uniqueness assumption. -/
theorem compileModelSource_ok_modelFamilies_mem_iff
    (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled)
    (hw : 0 < source.worlds.size) (ht : 0 < source.things.size)
    (family : ProductFamilySpec) (w : Fin source.worlds.size) :
    let M := compiled.tables.toFiniteModel4Cached source.worlds.size source.things.size hw ht
      (compileModelSource_ok_lookups_agree source compiled success)
      (compileModelSource_ok_inherenceCacheValid source compiled success)
      (compileModelSource_ok_tableDimensions source compiled success).1
      (compileModelSource_ok_tableDimensions source compiled success).2
    (∃ pf ∈ M.productFamilies, pf.toSpec = family ∧ pf.world = w) ↔
      family ∈ compiled.tables.productFamilies := by
  have h := congrArg (fun entries : Array (ProductFamilySpec × Nat) =>
    (family, w.val) ∈ entries)
    (compileModelSource_ok_modelFamilies_readback source compiled success hw ht)
  rw [compileModelSource_ok_tableFamilies source compiled success]
  simp [Array.mem_map, List.mem_flatMap, w.isLt] at h
  constructor
  · rintro ⟨pf, member, spec, world⟩
    exact h.mp ⟨pf, member, spec, congrArg Fin.val world⟩
  · intro member
    obtain ⟨pf, member, spec, world⟩ := h.mpr member
    exact ⟨pf, member, spec, Fin.ext world⟩

/-- Successful source compilation supplies both cache validity and primitive
lookup agreement. Thus the stored array answers the reachability recurrence
of the actual production model, without a separately supplied graph or cache. -/
theorem compileModelSource_ok_modelClosure_lookup
    (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled)
    (hw : 0 < source.worlds.size) (ht : 0 < source.things.size)
    (start target : Fin source.things.size) (world : Fin source.worlds.size) :
    let M := compiled.tables.toFiniteModel4Cached source.worlds.size source.things.size hw ht
      (compileModelSource_ok_lookups_agree source compiled success)
      (compileModelSource_ok_inherenceCacheValid source compiled success)
      (compileModelSource_ok_tableDimensions source compiled success).1
      (compileModelSource_ok_tableDimensions source compiled success).2
    compiled.tables.inherenceClosureTable start target world =
      Complexity.reachableVia (fun x y => M.inheresIn x y world)
        (List.finRange source.things.size) start target := by
  dsimp only [FactTables.toFiniteModel4Cached, FactTables.toFiniteModel4CachedCosted,
    Complexity.Costed.charge, Complexity.Costed.tick]
  obtain ⟨worlds, things⟩ := compileModelSource_ok_tableDimensions source compiled success
  have lookup := compiled.tables.inherenceCache_lookup
    (compileModelSource_ok_inherenceCacheValid source compiled success)
    _ _ worlds things start target world
  have edges := congrArg
    (fun lookups : FactTables.TableLookups source.worlds.size source.things.size =>
      fun x y => lookups.binary .inheresIn x y world)
    (compileModelSource_ok_lookups_agree source compiled success).symm
  change (fun x y => compiled.tables.binaryTypedTableDense .inheresIn x y world) = _ at edges
  rw [edges] at lookup
  exact lookup

theorem compileExplicitModelAST_tableDimensions (ast : ModelAST) :
    (compileExplicitModelAST ast).denseWorldCount = ast.worldCount ∧
      (compileExplicitModelAST ast).denseThingCount = ast.thingCount := by
  simp [compileExplicitModelAST]

/-- Bounded explicit facts supply both lookup agreement and a proved cache. -/
def compileVerifiedModel (ast : ModelAST)
    (worldPositive : 0 < ast.worldCount) (thingPositive : 0 < ast.thingCount)
    (bounded : explicitModelWellBounded ast) : FiniteModel4 :=
  (compileExplicitModelAST ast).toFiniteModel4Cached
    ast.worldCount ast.thingCount worldPositive thingPositive (compiledLookups_agree ast bounded)
    (compileExplicitModelAST_inherenceCacheValid ast)
    (compileExplicitModelAST_tableDimensions ast).1 (compileExplicitModelAST_tableDimensions ast).2

theorem compileVerifiedModel_signature (ast : ModelAST)
    (worldPositive : 0 < ast.worldCount) (thingPositive : 0 < ast.thingCount)
    (bounded : explicitModelWellBounded ast) :
    (compileVerifiedModel ast worldPositive thingPositive bounded).toUFOSignature4 =
      (compileExplicitModel ast worldPositive thingPositive).toUFOSignature4 := rfl

/-- Count the same two stages as `compileVerifiedModel`: build the explicit
tables, then construct the cached finite model from those returned tables.
Their accumulated costs stay separate from the proofs, which are erased.
This accounts for one reconstruction; it does not assert that native runtime
sharing causes every later checker call to reconstruct the model. -/
def compileVerifiedModelCosted (ast : ModelAST)
    (worldPositive : 0 < ast.worldCount) (thingPositive : 0 < ast.thingCount)
    (bounded : explicitModelWellBounded ast) : Complexity.Costed FiniteModel4 :=
  let built := compileExplicitModelASTCosted ast
  have same : built.value = compileExplicitModelAST ast := compileExplicitModelASTCosted_value ast
  have agreement : built.value.sparseLookups ast.worldCount ast.thingCount =
      built.value.denseLookups ast.worldCount ast.thingCount := by
    rw [same]
    exact compiledLookups_agree ast bounded
  have valid : built.value.InherenceCacheValid := by
    rw [same]
    exact compileExplicitModelAST_inherenceCacheValid ast
  have worlds : built.value.denseWorldCount = ast.worldCount := by
    rw [same]
    exact (compileExplicitModelAST_tableDimensions ast).1
  have things : built.value.denseThingCount = ast.thingCount := by
    rw [same]
    exact (compileExplicitModelAST_tableDimensions ast).2
  Complexity.Costed.charge built.cost <|
    built.value.toFiniteModel4CachedCosted ast.worldCount ast.thingCount
      worldPositive thingPositive agreement valid worlds things

/-- The counted constructor uses the production table builder's correspondence
theorem, then the production finite-model constructor's erasure. -/
theorem compileVerifiedModelCosted_value (ast : ModelAST)
    (worldPositive : 0 < ast.worldCount) (thingPositive : 0 < ast.thingCount)
    (bounded : explicitModelWellBounded ast) :
    (compileVerifiedModelCosted ast worldPositive thingPositive bounded).value =
      compileVerifiedModel ast worldPositive thingPositive bounded := by
  simp only [compileVerifiedModelCosted, Complexity.Costed.charge_value,
    compileExplicitModelASTCosted_value, compileVerifiedModel, FactTables.toFiniteModel4Cached]

/-- The cost comes from the executed table and model constructors, not from
the later source-size bound. Proof arguments do not contribute operations. -/
theorem compileVerifiedModelCosted_cost (ast : ModelAST)
    (worldPositive : 0 < ast.worldCount) (thingPositive : 0 < ast.thingCount)
    (bounded : explicitModelWellBounded ast) :
    (compileVerifiedModelCosted ast worldPositive thingPositive bounded).cost =
      (compileExplicitModelASTCosted ast).cost +
        ((compileExplicitModelAST ast).toFiniteModel4CachedCosted
          ast.worldCount ast.thingCount worldPositive thingPositive
          (compiledLookups_agree ast bounded) (compileExplicitModelAST_inherenceCacheValid ast)
          (compileExplicitModelAST_tableDimensions ast).1
          (compileExplicitModelAST_tableDimensions ast).2).cost := by
  simp only [compileVerifiedModelCosted, Complexity.Costed.charge_cost,
    compileExplicitModelASTCosted_value]

end LeanUfo.UFO.DSL
