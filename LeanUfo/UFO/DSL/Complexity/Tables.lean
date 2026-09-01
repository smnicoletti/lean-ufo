import LeanUfo.UFO.DSL.Complexity.CostModel
import LeanUfo.UFO.DSL.Compiler

/-!
# Deterministic indexed tables and footprints

The representation is an explicit flat array.  Consequently, the unit-cost
theorem assumes Lean array indexing as one primitive and charges initialization
of every cell.  It makes no constant-time claim about `HashMap` or strings.

As engineering precedent, RadixExperiment proves its executable interpreter
against relational semantics and proves each optimization separately.  We use
the same proof shape here: table construction/lookup are executable definitions,
then correspondence theorems connect them to fact membership.  RadixExperiment
is precedent for proof organization, not a source for our complexity theorem.
-/

namespace LeanUfo.UFO.DSL.Complexity

structure FlatBoolTable where
  fieldCount : Nat
  coordinateCount : Nat
  cells : Array Bool
  cells_size : cells.size = fieldCount * coordinateCount
deriving Repr

namespace FlatBoolTable

def empty (fieldCount coordinateCount : Nat) : FlatBoolTable :=
  { fieldCount, coordinateCount
    cells := Array.replicate (fieldCount * coordinateCount) false
    cells_size := by simp }

def index (table : FlatBoolTable) (field coordinate : Nat) : Nat :=
  field * table.coordinateCount + coordinate

/-- One charged bounds check plus one charged array access. -/
def getCosted (table : FlatBoolTable) (field coordinate : Nat) : Costed Bool :=
  .tick (table.cells[table.index field coordinate]?.getD false) 2

def get (table : FlatBoolTable) (field coordinate : Nat) : Bool :=
  (table.getCosted field coordinate).value

/-- One bounds check, index calculation, and deterministic array write. -/
def setCosted (table : FlatBoolTable) (field coordinate : Nat) : Costed FlatBoolTable :=
  if hField : field < table.fieldCount then
    if hCoordinate : coordinate < table.coordinateCount then
      let idx := table.index field coordinate
      let cells := table.cells.set! idx true
      .tick
        { table with cells := cells, cells_size := by simp [cells, table.cells_size] }
        3
    else .tick table 1
  else .tick table 1

def set (table : FlatBoolTable) (field coordinate : Nat) : FlatBoolTable :=
  (table.setCosted field coordinate).value

@[simp] theorem getCosted_value (table : FlatBoolTable) (field coordinate : Nat) :
    (table.getCosted field coordinate).value = table.get field coordinate := rfl

@[simp] theorem getCosted_cost (table : FlatBoolTable) (field coordinate : Nat) :
    (table.getCosted field coordinate).cost = 2 := rfl

end FlatBoolTable

/-!
## Dense materialization correspondence core

The production compiler writes `true` at flat coordinates with `Array.set!`.
The lemma below proves the reusable array-level fact behind unary, binary, and
ternary table correspondence: after a stream of in-bounds writes, lookup is
true exactly when the queried coordinate occurs in that stream.  This is the
pass-correspondence proof shape used in RadixExperiment; it concerns our
concrete array computation rather than treating lookup correctness as an
assumption.
-/

def materializeBoolIndices (cellCount : Nat) (indices : Array Nat) : Array Bool :=
  indices.foldl (fun cells index => cells.set! index true)
    (Array.replicate cellCount false)

def indexOccurs (query : Nat) (indices : Array Nat) : Bool :=
  indices.any (fun index => index == query)

private theorem foldl_setTrue_lookup
    (indices : List Nat) (cells : Array Bool) (query : Nat)
    (hQuery : query < cells.size) :
    (indices.foldl (fun cells index => cells.set! index true) cells)[query]?.getD false =
      (cells[query]?.getD false || indices.any (fun index => index == query)) := by
  induction indices generalizing cells with
  | nil => simp
  | cons index indices ih =>
      simp only [List.foldl_cons, List.any_cons]
      rw [ih]
      · rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
        by_cases hEq : index = query
        · subst index
          simp [hQuery]
        · have hBool : (index == query) = false :=
            beq_eq_false_iff_ne.mpr hEq
          simp [hEq, hBool]
      · simpa [Array.set!_eq_setIfInBounds] using hQuery

/-- Lookup in a freshly materialized Boolean table is exactly coordinate
membership in the write stream. Duplicate writes are therefore idempotent. -/
theorem materializeBoolIndices_lookup_iff
    (cellCount query : Nat) (indices : Array Nat) (hQuery : query < cellCount) :
    (materializeBoolIndices cellCount indices)[query]?.getD false = true ↔
      indexOccurs query indices = true := by
  unfold materializeBoolIndices indexOccurs
  rw [← Array.foldl_toList]
  rw [foldl_setTrue_lookup indices.toList (Array.replicate cellCount false) query]
  · rw [Array.any_toList]
    simp [hQuery]
  · simpa using hQuery

example :
    (materializeBoolIndices 4 #[1, 1, 3])[1]?.getD false = true := by
  native_decide

example :
    (materializeBoolIndices 4 #[1, 1, 3])[2]?.getD false = false := by
  native_decide

namespace Production

/-- Every coordinate in a resolved fact lies inside the explicit model. -/
def factWellBounded (worldCount thingCount : Nat) :
    CompiledFact → Prop
  | .unary _ thing world => thing < thingCount ∧ world < worldCount
  | .binary _ left right world =>
      left < thingCount ∧ right < thingCount ∧ world < worldCount
  | .ternary _ first second third world =>
      first < thingCount ∧ second < thingCount ∧ third < thingCount ∧
        world < worldCount
  | .tupleProjection tuple _index result world =>
      tuple < thingCount ∧ result < thingCount ∧ world < worldCount
  | .derived _ => True

/-- Equality of a row-major index recovers its row and bounded column. -/
private theorem rowMajor_eq_iff
    {width leftRow rightRow leftColumn rightColumn : Nat}
    (hWidth : 0 < width) (hLeft : leftColumn < width)
    (hRight : rightColumn < width) :
    leftRow * width + leftColumn = rightRow * width + rightColumn ↔
      leftRow = rightRow ∧ leftColumn = rightColumn := by
  constructor
  · intro h
    have hColumn : leftColumn = rightColumn := by
      have hMod := congrArg (fun value => value % width) h
      simpa [Nat.add_mod, Nat.mod_eq_of_lt hLeft,
        Nat.mod_eq_of_lt hRight] using hMod
    subst rightColumn
    exact ⟨Nat.eq_of_mul_eq_mul_right hWidth (Nat.add_right_cancel h), rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

private theorem rowMajor_lt (row column rowCount width : Nat)
    (hRow : row < rowCount) (hColumn : column < width) :
    row * width + column < rowCount * width := by
  have hWithin := Nat.add_lt_add_left hColumn (row * width)
  have hNext : row * width + width ≤ rowCount * width := by
    simpa [Nat.succ_mul] using
      Nat.mul_le_mul_right width (Nat.succ_le_iff.mpr hRow)
  exact lt_of_lt_of_le hWithin hNext

private theorem binaryCoordinate_lt
    {thingCount worldCount left right world : Nat}
    (hLeft : left < thingCount) (hRight : right < thingCount)
    (hWorld : world < worldCount) :
    binaryCoordinate thingCount worldCount left right world <
      thingCount * thingCount * worldCount := by
  have hPair := rowMajor_lt left right thingCount thingCount hLeft hRight
  simpa [binaryCoordinate, Nat.mul_assoc] using
    rowMajor_lt (left * thingCount + right) world
      (thingCount * thingCount) worldCount hPair hWorld

private theorem ternaryCoordinate_lt
    {thingCount worldCount first second third world : Nat}
    (hFirst : first < thingCount) (hSecond : second < thingCount)
    (hThird : third < thingCount) (hWorld : world < worldCount) :
    ternaryCoordinate thingCount worldCount first second third world <
      thingCount ^ 3 * worldCount := by
  have hFirstSecond :=
    rowMajor_lt first second thingCount thingCount hFirst hSecond
  have hTriple := rowMajor_lt (first * thingCount + second) third
    (thingCount * thingCount) thingCount hFirstSecond hThird
  simpa [ternaryCoordinate, Nat.pow_succ, Nat.mul_assoc] using
    rowMajor_lt ((first * thingCount + second) * thingCount + third) world
      (thingCount * thingCount * thingCount) worldCount hTriple hWorld

/-- Logical membership predicate shared by sparse and dense unary lookups. -/
def matchesUnaryFact (field : UnaryField) (thing world : Nat) :
    CompiledFact → Bool
  | .unary candidateField candidateThing candidateWorld =>
      field.toTableField == candidateField.toTableField &&
        thing == candidateThing && world == candidateWorld
  | _ => false

private theorem foldl_compileExplicitFact_unaryLookup_list
    (facts : List CompiledFact) (tables : FactTables)
    (field : UnaryField) (thing world : Nat) :
    (facts.foldl compileExplicitFact tables).unaryLookup
        field.toTableField thing world =
      (tables.unaryLookup field.toTableField thing world ||
        facts.any (matchesUnaryFact field thing world)) := by
  induction facts generalizing tables with
  | nil => simp
  | cons fact facts ih =>
      simp only [List.foldl_cons, List.any_cons, ih]
      cases fact <;>
        simp [compileExplicitFact, addUnary, addBinary, addTernary,
          addTupleProjection, addDerivedProp, matchesUnaryFact, Bool.or_assoc,
          Bool.or_left_comm, Bool.or_comm]

/-- Sparse unary lookup after the explicit compiler fold is exactly fact-stream
membership. The initial lookup remains visible for reuse by nonempty tables. -/
theorem foldl_compileExplicitFact_unaryLookup
    (facts : Array CompiledFact) (tables : FactTables)
    (field : UnaryField) (thing world : Nat) :
    (facts.foldl compileExplicitFact tables).unaryLookup
        field.toTableField thing world =
      (tables.unaryLookup field.toTableField thing world ||
        facts.any (matchesUnaryFact field thing world)) := by
  rw [← Array.foldl_toList, ← Array.any_toList]
  exact foldl_compileExplicitFact_unaryLookup_list
    facts.toList tables field thing world

def matchesBinaryFact (field : BinaryField) (left right world : Nat) :
    CompiledFact → Bool
  | .binary candidateField candidateLeft candidateRight candidateWorld =>
      field.toTableField == candidateField.toTableField &&
        left == candidateLeft && right == candidateRight && world == candidateWorld
  | _ => false

private theorem foldl_compileExplicitFact_binaryLookup_list
    (facts : List CompiledFact) (tables : FactTables)
    (field : BinaryField) (left right world : Nat) :
    (facts.foldl compileExplicitFact tables).binaryLookup
        field.toTableField left right world =
      (tables.binaryLookup field.toTableField left right world ||
        facts.any (matchesBinaryFact field left right world)) := by
  induction facts generalizing tables with
  | nil => simp
  | cons fact facts ih =>
      simp only [List.foldl_cons, List.any_cons, ih]
      cases fact <;>
        simp [compileExplicitFact, addUnary, addBinary, addTernary,
          addTupleProjection, addDerivedProp, matchesBinaryFact, Bool.or_assoc,
          Bool.or_left_comm, Bool.or_comm]

theorem foldl_compileExplicitFact_binaryLookup
    (facts : Array CompiledFact) (tables : FactTables)
    (field : BinaryField) (left right world : Nat) :
    (facts.foldl compileExplicitFact tables).binaryLookup
        field.toTableField left right world =
      (tables.binaryLookup field.toTableField left right world ||
        facts.any (matchesBinaryFact field left right world)) := by
  rw [← Array.foldl_toList, ← Array.any_toList]
  exact foldl_compileExplicitFact_binaryLookup_list
    facts.toList tables field left right world

def matchesTernaryFact (field : TernaryField)
    (first second third world : Nat) : CompiledFact → Bool
  | .ternary candidateField a b c candidateWorld =>
      field.toTableField == candidateField.toTableField && first == a &&
        second == b && third == c && world == candidateWorld
  | _ => false

private theorem foldl_compileExplicitFact_ternaryLookup_list
    (facts : List CompiledFact) (tables : FactTables) (field : TernaryField)
    (first second third world : Nat) :
    (facts.foldl compileExplicitFact tables).ternaryLookup
        field.toTableField first second third world =
      (tables.ternaryLookup field.toTableField first second third world ||
        facts.any (matchesTernaryFact field first second third world)) := by
  induction facts generalizing tables with
  | nil => simp
  | cons fact facts ih =>
      simp only [List.foldl_cons, List.any_cons, ih]
      cases fact <;>
        simp [compileExplicitFact, addUnary, addBinary, addTernary,
          addTupleProjection, addDerivedProp, matchesTernaryFact,
          Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

theorem foldl_compileExplicitFact_ternaryLookup
    (facts : Array CompiledFact) (tables : FactTables) (field : TernaryField)
    (first second third world : Nat) :
    (facts.foldl compileExplicitFact tables).ternaryLookup
        field.toTableField first second third world =
      (tables.ternaryLookup field.toTableField first second third world ||
        facts.any (matchesTernaryFact field first second third world)) := by
  rw [← Array.foldl_toList, ← Array.any_toList]
  exact foldl_compileExplicitFact_ternaryLookup_list facts.toList tables
    field first second third world

def applyProjectionResult (tuple slot world : Nat)
    (current : Option Nat) : CompiledFact → Option Nat
  | .tupleProjection candidateTuple candidateSlot result candidateWorld =>
      if tuple == candidateTuple && slot == candidateSlot && world == candidateWorld then
        some result
      else current
  | _ => current

private theorem foldl_compileExplicitFact_projectionResult_list
    (facts : List CompiledFact) (tables : FactTables)
    (tuple slot world : Nat) :
    (facts.foldl compileExplicitFact tables).tupleProjectionResult? tuple slot world =
      facts.foldl (applyProjectionResult tuple slot world)
        (tables.tupleProjectionResult? tuple slot world) := by
  induction facts generalizing tables with
  | nil => rfl
  | cons fact facts ih =>
      simp only [List.foldl_cons, ih]
      cases fact <;>
        simp [compileExplicitFact, addUnary, addBinary, addTernary,
          addTupleProjection, addDerivedProp, applyProjectionResult]

theorem foldl_compileExplicitFact_projectionResult
    (facts : Array CompiledFact) (tables : FactTables)
    (tuple slot world : Nat) :
    (facts.foldl compileExplicitFact tables).tupleProjectionResult? tuple slot world =
      facts.foldl (applyProjectionResult tuple slot world)
        (tables.tupleProjectionResult? tuple slot world) := by
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  exact foldl_compileExplicitFact_projectionResult_list
    facts.toList tables tuple slot world

private theorem foldl_applyProjectionResult_none_of_arity_le_list
    (facts : List CompiledFact) (tuple slot world arity : Nat)
    (hArity : ∀ fact ∈ facts, fact.projectionArity ≤ arity)
    (hSlot : arity ≤ slot) :
    facts.foldl (applyProjectionResult tuple slot world) none = none := by
  induction facts with
  | nil => rfl
  | cons fact facts ih =>
      simp only [List.foldl_cons]
      have hHead := hArity fact (by simp)
      have hTail : ∀ candidate ∈ facts, candidate.projectionArity ≤ arity := by
        intro candidate hCandidate
        exact hArity candidate (by simp [hCandidate])
      cases fact with
      | tupleProjection candidateTuple candidateSlot result candidateWorld =>
          have hNe : slot ≠ candidateSlot := by
            intro hEq
            subst candidateSlot
            simp [CompiledFact.projectionArity] at hHead
            omega
          simp [applyProjectionResult, hNe, ih hTail]
      | unary | binary | ternary | derived =>
          simpa [applyProjectionResult] using ih hTail

theorem foldl_applyProjectionResult_none_of_arity_le
    (facts : Array CompiledFact) (tuple slot world : Nat)
    (hSlot : projectionArityOfFacts facts ≤ slot) :
    facts.foldl (applyProjectionResult tuple slot world) none = none := by
  rw [← Array.foldl_toList]
  apply foldl_applyProjectionResult_none_of_arity_le_list facts.toList tuple slot world
    (projectionArityOfFacts facts)
  · intro fact hFact
    exact fact.projectionArity_le_of_mem facts (by simpa using hFact)
  · exact hSlot

/-- Flat unary coordinate written by one production compiler fact. -/
def unaryWriteIndex? (tables : FactTables) : CompiledFact → Option Nat
  | .unary field thing world =>
      some (field.index * (tables.denseThingCount * tables.denseWorldCount) +
        (thing * tables.denseWorldCount + world))
  | _ => none

private theorem unaryWriteIndex?_eq_matchesUnaryFact
    (worldCount thingCount : Nat) (facts : Array CompiledFact)
    (tables : FactTables)
    (field : UnaryField) (x : Fin thingCount) (w : Fin worldCount)
    (fact : CompiledFact) (hFact : factWellBounded worldCount thingCount fact) :
    (unaryWriteIndex?
        (tables.initializeDense worldCount thingCount
          (projectionArityOfFacts facts)) fact ==
      some (field.index * (thingCount * worldCount) +
        unaryCoordinate x.val worldCount w.val)) =
      matchesUnaryFact field x.val w.val fact := by
  cases fact with
  | binary | ternary | tupleProjection | derived =>
      simp [unaryWriteIndex?, matchesUnaryFact]
  | unary candidateField candidateThing candidateWorld =>
      rcases hFact with ⟨hCandidateThing, hCandidateWorld⟩
      have hWorldCount : 0 < worldCount :=
        Nat.zero_lt_of_lt w.isLt
      have hThingCount : 0 < thingCount :=
        Nat.zero_lt_of_lt x.isLt
      have queryCoordinateBound :
          unaryCoordinate x.val worldCount w.val < thingCount * worldCount := by
        have hWithin := Nat.add_lt_add_left w.isLt (x.val * worldCount)
        have hNext : x.val * worldCount + worldCount ≤
            thingCount * worldCount := by
          simpa [Nat.succ_mul] using
            Nat.mul_le_mul_right worldCount (Nat.succ_le_iff.mpr x.isLt)
        exact lt_of_lt_of_le hWithin hNext
      have candidateCoordinateBound :
          unaryCoordinate candidateThing worldCount candidateWorld <
            thingCount * worldCount := by
        have hWithin :=
          Nat.add_lt_add_left hCandidateWorld (candidateThing * worldCount)
        have hNext : candidateThing * worldCount + worldCount ≤
            thingCount * worldCount := by
          simpa [Nat.succ_mul] using Nat.mul_le_mul_right worldCount
            (Nat.succ_le_iff.mpr hCandidateThing)
        exact lt_of_lt_of_le hWithin hNext
      rw [Bool.eq_iff_iff]
      simp only [unaryWriteIndex?, FactTables.initializeDense,
        Option.some.injEq, beq_iff_eq, matchesUnaryFact, Bool.and_eq_true,
        unaryCoordinate]
      constructor
      · intro hIndex
        have separated := (rowMajor_eq_iff
          (Nat.mul_pos hThingCount hWorldCount)
          candidateCoordinateBound queryCoordinateBound).mp hIndex
        rcases separated with ⟨hFieldIndex, hCoordinate⟩
        have hField : candidateField = field :=
          UnaryField.index_injective hFieldIndex
        have hPair := (rowMajor_eq_iff hWorldCount
          hCandidateWorld w.isLt).mp hCoordinate
        rcases hPair with ⟨hThing, hWorld⟩
        exact ⟨⟨congrArg UnaryField.toTableField hField.symm,
          hThing.symm⟩, hWorld.symm⟩
      · rintro ⟨⟨hFieldName, hThing⟩, hWorld⟩
        have hField : field = candidateField :=
          UnaryField.toTableField_injective hFieldName
        subst candidateField
        subst candidateThing
        subst candidateWorld
        rfl

/-- One production dense write changes unary lookup exactly at the unary
coordinate encoded by that fact. Other fact arities are isolated. -/
theorem writeDenseFact_unary_lookup
    (tables : FactTables) (fact : CompiledFact) (query : Nat)
    (hQuery : query < tables.unaryCells.size) :
    (tables.writeDenseFact fact).unaryCells[query]?.getD false =
      (tables.unaryCells[query]?.getD false ||
        (unaryWriteIndex? tables fact == some query)) := by
  cases fact with
  | unary field thing world =>
      simp only [FactTables.writeDenseFact, unaryWriteIndex?]
      simp only [unaryCoordinate]
      rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
      by_cases hEq :
          field.index * (tables.denseThingCount * tables.denseWorldCount) +
            (thing * tables.denseWorldCount + world) = query
      · simp [hEq, hQuery]
      · have hBool :
            (field.index * (tables.denseThingCount * tables.denseWorldCount) +
              (thing * tables.denseWorldCount + world) == query) = false :=
          beq_eq_false_iff_ne.mpr hEq
        simp [hEq, hBool]
  | binary | ternary | tupleProjection | derived =>
      simp [FactTables.writeDenseFact, unaryWriteIndex?]

private theorem writeDenseFact_unaryCells_size
    (tables : FactTables) (fact : CompiledFact) :
    (tables.writeDenseFact fact).unaryCells.size = tables.unaryCells.size := by
  cases fact <;>
    simp [FactTables.writeDenseFact, Array.set!_eq_setIfInBounds]

private theorem unaryWriteIndex?_writeDenseFact
    (tables : FactTables) (written candidate : CompiledFact) :
    unaryWriteIndex? (tables.writeDenseFact written) candidate =
      unaryWriteIndex? tables candidate := by
  cases written <;> cases candidate <;>
    simp [FactTables.writeDenseFact, unaryWriteIndex?]

private theorem foldl_writeDenseFact_unary_lookup_list
    (facts : List CompiledFact) (tables : FactTables) (query : Nat)
    (hQuery : query < tables.unaryCells.size) :
    (facts.foldl FactTables.writeDenseFact tables).unaryCells[query]?.getD false =
      (tables.unaryCells[query]?.getD false ||
        facts.any (fun fact => unaryWriteIndex? tables fact == some query)) := by
  induction facts generalizing tables with
  | nil => simp
  | cons fact facts ih =>
      simp only [List.foldl_cons, List.any_cons]
      have hUpdated : query < (tables.writeDenseFact fact).unaryCells.size := by
        simpa [writeDenseFact_unaryCells_size] using hQuery
      rw [ih (tables.writeDenseFact fact) hUpdated]
      rw [writeDenseFact_unary_lookup tables fact query hQuery]
      simp only [unaryWriteIndex?_writeDenseFact]
      simp [Bool.or_assoc]

/-- Unary lookup after the production compiler's actual fact fold is the
initial cell or membership of that exact encoded coordinate in the fact stream.
This is implementation correspondence, not a theorem about a parallel model. -/
theorem foldl_writeDenseFact_unary_lookup
    (facts : Array CompiledFact) (tables : FactTables) (query : Nat)
    (hQuery : query < tables.unaryCells.size) :
    (facts.foldl FactTables.writeDenseFact tables).unaryCells[query]?.getD false =
      (tables.unaryCells[query]?.getD false ||
        facts.any (fun fact => unaryWriteIndex? tables fact == some query)) := by
  rw [← Array.foldl_toList, ← Array.any_toList]
  exact foldl_writeDenseFact_unary_lookup_list facts.toList tables query hQuery

/-- Flat binary coordinate written by one production compiler fact. -/
def binaryWriteIndex? (tables : FactTables) : CompiledFact → Option Nat
  | .binary field left right world =>
      some (field.index *
          (tables.denseThingCount * tables.denseThingCount * tables.denseWorldCount) +
        ((left * tables.denseThingCount + right) * tables.denseWorldCount + world))
  | _ => none

private theorem binaryWriteIndex?_eq_matchesBinaryFact
    (worldCount thingCount : Nat) (facts : Array CompiledFact)
    (tables : FactTables) (field : BinaryField)
    (x y : Fin thingCount) (w : Fin worldCount)
    (fact : CompiledFact) (hFact : factWellBounded worldCount thingCount fact) :
    (binaryWriteIndex?
        (tables.initializeDense worldCount thingCount
          (projectionArityOfFacts facts)) fact ==
      some (field.index * (thingCount * thingCount * worldCount) +
        binaryCoordinate thingCount worldCount x.val y.val w.val)) =
      matchesBinaryFact field x.val y.val w.val fact := by
  cases fact with
  | unary | ternary | tupleProjection | derived =>
      simp [binaryWriteIndex?, matchesBinaryFact]
  | binary candidateField candidateLeft candidateRight candidateWorld =>
      rcases hFact with ⟨hLeft, hRight, hWorld⟩
      have hWorldCount : 0 < worldCount := Nat.zero_lt_of_lt w.isLt
      have hThingCount : 0 < thingCount := Nat.zero_lt_of_lt x.isLt
      have hQuery := binaryCoordinate_lt x.isLt y.isLt w.isLt
      have hCandidate := binaryCoordinate_lt hLeft hRight hWorld
      rw [Bool.eq_iff_iff]
      simp only [binaryWriteIndex?, FactTables.initializeDense,
        Option.some.injEq, beq_iff_eq, matchesBinaryFact, Bool.and_eq_true]
      constructor
      · intro hIndex
        have separated := (rowMajor_eq_iff
          (Nat.mul_pos (Nat.mul_pos hThingCount hThingCount) hWorldCount)
          hCandidate hQuery).mp hIndex
        rcases separated with ⟨hFieldIndex, hCoordinate⟩
        have hField : candidateField = field :=
          BinaryField.index_injective hFieldIndex
        have hPairWorld := (rowMajor_eq_iff hWorldCount hWorld w.isLt).mp
          (by simpa [binaryCoordinate] using hCoordinate)
        rcases hPairWorld with ⟨hPair, hWorldEq⟩
        have hLeftRight := (rowMajor_eq_iff hThingCount hRight y.isLt).mp hPair
        rcases hLeftRight with ⟨hLeftEq, hRightEq⟩
        exact ⟨⟨⟨congrArg BinaryField.toTableField hField.symm,
          hLeftEq.symm⟩, hRightEq.symm⟩, hWorldEq.symm⟩
      · rintro ⟨⟨⟨hFieldName, hLeftEq⟩, hRightEq⟩, hWorldEq⟩
        have hField : field = candidateField :=
          BinaryField.toTableField_injective hFieldName
        subst candidateField
        subst candidateLeft
        subst candidateRight
        subst candidateWorld
        rfl

/-- One production dense write changes binary lookup exactly at the binary
coordinate encoded by that fact. Other fact arities are isolated. -/
theorem writeDenseFact_binary_lookup
    (tables : FactTables) (fact : CompiledFact) (query : Nat)
    (hQuery : query < tables.binaryCells.size) :
    (tables.writeDenseFact fact).binaryCells[query]?.getD false =
      (tables.binaryCells[query]?.getD false ||
        (binaryWriteIndex? tables fact == some query)) := by
  cases fact with
  | binary field left right world =>
      simp only [FactTables.writeDenseFact, binaryWriteIndex?, binaryCoordinate]
      rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
      by_cases hEq :
          field.index *
              (tables.denseThingCount * tables.denseThingCount * tables.denseWorldCount) +
            ((left * tables.denseThingCount + right) * tables.denseWorldCount + world) = query
      · simp [hEq, hQuery]
      · have hBool :
            (field.index *
                (tables.denseThingCount * tables.denseThingCount * tables.denseWorldCount) +
              ((left * tables.denseThingCount + right) * tables.denseWorldCount + world) == query) =
              false := beq_eq_false_iff_ne.mpr hEq
        simp [hEq, hBool]
  | unary | ternary | tupleProjection | derived =>
      simp [FactTables.writeDenseFact, binaryWriteIndex?]

private theorem writeDenseFact_binaryCells_size
    (tables : FactTables) (fact : CompiledFact) :
    (tables.writeDenseFact fact).binaryCells.size = tables.binaryCells.size := by
  cases fact <;>
    simp [FactTables.writeDenseFact, Array.set!_eq_setIfInBounds]

private theorem binaryWriteIndex?_writeDenseFact
    (tables : FactTables) (written candidate : CompiledFact) :
    binaryWriteIndex? (tables.writeDenseFact written) candidate =
      binaryWriteIndex? tables candidate := by
  cases written <;> cases candidate <;>
    simp [FactTables.writeDenseFact, binaryWriteIndex?]

private theorem foldl_writeDenseFact_binary_lookup_list
    (facts : List CompiledFact) (tables : FactTables) (query : Nat)
    (hQuery : query < tables.binaryCells.size) :
    (facts.foldl FactTables.writeDenseFact tables).binaryCells[query]?.getD false =
      (tables.binaryCells[query]?.getD false ||
        facts.any (fun fact => binaryWriteIndex? tables fact == some query)) := by
  induction facts generalizing tables with
  | nil => simp
  | cons fact facts ih =>
      simp only [List.foldl_cons, List.any_cons]
      have hUpdated : query < (tables.writeDenseFact fact).binaryCells.size := by
        simpa [writeDenseFact_binaryCells_size] using hQuery
      rw [ih (tables.writeDenseFact fact) hUpdated]
      rw [writeDenseFact_binary_lookup tables fact query hQuery]
      simp only [binaryWriteIndex?_writeDenseFact]
      simp [Bool.or_assoc]

/-- Binary lookup after the production compiler's actual fact fold is exactly
initial lookup or membership of the encoded binary coordinate. -/
theorem foldl_writeDenseFact_binary_lookup
    (facts : Array CompiledFact) (tables : FactTables) (query : Nat)
    (hQuery : query < tables.binaryCells.size) :
    (facts.foldl FactTables.writeDenseFact tables).binaryCells[query]?.getD false =
      (tables.binaryCells[query]?.getD false ||
        facts.any (fun fact => binaryWriteIndex? tables fact == some query)) := by
  rw [← Array.foldl_toList, ← Array.any_toList]
  exact foldl_writeDenseFact_binary_lookup_list facts.toList tables query hQuery

/-- Flat ternary coordinate written by one production compiler fact. -/
def ternaryWriteIndex? (tables : FactTables) : CompiledFact → Option Nat
  | .ternary field first second third world =>
      some (field.index * (tables.denseThingCount ^ 3 * tables.denseWorldCount) +
        (((first * tables.denseThingCount + second) * tables.denseThingCount + third) *
          tables.denseWorldCount + world))
  | _ => none

private theorem ternaryWriteIndex?_eq_matchesTernaryFact
    (worldCount thingCount : Nat) (facts : Array CompiledFact)
    (tables : FactTables) (field : TernaryField)
    (x y z : Fin thingCount) (w : Fin worldCount)
    (fact : CompiledFact) (hFact : factWellBounded worldCount thingCount fact) :
    (ternaryWriteIndex? (tables.initializeDense worldCount thingCount
        (projectionArityOfFacts facts)) fact ==
      some (field.index * (thingCount ^ 3 * worldCount) +
        ternaryCoordinate thingCount worldCount x.val y.val z.val w.val)) =
      matchesTernaryFact field x.val y.val z.val w.val fact := by
  cases fact with
  | unary | binary | tupleProjection | derived =>
      simp [ternaryWriteIndex?, matchesTernaryFact]
  | ternary candidateField a b c candidateWorld =>
      rcases hFact with ⟨ha, hb, hc, hw⟩
      have hW : 0 < worldCount := Nat.zero_lt_of_lt w.isLt
      have hT : 0 < thingCount := Nat.zero_lt_of_lt x.isLt
      have hQuery := ternaryCoordinate_lt x.isLt y.isLt z.isLt w.isLt
      have hCandidate := ternaryCoordinate_lt ha hb hc hw
      rw [Bool.eq_iff_iff]
      simp only [ternaryWriteIndex?, FactTables.initializeDense,
        Option.some.injEq, beq_iff_eq, matchesTernaryFact, Bool.and_eq_true]
      constructor
      · intro hIndex
        rcases (rowMajor_eq_iff
          (Nat.mul_pos (Nat.pow_pos hT) hW) hCandidate hQuery).mp hIndex with
          ⟨hFieldIndex, hCoordinate⟩
        have hField := TernaryField.index_injective hFieldIndex
        rcases (rowMajor_eq_iff hW hw w.isLt).mp
          (by simpa [ternaryCoordinate] using hCoordinate) with ⟨hTriple, hWorld⟩
        rcases (rowMajor_eq_iff hT hc z.isLt).mp hTriple with ⟨hPair, hThird⟩
        rcases (rowMajor_eq_iff hT hb y.isLt).mp hPair with ⟨hFirst, hSecond⟩
        exact ⟨⟨⟨⟨congrArg TernaryField.toTableField hField.symm,
          hFirst.symm⟩, hSecond.symm⟩, hThird.symm⟩, hWorld.symm⟩
      · rintro ⟨⟨⟨⟨hFieldName, hFirst⟩, hSecond⟩, hThird⟩, hWorld⟩
        have hField := TernaryField.toTableField_injective hFieldName
        subst candidateField
        subst a
        subst b
        subst c
        subst candidateWorld
        rfl

/-- One production dense write changes ternary lookup exactly at the ternary
coordinate encoded by that fact. Other fact arities are isolated. -/
theorem writeDenseFact_ternary_lookup
    (tables : FactTables) (fact : CompiledFact) (query : Nat)
    (hQuery : query < tables.ternaryCells.size) :
    (tables.writeDenseFact fact).ternaryCells[query]?.getD false =
      (tables.ternaryCells[query]?.getD false ||
        (ternaryWriteIndex? tables fact == some query)) := by
  cases fact with
  | ternary field first second third world =>
      simp only [FactTables.writeDenseFact, ternaryWriteIndex?, ternaryCoordinate]
      rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
      by_cases hEq :
          field.index * (tables.denseThingCount ^ 3 * tables.denseWorldCount) +
            (((first * tables.denseThingCount + second) * tables.denseThingCount + third) *
              tables.denseWorldCount + world) = query
      · simp [hEq, hQuery]
      · have hBool :
            (field.index * (tables.denseThingCount ^ 3 * tables.denseWorldCount) +
              (((first * tables.denseThingCount + second) * tables.denseThingCount + third) *
                tables.denseWorldCount + world) == query) = false :=
          beq_eq_false_iff_ne.mpr hEq
        simp [hEq, hBool]
  | unary | binary | tupleProjection | derived =>
      simp [FactTables.writeDenseFact, ternaryWriteIndex?]

private theorem writeDenseFact_ternaryCells_size
    (tables : FactTables) (fact : CompiledFact) :
    (tables.writeDenseFact fact).ternaryCells.size = tables.ternaryCells.size := by
  cases fact <;>
    simp [FactTables.writeDenseFact, Array.set!_eq_setIfInBounds]

private theorem ternaryWriteIndex?_writeDenseFact
    (tables : FactTables) (written candidate : CompiledFact) :
    ternaryWriteIndex? (tables.writeDenseFact written) candidate =
      ternaryWriteIndex? tables candidate := by
  cases written <;> cases candidate <;>
    simp [FactTables.writeDenseFact, ternaryWriteIndex?]

private theorem foldl_writeDenseFact_ternary_lookup_list
    (facts : List CompiledFact) (tables : FactTables) (query : Nat)
    (hQuery : query < tables.ternaryCells.size) :
    (facts.foldl FactTables.writeDenseFact tables).ternaryCells[query]?.getD false =
      (tables.ternaryCells[query]?.getD false ||
        facts.any (fun fact => ternaryWriteIndex? tables fact == some query)) := by
  induction facts generalizing tables with
  | nil => simp
  | cons fact facts ih =>
      simp only [List.foldl_cons, List.any_cons]
      have hUpdated : query < (tables.writeDenseFact fact).ternaryCells.size := by
        simpa [writeDenseFact_ternaryCells_size] using hQuery
      rw [ih (tables.writeDenseFact fact) hUpdated]
      rw [writeDenseFact_ternary_lookup tables fact query hQuery]
      simp only [ternaryWriteIndex?_writeDenseFact]
      simp [Bool.or_assoc]

/-- Ternary lookup after the production compiler's actual fact fold is exactly
initial lookup or membership of the encoded ternary coordinate. -/
theorem foldl_writeDenseFact_ternary_lookup
    (facts : Array CompiledFact) (tables : FactTables) (query : Nat)
    (hQuery : query < tables.ternaryCells.size) :
    (facts.foldl FactTables.writeDenseFact tables).ternaryCells[query]?.getD false =
      (tables.ternaryCells[query]?.getD false ||
        facts.any (fun fact => ternaryWriteIndex? tables fact == some query)) := by
  rw [← Array.foldl_toList, ← Array.any_toList]
  exact foldl_writeDenseFact_ternary_lookup_list facts.toList tables query hQuery

/-- Concrete coordinate/result pair written by a production projection fact. -/
def projectionWrite? (tables : FactTables) : CompiledFact → Option (Nat × Nat)
  | .tupleProjection tuple slot result world =>
      some (((tuple * tables.denseProjectionArity + slot) *
        tables.denseWorldCount + world), result)
  | _ => none

/-- Apply one fact's projection write to a single observed coordinate. This
exposes the raw table's deterministic last-write behavior. -/
def applyProjectionWrite (tables : FactTables) (query : Nat)
    (current : Option Nat) (fact : CompiledFact) : Option Nat :=
  match projectionWrite? tables fact with
  | some (coordinate, result) => if coordinate == query then some result else current
  | none => current

private theorem applyProjectionWrite_eq_applyProjectionResult
    (worldCount thingCount arity : Nat) (tables : FactTables)
    (p : Fin thingCount) (slot : Nat) (w : Fin worldCount)
    (hSlot : slot < arity) (current : Option Nat) (fact : CompiledFact)
    (hFact : factWellBounded worldCount thingCount fact)
    (hFactSlot : fact.projectionArity ≤ arity) :
    applyProjectionWrite (tables.initializeDense worldCount thingCount arity)
        (projectionCoordinate arity worldCount p.val slot w.val) current fact =
      applyProjectionResult p.val slot w.val current fact := by
  cases fact with
  | unary | binary | ternary | derived =>
      simp [applyProjectionWrite, applyProjectionResult, projectionWrite?]
  | tupleProjection tuple candidateSlot result world =>
      rcases hFact with ⟨hTuple, _hResult, hWorld⟩
      have hCandidateSlot : candidateSlot < arity := by
        simpa [CompiledFact.projectionArity, Nat.lt_iff_add_one_le] using hFactSlot
      have hWorldCount : 0 < worldCount := Nat.zero_lt_of_lt w.isLt
      have hArity : 0 < arity := Nat.zero_lt_of_lt hSlot
      simp only [applyProjectionWrite, projectionWrite?, FactTables.initializeDense,
        applyProjectionResult]
      by_cases hCoordinate :
          (tuple * arity + candidateSlot) * worldCount + world =
            projectionCoordinate arity worldCount p.val slot w.val
      ·
        rcases (rowMajor_eq_iff hWorldCount hWorld w.isLt).mp
          (by simpa [projectionCoordinate] using hCoordinate) with ⟨hPair, hWorldEq⟩
        rcases (rowMajor_eq_iff hArity hCandidateSlot hSlot).mp hPair with
          ⟨hTupleEq, hSlotEq⟩
        simp [hCoordinate, hTupleEq.symm, hSlotEq.symm, hWorldEq.symm]
      ·
        simp [hCoordinate]
        intro hTupleEq hSlotEq hWorldEq
        exfalso
        apply hCoordinate
        subst tuple
        subst candidateSlot
        subst world
        rfl

private theorem foldl_projectionWrite_eq_projectionResult_list
    (worldCount thingCount arity : Nat) (allFacts facts : List CompiledFact)
    (tables : FactTables) (p : Fin thingCount) (slot : Nat)
    (w : Fin worldCount) (hSlot : slot < arity)
    (hFacts : ∀ fact ∈ allFacts, factWellBounded worldCount thingCount fact)
    (hArity : ∀ fact ∈ allFacts, fact.projectionArity ≤ arity)
    (hSubset : ∀ fact ∈ facts, fact ∈ allFacts)
    (initial : Option Nat) :
    facts.foldl
        (applyProjectionWrite (tables.initializeDense worldCount thingCount arity)
          (projectionCoordinate arity worldCount p.val slot w.val)) initial =
      facts.foldl (applyProjectionResult p.val slot w.val) initial := by
  induction facts generalizing initial with
  | nil => rfl
  | cons fact facts ih =>
      simp only [List.foldl_cons]
      rw [applyProjectionWrite_eq_applyProjectionResult worldCount thingCount arity
        tables p slot w hSlot initial fact
        (hFacts fact (hSubset fact (by simp)))
        (hArity fact (hSubset fact (by simp)))]
      apply ih
      intro candidate hCandidate
      exact hSubset candidate (by simp [hCandidate])

theorem foldl_projectionWrite_eq_projectionResult
    (worldCount thingCount : Nat) (facts : Array CompiledFact)
    (tables : FactTables) (p : Fin thingCount) (slot : Nat)
    (w : Fin worldCount) (hSlot : slot < projectionArityOfFacts facts)
    (hFacts : ∀ fact ∈ facts, factWellBounded worldCount thingCount fact) :
    facts.foldl
        (applyProjectionWrite
          (tables.initializeDense worldCount thingCount (projectionArityOfFacts facts))
          (projectionCoordinate (projectionArityOfFacts facts) worldCount
            p.val slot w.val)) none =
      facts.foldl (applyProjectionResult p.val slot w.val) none := by
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  apply foldl_projectionWrite_eq_projectionResult_list worldCount thingCount
    (projectionArityOfFacts facts) facts.toList facts.toList tables p slot w hSlot
  · simpa using hFacts
  · intro fact hFact
    exact fact.projectionArity_le_of_mem facts (by simpa using hFact)
  · intro fact hFact
    exact hFact

/-- One production projection write is exactly `applyProjectionWrite` at an
in-bounds observed coordinate. Other fact arities are isolated. -/
theorem writeDenseFact_projection_lookup
    (tables : FactTables) (fact : CompiledFact) (query : Nat)
    (hQuery : query < tables.projectionCells.size) :
    (tables.writeDenseFact fact).projectionCells[query]?.join =
      applyProjectionWrite tables query (tables.projectionCells[query]?.join) fact := by
  cases fact with
  | tupleProjection tuple slot result world =>
      simp only [FactTables.writeDenseFact, applyProjectionWrite, projectionWrite?,
        projectionCoordinate]
      rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
      by_cases hEq :
          (tuple * tables.denseProjectionArity + slot) * tables.denseWorldCount + world = query
      · simp [hEq, hQuery]
      · have hBool :
            ((tuple * tables.denseProjectionArity + slot) * tables.denseWorldCount + world ==
              query) = false := beq_eq_false_iff_ne.mpr hEq
        simp [hEq, hBool]
  | unary | binary | ternary | derived =>
      simp [FactTables.writeDenseFact, applyProjectionWrite, projectionWrite?]

private theorem writeDenseFact_projectionCells_size
    (tables : FactTables) (fact : CompiledFact) :
    (tables.writeDenseFact fact).projectionCells.size = tables.projectionCells.size := by
  cases fact <;>
    simp [FactTables.writeDenseFact, Array.set!_eq_setIfInBounds]

private theorem projectionWrite?_writeDenseFact
    (tables : FactTables) (written candidate : CompiledFact) :
    projectionWrite? (tables.writeDenseFact written) candidate =
      projectionWrite? tables candidate := by
  cases written <;> cases candidate <;>
    simp [FactTables.writeDenseFact, projectionWrite?]

private theorem applyProjectionWrite_writeDenseFact
    (tables : FactTables) (written candidate : CompiledFact)
    (query : Nat) (current : Option Nat) :
    applyProjectionWrite (tables.writeDenseFact written) query current candidate =
      applyProjectionWrite tables query current candidate := by
  simp [applyProjectionWrite, projectionWrite?_writeDenseFact]

private theorem foldl_writeDenseFact_projection_lookup_list
    (facts : List CompiledFact) (tables : FactTables) (query : Nat)
    (hQuery : query < tables.projectionCells.size) :
    (facts.foldl FactTables.writeDenseFact tables).projectionCells[query]?.join =
      facts.foldl (applyProjectionWrite tables query)
        (tables.projectionCells[query]?.join) := by
  induction facts generalizing tables with
  | nil => rfl
  | cons fact facts ih =>
      simp only [List.foldl_cons]
      have hUpdated : query < (tables.writeDenseFact fact).projectionCells.size := by
        simpa [writeDenseFact_projectionCells_size] using hQuery
      rw [ih (tables.writeDenseFact fact) hUpdated]
      rw [writeDenseFact_projection_lookup tables fact query hQuery]
      congr 1
      funext current candidate
      exact applyProjectionWrite_writeDenseFact tables fact candidate query current

/-- Projection lookup after the production compiler's actual fact fold is the
same deterministic sequence of coordinate-sensitive writes. Compiler conflict
validation separately guarantees that matching writes agree on their result. -/
theorem foldl_writeDenseFact_projection_lookup
    (facts : Array CompiledFact) (tables : FactTables) (query : Nat)
    (hQuery : query < tables.projectionCells.size) :
    (facts.foldl FactTables.writeDenseFact tables).projectionCells[query]?.join =
      facts.foldl (applyProjectionWrite tables query)
        (tables.projectionCells[query]?.join) := by
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  exact foldl_writeDenseFact_projection_lookup_list facts.toList tables query hQuery

/-!
### Production materialization

These corollaries instantiate the fold theorems at `withDenseFacts`, whose
counted initialization explicitly allocates every cell and fills it with
`false`/`none`. Thus the right-hand sides describe the tables consumed by the
checker, rather than an auxiliary materializer used only in a proof.
-/

theorem withDenseFacts_unary_lookup
    (tables : FactTables) (worldCount thingCount : Nat)
    (facts : Array CompiledFact) (query : Nat)
    (hQuery : query < UnaryField.count * thingCount * worldCount) :
    (tables.withDenseFacts worldCount thingCount facts).unaryCells[query]?.getD false =
      facts.any (fun fact =>
        unaryWriteIndex? (tables.initializeDense worldCount thingCount
          (projectionArityOfFacts facts)) fact == some query) := by
  simp only [FactTables.withDenseFacts]
  have hInitialized : query <
      (tables.initializeDense worldCount thingCount
        (projectionArityOfFacts facts)).unaryCells.size := by
    simpa [FactTables.initializeDense] using hQuery
  rw [foldl_writeDenseFact_unary_lookup facts _ query hInitialized]
  have hEmpty :
      (tables.initializeDense worldCount thingCount
        (projectionArityOfFacts facts)).unaryCells[query]?.getD false = false := by
    simp [FactTables.initializeDense, hQuery]
  rw [hEmpty]
  rfl

/-- The value whose cost is used by the checker theorem is the lookup in the
actual materialized unary table, and that value is characterized by the input
fact stream. This theorem makes the executable-representation boundary
explicit; it does not appeal to the compact proof-facing lookup closure. -/
theorem withDenseFacts_unaryTypedTableCosted_value
    (tables : FactTables) (worldCount thingCount : Nat)
    (facts : Array CompiledFact) (field : UnaryField)
    (x : Fin thingCount) (w : Fin worldCount) :
    ((tables.withDenseFacts worldCount thingCount facts).unaryTypedTableCosted
      field x w).value =
      facts.any (fun fact =>
        unaryWriteIndex? (tables.initializeDense worldCount thingCount
          (projectionArityOfFacts facts)) fact ==
            some (field.index * (thingCount * worldCount) +
              unaryCoordinate x.val worldCount w.val)) := by
  rw [FactTables.unaryTypedTableCosted_value_dense]
  simp only [FactTables.unaryTypedTableDense,
    FactTables.withDenseFacts_denseThingCount,
    FactTables.withDenseFacts_denseWorldCount]
  apply withDenseFacts_unary_lookup
  have hField := field.index_lt_count
  have hx := x.isLt
  have hw := w.isLt
  have hCoordinate : unaryCoordinate x.val worldCount w.val <
      thingCount * worldCount := by
    have hWithinRow : x.val * worldCount + w.val <
        x.val * worldCount + worldCount := Nat.add_lt_add_left hw _
    have hNextRow : x.val * worldCount + worldCount ≤
        thingCount * worldCount := by
      simpa [Nat.succ_mul] using
        Nat.mul_le_mul_right worldCount (Nat.succ_le_iff.mpr hx)
    exact lt_of_lt_of_le hWithinRow hNextRow
  have hWithinField :
      field.index * (thingCount * worldCount) +
          unaryCoordinate x.val worldCount w.val <
        field.index * (thingCount * worldCount) + thingCount * worldCount :=
    Nat.add_lt_add_left hCoordinate _
  have hNextField :
      field.index * (thingCount * worldCount) + thingCount * worldCount ≤
        UnaryField.count * thingCount * worldCount := by
    simpa [Nat.succ_mul, Nat.mul_assoc] using
      Nat.mul_le_mul_right (thingCount * worldCount)
        (Nat.succ_le_iff.mpr hField)
  exact lt_of_lt_of_le hWithinField hNextField

/-- On a bounded explicit fact stream, the compact kernel lookup and the dense
native lookup return the same unary value. Their running costs are
different; this theorem establishes implementation correspondence only. -/
theorem explicitFacts_unaryTypedTable_eq_dense
    (worldCount thingCount : Nat) (facts : Array CompiledFact)
    (hFacts : ∀ fact ∈ facts, factWellBounded worldCount thingCount fact)
    (field : UnaryField) (x : Fin thingCount) (w : Fin worldCount) :
    let sparse := facts.foldl compileExplicitFact ({} : FactTables)
    let tables := sparse.withDenseFacts worldCount thingCount facts
    tables.unaryTypedTable field x w = tables.unaryTypedTableDense field x w := by
  dsimp only
  rw [FactTables.unaryTypedTable]
  simp only [FactTables.withDenseFacts_unaryLookup]
  rw [foldl_compileExplicitFact_unaryLookup]
  change (false || facts.any (matchesUnaryFact field x.val w.val)) = _
  simp only [Bool.false_or]
  rw [← FactTables.unaryTypedTableCosted_value_dense]
  rw [withDenseFacts_unaryTypedTableCosted_value]
  rw [Bool.eq_iff_iff]
  simp only [Array.any_eq_true]
  constructor
  · rintro ⟨i, hi, hMatch⟩
    refine ⟨i, hi, ?_⟩
    rw [unaryWriteIndex?_eq_matchesUnaryFact worldCount thingCount facts
      (facts.foldl compileExplicitFact ({} : FactTables))
      field x w facts[i] (hFacts facts[i] (by simp))]
    exact hMatch
  · rintro ⟨i, hi, hIndex⟩
    refine ⟨i, hi, ?_⟩
    rw [← unaryWriteIndex?_eq_matchesUnaryFact worldCount thingCount facts
      (facts.foldl compileExplicitFact ({} : FactTables))
      field x w facts[i] (hFacts facts[i] (by simp))]
    exact hIndex

theorem withDenseFacts_binary_lookup
    (tables : FactTables) (worldCount thingCount : Nat)
    (facts : Array CompiledFact) (query : Nat)
    (hQuery : query < BinaryField.count * thingCount * thingCount * worldCount) :
    (tables.withDenseFacts worldCount thingCount facts).binaryCells[query]?.getD false =
      facts.any (fun fact =>
        binaryWriteIndex? (tables.initializeDense worldCount thingCount
          (projectionArityOfFacts facts)) fact == some query) := by
  simp only [FactTables.withDenseFacts]
  have hInitialized : query <
      (tables.initializeDense worldCount thingCount
        (projectionArityOfFacts facts)).binaryCells.size := by
    simpa [FactTables.initializeDense] using hQuery
  rw [foldl_writeDenseFact_binary_lookup facts _ query hInitialized]
  have hEmpty :
      (tables.initializeDense worldCount thingCount
        (projectionArityOfFacts facts)).binaryCells[query]?.getD false = false := by
    simp [FactTables.initializeDense, hQuery]
  rw [hEmpty]
  rfl

theorem withDenseFacts_binaryTypedTableCosted_value
    (tables : FactTables) (worldCount thingCount : Nat)
    (facts : Array CompiledFact) (field : BinaryField)
    (x y : Fin thingCount) (w : Fin worldCount) :
    ((tables.withDenseFacts worldCount thingCount facts).binaryTypedTableCosted
      field x y w).value =
      facts.any (fun fact =>
        binaryWriteIndex? (tables.initializeDense worldCount thingCount
          (projectionArityOfFacts facts)) fact ==
            some (field.index * (thingCount * thingCount * worldCount) +
              binaryCoordinate thingCount worldCount x.val y.val w.val)) := by
  rw [FactTables.binaryTypedTableCosted_value_dense]
  simp only [FactTables.binaryTypedTableDense,
    FactTables.withDenseFacts_denseThingCount,
    FactTables.withDenseFacts_denseWorldCount]
  apply withDenseFacts_binary_lookup
  have hCoordinate := binaryCoordinate_lt x.isLt y.isLt w.isLt
  have hField := field.index_lt_count
  have hWithin := Nat.add_lt_add_left hCoordinate
    (field.index * (thingCount * thingCount * worldCount))
  have hNext :
      field.index * (thingCount * thingCount * worldCount) +
          thingCount * thingCount * worldCount ≤
        BinaryField.count * thingCount * thingCount * worldCount := by
    simpa [Nat.succ_mul, Nat.mul_assoc] using
      Nat.mul_le_mul_right (thingCount * thingCount * worldCount)
        (Nat.succ_le_iff.mpr hField)
  exact lt_of_lt_of_le hWithin hNext

/-- The compact and dense binary lookups agree on bounded explicit facts. -/
theorem explicitFacts_binaryTypedTable_eq_dense
    (worldCount thingCount : Nat) (facts : Array CompiledFact)
    (hFacts : ∀ fact ∈ facts, factWellBounded worldCount thingCount fact)
    (field : BinaryField) (x y : Fin thingCount) (w : Fin worldCount) :
    let sparse := facts.foldl compileExplicitFact ({} : FactTables)
    let tables := sparse.withDenseFacts worldCount thingCount facts
    tables.binaryTypedTable field x y w =
      tables.binaryTypedTableDense field x y w := by
  dsimp only
  rw [FactTables.binaryTypedTable]
  simp only [FactTables.withDenseFacts_binaryLookup]
  rw [foldl_compileExplicitFact_binaryLookup]
  change (false || facts.any (matchesBinaryFact field x.val y.val w.val)) = _
  simp only [Bool.false_or]
  rw [← FactTables.binaryTypedTableCosted_value_dense]
  rw [withDenseFacts_binaryTypedTableCosted_value]
  rw [Bool.eq_iff_iff]
  simp only [Array.any_eq_true]
  constructor
  · rintro ⟨i, hi, hMatch⟩
    refine ⟨i, hi, ?_⟩
    rw [binaryWriteIndex?_eq_matchesBinaryFact worldCount thingCount facts
      (facts.foldl compileExplicitFact ({} : FactTables))
      field x y w facts[i] (hFacts facts[i] (by simp))]
    exact hMatch
  · rintro ⟨i, hi, hIndex⟩
    refine ⟨i, hi, ?_⟩
    rw [← binaryWriteIndex?_eq_matchesBinaryFact worldCount thingCount facts
      (facts.foldl compileExplicitFact ({} : FactTables))
      field x y w facts[i] (hFacts facts[i] (by simp))]
    exact hIndex

theorem withDenseFacts_ternary_lookup
    (tables : FactTables) (worldCount thingCount : Nat)
    (facts : Array CompiledFact) (query : Nat)
    (hQuery : query < TernaryField.count * thingCount * thingCount * thingCount * worldCount) :
    (tables.withDenseFacts worldCount thingCount facts).ternaryCells[query]?.getD false =
      facts.any (fun fact =>
        ternaryWriteIndex? (tables.initializeDense worldCount thingCount
          (projectionArityOfFacts facts)) fact == some query) := by
  simp only [FactTables.withDenseFacts]
  have hInitialized : query <
      (tables.initializeDense worldCount thingCount
        (projectionArityOfFacts facts)).ternaryCells.size := by
    simpa [FactTables.initializeDense] using hQuery
  rw [foldl_writeDenseFact_ternary_lookup facts _ query hInitialized]
  have hEmpty :
      (tables.initializeDense worldCount thingCount
        (projectionArityOfFacts facts)).ternaryCells[query]?.getD false = false := by
    simp [FactTables.initializeDense, hQuery]
  rw [hEmpty]
  rfl

theorem withDenseFacts_ternaryTypedTableCosted_value
    (tables : FactTables) (worldCount thingCount : Nat)
    (facts : Array CompiledFact) (field : TernaryField)
    (x y z : Fin thingCount) (w : Fin worldCount) :
    ((tables.withDenseFacts worldCount thingCount facts).ternaryTypedTableCosted
      field x y z w).value =
      facts.any (fun fact => ternaryWriteIndex?
        (tables.initializeDense worldCount thingCount (projectionArityOfFacts facts)) fact ==
          some (field.index * (thingCount ^ 3 * worldCount) +
            ternaryCoordinate thingCount worldCount x.val y.val z.val w.val)) := by
  rw [FactTables.ternaryTypedTableCosted_value_dense]
  simp only [FactTables.ternaryTypedTableDense,
    FactTables.withDenseFacts_denseThingCount,
    FactTables.withDenseFacts_denseWorldCount]
  apply withDenseFacts_ternary_lookup
  have hCoordinate := ternaryCoordinate_lt x.isLt y.isLt z.isLt w.isLt
  have hField := field.index_lt_count
  have hWithin := Nat.add_lt_add_left hCoordinate
    (field.index * (thingCount ^ 3 * worldCount))
  have hNextPow : field.index * (thingCount ^ 3 * worldCount) +
      thingCount ^ 3 * worldCount ≤
      TernaryField.count * (thingCount ^ 3 * worldCount) := by
    simpa [Nat.succ_mul] using
      Nat.mul_le_mul_right (thingCount ^ 3 * worldCount)
        (Nat.succ_le_iff.mpr hField)
  exact lt_of_lt_of_le hWithin (by
    simpa [Nat.pow_succ, Nat.mul_assoc] using hNextPow)

theorem explicitFacts_ternaryTypedTable_eq_dense
    (worldCount thingCount : Nat) (facts : Array CompiledFact)
    (hFacts : ∀ fact ∈ facts, factWellBounded worldCount thingCount fact)
    (field : TernaryField) (x y z : Fin thingCount) (w : Fin worldCount) :
    let sparse := facts.foldl compileExplicitFact ({} : FactTables)
    let tables := sparse.withDenseFacts worldCount thingCount facts
    tables.ternaryTypedTable field x y z w =
      tables.ternaryTypedTableDense field x y z w := by
  dsimp only
  rw [FactTables.ternaryTypedTable]
  simp only [FactTables.withDenseFacts_ternaryLookup]
  rw [foldl_compileExplicitFact_ternaryLookup]
  change (false || facts.any (matchesTernaryFact field x.val y.val z.val w.val)) = _
  simp only [Bool.false_or]
  rw [← FactTables.ternaryTypedTableCosted_value_dense]
  rw [withDenseFacts_ternaryTypedTableCosted_value]
  rw [Bool.eq_iff_iff]
  simp only [Array.any_eq_true]
  constructor
  · rintro ⟨i, hi, hMatch⟩
    refine ⟨i, hi, ?_⟩
    rw [ternaryWriteIndex?_eq_matchesTernaryFact worldCount thingCount facts
      (facts.foldl compileExplicitFact ({} : FactTables))
      field x y z w facts[i] (hFacts facts[i] (by simp))]
    exact hMatch
  · rintro ⟨i, hi, hIndex⟩
    refine ⟨i, hi, ?_⟩
    rw [← ternaryWriteIndex?_eq_matchesTernaryFact worldCount thingCount facts
      (facts.foldl compileExplicitFact ({} : FactTables))
      field x y z w facts[i] (hFacts facts[i] (by simp))]
    exact hIndex

theorem withDenseFacts_projection_lookup
    (tables : FactTables) (worldCount thingCount : Nat)
    (facts : Array CompiledFact) (query : Nat)
    (hQuery : query < thingCount * projectionArityOfFacts facts * worldCount) :
    (tables.withDenseFacts worldCount thingCount facts).projectionCells[query]?.join =
      facts.foldl
        (applyProjectionWrite
          (tables.initializeDense worldCount thingCount (projectionArityOfFacts facts)) query)
        none := by
  simp only [FactTables.withDenseFacts]
  have hInitialized : query <
      (tables.initializeDense worldCount thingCount
        (projectionArityOfFacts facts)).projectionCells.size := by
    simpa [FactTables.initializeDense] using hQuery
  rw [foldl_writeDenseFact_projection_lookup facts _ query hInitialized]
  have hEmpty :
      (tables.initializeDense worldCount thingCount
        (projectionArityOfFacts facts)).projectionCells[query]?.join = none := by
    simp [FactTables.initializeDense, hQuery]
  rw [hEmpty]

/-- On a bounded explicit fact stream, compact projection lookup and the dense
native array lookup return the same thing. Both sides use deterministic
last-write semantics; conflict rejection is a separate compiler-validation
property. The two implementations need not take the same number of steps. -/
theorem explicitFacts_tupleProjectionTypedTable_eq_dense
    (worldCount thingCount : Nat) (facts : Array CompiledFact)
    (hFacts : ∀ fact ∈ facts, factWellBounded worldCount thingCount fact)
    (p : Fin thingCount) (slot : Nat) (w : Fin worldCount) :
    let sparse := facts.foldl compileExplicitFact ({} : FactTables)
    let tables := sparse.withDenseFacts worldCount thingCount facts
    tables.tupleProjectionTypedTable p slot w =
      tables.tupleProjectionTypedTableDense p slot w := by
  dsimp only
  rw [FactTables.tupleProjectionTypedTable]
  simp only [FactTables.withDenseFacts_tupleProjectionResult?]
  rw [foldl_compileExplicitFact_projectionResult]
  change (match facts.foldl (applyProjectionResult p.val slot w.val) none with
    | some result => if h : result < thingCount then
        (⟨result, h⟩ : Fin thingCount) else p
    | none => p) = _
  unfold FactTables.tupleProjectionTypedTableDense
  simp only [FactTables.withDenseFacts_denseProjectionArity,
    FactTables.withDenseFacts_denseWorldCount]
  by_cases hSlot : slot < projectionArityOfFacts facts
  · simp only [hSlot, ↓reduceIte]
    have hPair : p.val * projectionArityOfFacts facts + slot <
        thingCount * projectionArityOfFacts facts :=
      rowMajor_lt p.val slot thingCount (projectionArityOfFacts facts) p.isLt hSlot
    have hCoordinate :
        projectionCoordinate (projectionArityOfFacts facts) worldCount
            p.val slot w.val <
          thingCount * projectionArityOfFacts facts * worldCount := by
      simpa [projectionCoordinate, Nat.mul_assoc] using
        rowMajor_lt
          (p.val * projectionArityOfFacts facts + slot) w.val
          (thingCount * projectionArityOfFacts facts) worldCount hPair w.isLt
    rw [withDenseFacts_projection_lookup _ _ _ _ _ hCoordinate]
    rw [foldl_projectionWrite_eq_projectionResult
      worldCount thingCount facts
      (facts.foldl compileExplicitFact ({} : FactTables)) p slot w hSlot hFacts]
    rfl
  · have hOutOfRange : projectionArityOfFacts facts ≤ slot := Nat.le_of_not_gt hSlot
    rw [foldl_applyProjectionResult_none_of_arity_le facts p.val slot w.val hOutOfRange]
    simp [hSlot]

/-- One proposition packages the complete value correspondence between the
compact kernel-facing tables and the dense native tables. This theorem
says nothing about equal running costs: the dense implementation is the
implementation measured by the operational complexity development. -/
structure ExplicitTableCorrespondence
    (worldCount thingCount : Nat) (facts : Array CompiledFact) : Prop where
  unary : ∀ (field : UnaryField) (x : Fin thingCount) (w : Fin worldCount),
    let sparse := facts.foldl compileExplicitFact ({} : FactTables)
    let tables := sparse.withDenseFacts worldCount thingCount facts
    tables.unaryTypedTable field x w = tables.unaryTypedTableDense field x w
  binary : ∀ (field : BinaryField) (x y : Fin thingCount) (w : Fin worldCount),
    let sparse := facts.foldl compileExplicitFact ({} : FactTables)
    let tables := sparse.withDenseFacts worldCount thingCount facts
    tables.binaryTypedTable field x y w = tables.binaryTypedTableDense field x y w
  ternary : ∀ (field : TernaryField) (x y z : Fin thingCount) (w : Fin worldCount),
    let sparse := facts.foldl compileExplicitFact ({} : FactTables)
    let tables := sparse.withDenseFacts worldCount thingCount facts
    tables.ternaryTypedTable field x y z w =
      tables.ternaryTypedTableDense field x y z w
  projection : ∀ (p : Fin thingCount) (slot : Nat) (w : Fin worldCount),
    let sparse := facts.foldl compileExplicitFact ({} : FactTables)
    let tables := sparse.withDenseFacts worldCount thingCount facts
    tables.tupleProjectionTypedTable p slot w =
      tables.tupleProjectionTypedTableDense p slot w

/-- Every bounded explicit model has the complete compact-to-dense table
correspondence required by the `implemented_by` production lookups. -/
theorem explicitFacts_typedTableCorrespondence
    (worldCount thingCount : Nat) (facts : Array CompiledFact)
    (hFacts : ∀ fact ∈ facts, factWellBounded worldCount thingCount fact) :
    ExplicitTableCorrespondence worldCount thingCount facts where
  unary := explicitFacts_unaryTypedTable_eq_dense worldCount thingCount facts hFacts
  binary := explicitFacts_binaryTypedTable_eq_dense worldCount thingCount facts hFacts
  ternary := explicitFacts_ternaryTypedTable_eq_dense worldCount thingCount facts hFacts
  projection :=
    explicitFacts_tupleProjectionTypedTable_eq_dense worldCount thingCount facts hFacts

/-- The explicit compiler's input condition: every resolved coordinate refers
to an element of the finite model encoded by the AST. -/
def explicitModelWellBounded (ast : ModelAST) : Prop :=
  ∀ fact ∈ ast.facts, factWellBounded ast.worldCount ast.thingCount fact

/-- End-to-end table-representation guarantee for a well-bounded explicit
compiler input. Together with `compileExplicitModelASTCosted_value`, this
connects the compact production compiler, the counted compiler, and all four
dense native lookup implementations. -/
theorem explicitCompilationTableCorrespondence
    (ast : ModelAST) (hBounded : explicitModelWellBounded ast) :
    ExplicitTableCorrespondence ast.worldCount ast.thingCount ast.facts :=
  explicitFacts_typedTableCorrespondence
    ast.worldCount ast.thingCount ast.facts hBounded

/-- The complete explicit-compilation package keeps three claims distinct:
the production result, erasure of the counted compiler, and lookup-value
correspondence between compact and dense representations. -/
structure ExplicitCompilationGuarantee (ast : ModelAST) : Prop where
  countedErasesToProduction :
    (compileExplicitModelASTCosted ast).value = compileExplicitModelAST ast
  lookupCorrespondence :
    ExplicitTableCorrespondence ast.worldCount ast.thingCount ast.facts

/-- A well-bounded explicit compiler input receives both the executable-erasure
guarantee and the complete four-table representation guarantee. -/
theorem explicitCompilationGuarantee
    (ast : ModelAST) (hBounded : explicitModelWellBounded ast) :
    ExplicitCompilationGuarantee ast where
  countedErasesToProduction := compileExplicitModelASTCosted_value ast
  lookupCorrespondence := explicitCompilationTableCorrespondence ast hBounded

end Production

structure ProjectionTable where
  thingCount : Nat
  worldCount : Nat
  maxArity : Nat
  cells : Array (Option Nat)
  cells_size : cells.size = thingCount * maxArity * worldCount
deriving Repr

namespace ProjectionTable

def empty (thingCount worldCount maxArity : Nat) : ProjectionTable :=
  { thingCount, worldCount, maxArity
    cells := Array.replicate (thingCount * maxArity * worldCount) none
    cells_size := by simp }

def index (table : ProjectionTable) (tuple slot world : Nat) : Nat :=
  (tuple * table.maxArity + slot) * table.worldCount + world

def lookup (table : ProjectionTable) (tuple slot world : Nat) : Option Nat :=
  table.cells[table.index tuple slot world]?.join

/-- Conflicting results are rejected; identical duplicate facts are idempotent. -/
def insert (table : ProjectionTable) (tuple slot world result : Nat) :
    Except Unit ProjectionTable := do
  if !(tuple < table.thingCount && slot < table.maxArity && world < table.worldCount) then
    throw ()
  let idx := table.index tuple slot world
  match table.cells[idx]? with
  | some none =>
      let cells := table.cells.set! idx (some result)
      pure { table with cells := cells, cells_size := by simp [cells, table.cells_size] }
  | some (some old) => if old = result then pure table else throw ()
  | none => throw ()

end ProjectionTable

def unaryCells (fieldCount things worlds : Nat) : Nat :=
  fieldCount * things * worlds

def binaryCells (fieldCount things worlds : Nat) : Nat :=
  fieldCount * things ^ 2 * worlds

def ternaryCells (fieldCount things worlds : Nat) : Nat :=
  fieldCount * things ^ 3 * worlds

def projectionCells (things worlds maxArity : Nat) : Nat :=
  things * maxArity * worlds

def explicitTableCells
    (unaryFieldCount binaryFieldCount ternaryFieldCount things worlds maxArity : Nat) : Nat :=
  unaryCells unaryFieldCount things worlds +
    binaryCells binaryFieldCount things worlds +
    ternaryCells ternaryFieldCount things worlds +
    projectionCells things worlds maxArity

theorem unaryCells_polynomial (f t w : Nat) : unaryCells f t w = f * t * w := rfl
theorem binaryCells_polynomial (f t w : Nat) : binaryCells f t w = f * t ^ 2 * w := rfl
theorem ternaryCells_polynomial (f t w : Nat) : ternaryCells f t w = f * t ^ 3 * w := rfl

example : (FlatBoolTable.empty 2 3).cells.size = 6 := by native_decide
example : ((FlatBoolTable.empty 2 3).setCosted 1 2).cost = 3 := by native_decide

example :
    ((ProjectionTable.empty 2 1 2).insert 1 0 0 1 >>= fun table =>
      table.insert 1 0 0 1).isOk := by native_decide

private def projectionInsertFailed (result : Except Unit ProjectionTable) : Bool :=
  match result with | .error _ => true | .ok _ => false

example :
    projectionInsertFailed
      ((ProjectionTable.empty 2 1 2).insert 1 0 0 1 >>= fun table =>
        table.insert 1 0 0 0) := by native_decide

end LeanUfo.UFO.DSL.Complexity
