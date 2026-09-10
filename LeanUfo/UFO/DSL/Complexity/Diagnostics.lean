import LeanUfo.UFO.DSL.Complexity.CostModel
import LeanUfo.UFO.DSL.Compiler.VerifiedModel

/-!
# Diagnostic query and output costs

This module provides guarded dense queries, their compilation-correspondence
proofs, and deterministic output-limiter primitives. The counted production
axiom analysis is in `Diagnostic.AxiomAnalysis`, which composes query and
evidence-production costs. The separate pre-certification path in
`Diagnostic.DerivedAssertions` counts the separate pre-certification selection,
complete report construction, and output cap.
-/

namespace LeanUfo.UFO.DSL.Complexity

/-- Diagnostic variables carry natural-number coordinates. Check their domains
before a dense read so an invalid coordinate cannot alias a different row or
field. Each guard costs a comparison and a branch. The dense core charges its
own arithmetic and array access. Correspondence requires an agreement proof,
as in the compiler's proof-carrying interpretation (RadixExperiment's method of
proving each representation change separately; see `docs/dsl/complexity.md`). -/
def diagnosticUnaryCosted (worldCount thingCount : Nat) (tables : FactTables)
    (field : UnaryField) (x w : Nat) : Costed Bool :=
  if hx : x < thingCount then
    if hw : w < worldCount then
      Costed.charge 4 (tables.unaryTypedTableCosted field ⟨x, hx⟩ ⟨w, hw⟩)
    else .tick false 4
  else .tick false 2

def diagnosticBinaryCosted (worldCount thingCount : Nat) (tables : FactTables)
    (field : BinaryField) (x y w : Nat) : Costed Bool :=
  if hx : x < thingCount then
    if hy : y < thingCount then
      if hw : w < worldCount then
        Costed.charge 6 (tables.binaryTypedTableCosted field ⟨x, hx⟩ ⟨y, hy⟩ ⟨w, hw⟩)
      else .tick false 6
    else .tick false 4
  else .tick false 2

def diagnosticTernaryCosted (worldCount thingCount : Nat) (tables : FactTables)
    (field : TernaryField) (x y z w : Nat) : Costed Bool :=
  if hx : x < thingCount then
    if hy : y < thingCount then
      if hz : z < thingCount then
        if hw : w < worldCount then
          Costed.charge 8
            (tables.ternaryTypedTableCosted field ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ ⟨w, hw⟩)
        else .tick false 8
      else .tick false 6
    else .tick false 4
  else .tick false 2

theorem diagnosticUnaryCosted_cost_le (worldCount thingCount : Nat) (tables : FactTables)
    (field : UnaryField) (x w : Nat) :
    (diagnosticUnaryCosted worldCount thingCount tables field x w).cost ≤ 12 := by
  unfold diagnosticUnaryCosted
  split <;> (try split) <;> simp

theorem diagnosticBinaryCosted_cost_le (worldCount thingCount : Nat) (tables : FactTables)
    (field : BinaryField) (x y w : Nat) :
    (diagnosticBinaryCosted worldCount thingCount tables field x y w).cost ≤ 17 := by
  unfold diagnosticBinaryCosted
  split <;> (try split) <;> (try split) <;> simp

theorem diagnosticTernaryCosted_cost_le (worldCount thingCount : Nat) (tables : FactTables)
    (field : TernaryField) (x y z w : Nat) :
    (diagnosticTernaryCosted worldCount thingCount tables field x y z w).cost ≤ 22 := by
  unfold diagnosticTernaryCosted
  split <;> (try split) <;> (try split) <;> (try split) <;> simp

theorem diagnosticUnaryCosted_value (worldCount thingCount : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups worldCount thingCount =
      tables.denseLookups worldCount thingCount)
    (field : UnaryField) (x : Fin thingCount) (w : Fin worldCount) :
    (diagnosticUnaryCosted worldCount thingCount tables field x.val w.val).value =
      tables.unaryTypedTable field x w := by
  simp only [diagnosticUnaryCosted, x.isLt, w.isLt, ↓reduceDIte, Costed.charge_value,
    FactTables.unaryTypedTableCosted_value_dense]
  exact (congrArg (fun queries => queries.unary field x w) agreement).symm

theorem diagnosticBinaryCosted_value (worldCount thingCount : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups worldCount thingCount =
      tables.denseLookups worldCount thingCount)
    (field : BinaryField) (x y : Fin thingCount) (w : Fin worldCount) :
    (diagnosticBinaryCosted worldCount thingCount tables field x.val y.val w.val).value =
      tables.binaryTypedTable field x y w := by
  simp only [diagnosticBinaryCosted, x.isLt, y.isLt, w.isLt, ↓reduceDIte, Costed.charge_value,
    FactTables.binaryTypedTableCosted_value_dense]
  exact (congrArg (fun queries => queries.binary field x y w) agreement).symm

theorem diagnosticTernaryCosted_value (worldCount thingCount : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups worldCount thingCount =
      tables.denseLookups worldCount thingCount)
    (field : TernaryField) (x y z : Fin thingCount) (w : Fin worldCount) :
    (diagnosticTernaryCosted worldCount thingCount tables field x.val y.val z.val w.val).value =
      tables.ternaryTypedTable field x y z w := by
  simp only [diagnosticTernaryCosted, x.isLt, y.isLt, z.isLt, w.isLt, ↓reduceDIte,
    Costed.charge_value, FactTables.ternaryTypedTableCosted_value_dense]
  exact (congrArg (fun queries => queries.ternary field x y z w) agreement).symm

/-- Bounded explicit compilation discharges the representation-agreement
precondition. No equality between sparse and dense execution costs is assumed. -/
theorem diagnosticUnaryCosted_compiled (ast : ModelAST)
    (bounded : Production.explicitModelWellBounded ast)
    (field : UnaryField) (x : Fin ast.thingCount) (w : Fin ast.worldCount) :
    (diagnosticUnaryCosted ast.worldCount ast.thingCount (compileExplicitModelAST ast)
      field x.val w.val).value =
        (compileExplicitModelAST ast).unaryLookup field.toTableField x.val w.val :=
  diagnosticUnaryCosted_value _ _ _ (compiledLookups_agree ast bounded) field x w

theorem diagnosticBinaryCosted_compiled (ast : ModelAST)
    (bounded : Production.explicitModelWellBounded ast)
    (field : BinaryField) (x y : Fin ast.thingCount) (w : Fin ast.worldCount) :
    (diagnosticBinaryCosted ast.worldCount ast.thingCount (compileExplicitModelAST ast)
      field x.val y.val w.val).value =
        (compileExplicitModelAST ast).binaryLookup field.toTableField x.val y.val w.val :=
  diagnosticBinaryCosted_value _ _ _ (compiledLookups_agree ast bounded) field x y w

theorem diagnosticTernaryCosted_compiled (ast : ModelAST)
    (bounded : Production.explicitModelWellBounded ast)
    (field : TernaryField) (x y z : Fin ast.thingCount) (w : Fin ast.worldCount) :
    (diagnosticTernaryCosted ast.worldCount ast.thingCount (compileExplicitModelAST ast)
      field x.val y.val z.val w.val).value =
        (compileExplicitModelAST ast).ternaryLookup field.toTableField x.val y.val z.val w.val :=
  diagnosticTernaryCosted_value _ _ _ (compiledLookups_agree ast bounded) field x y z w

/-- Bounded diagnostic output with deterministic truncation. -/
structure BoundedEvidence (α : Type u) where
  items : Array α
  truncated : Bool
deriving Repr, Inhabited, DecidableEq

/-- Copy only the retained prefix through direct indexed reads. Each item
costs four operations: iteration, read, write, and emission. Prefix selection
costs two, array initialization costs one, and the truncation comparison costs
one. The existing counted constructor supplies the iteration and write costs.
This follows compositional cost semantics (Niu et al., POPL 2022,
doi:10.1145/3498670); the bound excludes string-character and allocator costs. -/
def boundedEvidenceCosted (budget : Nat) (items : Array α) : Costed (BoundedEvidence α) := do
  let kept ← Costed.charge 3 <| Costed.vectorOfFn fun i : Fin (min budget items.size) =>
    Costed.tick (items[i.val]'(Nat.lt_of_lt_of_le i.isLt (Nat.min_le_right ..))) 2
  Costed.tick { items := kept.toArray, truncated := budget < items.size } 1

def boundedEvidence (budget : Nat) (items : Array α) : BoundedEvidence α :=
  (boundedEvidenceCosted budget items).value

@[simp] theorem boundedEvidenceCosted_value (budget : Nat) (items : Array α) :
    (boundedEvidenceCosted budget items).value = boundedEvidence budget items := rfl

/-- The executable copy retains exactly the original prefix and reports
truncation exactly when the input exceeds the budget. -/
theorem boundedEvidence_eq_prefix (budget : Nat) (items : Array α) :
    boundedEvidence budget items =
      { items := items.extract 0 budget, truncated := budget < items.size } := by
  simp only [boundedEvidence, boundedEvidenceCosted, Bind.bind, Costed.bind_value,
    Costed.charge_value, Costed.vectorOfFn_value, Costed.tick_value, Vector.toArray_ofFn]
  congr 1
  apply Array.ext
  · simp
  · intro i hi hj
    simp

theorem boundedEvidenceCosted_cost (budget : Nat) (items : Array α) :
    (boundedEvidenceCosted budget items).cost =
      4 * min budget items.size + 4 := by
  simp only [boundedEvidenceCosted, Bind.bind, Costed.bind_cost, Costed.charge_cost,
    Costed.tick_cost]
  rw [Costed.vectorOfFn_cost_eq _ 2 (by intros; rfl)]
  omega

theorem boundedEvidence_size_le_budget (budget : Nat) (items : Array α) :
    (boundedEvidence budget items).items.size ≤ budget := by
  simp [boundedEvidence_eq_prefix]

theorem boundedEvidence_size_le_input (budget : Nat) (items : Array α) :
    (boundedEvidence budget items).items.size ≤ items.size := by
  simp [boundedEvidence_eq_prefix]

/-- Reapplying the same budget does not change the retained items. One cap
at the producer boundary therefore suffices for output length and order. -/
theorem boundedEvidence_items_idempotent (budget : Nat) (items : Array α) :
    (boundedEvidence budget (boundedEvidence budget items).items).items =
      (boundedEvidence budget items).items := by
  simp [boundedEvidence_eq_prefix]

/-- The copy cost depends on emitted items, not the discarded suffix. -/
theorem boundedEvidenceCosted_cost_eq_emitted (budget : Nat) (items : Array α) :
    (boundedEvidenceCosted budget items).cost =
      4 * (boundedEvidence budget items).items.size + 4 := by
  simp [boundedEvidenceCosted_cost, boundedEvidence_eq_prefix]

end LeanUfo.UFO.DSL.Complexity
