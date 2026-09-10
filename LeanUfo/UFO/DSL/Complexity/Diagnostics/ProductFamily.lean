import LeanUfo.UFO.DSL.Complexity.Diagnostics
import LeanUfo.UFO.DSL.Checker.Axioms

/-!
# Counted validation of declared product families

The axiom 99 diagnostic must inspect the supplied witness arrays. Searching for
different dimensions can accept a family that the certification checker rejects.
The validator below checks finite coordinates and equal array lengths, then
checks projection membership, dimension/type associations, and coverage of all
characterization targets. Each finite scan stops at its first decisive result.

Projection uses the compiler's indexed table and its tuple-as-default rule.
There is no search over candidate projection results. The bounds count table
reads, coordinate arithmetic, array reads, comparisons, and visited loop steps.
Cost composition follows the approach of Niu et al. (POPL 2022,
doi:10.1145/3498670): costs accumulate alongside results, and the ordinary
diagnostic discards the cost field. The machine-model limits are stated in
`docs/dsl/complexity.md`.
-/

namespace LeanUfo.UFO.DSL.Complexity

open Checker

private def familyProjectionRowsCosted (tables : FactTables)
    (family : ProductFamilySpec) (x : Fin T) (w : Fin W) : Costed Bool :=
  allFinEvalCosted T fun p =>
    (tables.binaryTypedTableCosted .memberOf p x w).implies fun _ =>
      allFinEvalCosted family.dimensionThings.size fun i => do
        let dimension ← Costed.tick family.dimensionThings[i.val] 1
        let component ← tables.tupleProjectionTypedTableCosted p i.val w
        diagnosticBinaryCosted W T tables .memberOf component.val dimension w.val

private theorem familyProjectionRowsCosted_cost_le (tables : FactTables)
    (family : ProductFamilySpec) (x : Fin T) (w : Fin W) :
    (familyProjectionRowsCosted tables family x w).cost ≤
      T * (31 * family.dimensionThings.size + 15) := by
  unfold familyProjectionRowsCosted
  apply allFinEvalCosted_cost_le _ _ (31 * family.dimensionThings.size + 13)
  intro p
  apply le_trans (Costed.implies_cost_le _ _ 11 (31 * family.dimensionThings.size) ?_ ?_) (by omega)
  · simp
  · have h := allFinEvalCosted_cost_le family.dimensionThings.size
      (fun i => do
        let dimension ← Costed.tick family.dimensionThings[i.val] 1
        let component ← tables.tupleProjectionTypedTableCosted p i.val w
        diagnosticBinaryCosted W T tables .memberOf component.val dimension w.val) 29 (by
          intro i
          have hp := tables.tupleProjectionTypedTableCosted_cost_le p i.val w
          have hb := diagnosticBinaryCosted_cost_le W T tables .memberOf
            (tables.tupleProjectionTypedTableCosted p i.val w).value.val
            family.dimensionThings[i.val] w.val
          simp only [Bind.bind, Costed.bind, Costed.tick]
          omega)
    simpa [Nat.mul_comm] using h

private def familyAssociationRowsCosted (tables : FactTables)
    (family : ProductFamilySpec) (sameSize : family.dimensionThings.size = family.typeThings.size)
    (t : Fin T) (w : Fin W) : Costed Bool :=
  allFinEvalCosted family.dimensionThings.size fun i => do
    let dimension ← Costed.tick family.dimensionThings[i.val] 1
    let qualityType ← Costed.tick (family.typeThings[i.val]'(by omega)) 1
    (diagnosticBinaryCosted W T tables .associatedWith dimension qualityType w.val).andThen fun _ =>
      diagnosticBinaryCosted W T tables .characterization t.val qualityType w.val

private theorem familyAssociationRowsCosted_cost_le (tables : FactTables)
    (family : ProductFamilySpec) (sameSize : family.dimensionThings.size = family.typeThings.size)
    (t : Fin T) (w : Fin W) :
    (familyAssociationRowsCosted tables family sameSize t w).cost ≤
      39 * family.dimensionThings.size := by
  unfold familyAssociationRowsCosted
  have h := allFinEvalCosted_cost_le family.dimensionThings.size
    (fun i => do
      let dimension ← Costed.tick family.dimensionThings[i.val] 1
      let qualityType ← Costed.tick (family.typeThings[i.val]'(by omega)) 1
      (diagnosticBinaryCosted W T tables .associatedWith dimension qualityType w.val).andThen fun _ =>
        diagnosticBinaryCosted W T tables .characterization t.val qualityType w.val) 37 (by
          intro i
          have h := Costed.andThen_cost_le
            (diagnosticBinaryCosted W T tables .associatedWith family.dimensionThings[i.val]
              (family.typeThings[i.val]'(by omega)) w.val)
            (fun _ => diagnosticBinaryCosted W T tables .characterization
              t.val (family.typeThings[i.val]'(by omega)) w.val) 17 17
            (diagnosticBinaryCosted_cost_le ..) (diagnosticBinaryCosted_cost_le ..)
          simp only [Bind.bind, Costed.bind, Costed.tick]
          omega)
  simpa [Nat.mul_comm] using h

private def familyCoverageRowsCosted (tables : FactTables)
    (family : ProductFamilySpec) (t : Fin T) (w : Fin W) : Costed Bool :=
  allFinEvalCosted T fun u =>
    (tables.binaryTypedTableCosted .characterization t u w).implies fun _ =>
      anyArrayCosted family.typeThings fun qualityType =>
        Costed.tick (u.val == qualityType) 1

private theorem familyCoverageRowsCosted_cost_le (tables : FactTables)
    (family : ProductFamilySpec) (t : Fin T) (w : Fin W) :
    (familyCoverageRowsCosted tables family t w).cost ≤
      T * (4 * family.typeThings.size + 15) := by
  unfold familyCoverageRowsCosted
  apply allFinEvalCosted_cost_le _ _ (4 * family.typeThings.size + 13)
  intro u
  apply le_trans (Costed.implies_cost_le _ _ 11 (4 * family.typeThings.size) ?_ ?_) (by omega)
  · simp
  · have h := anyArrayCosted_cost_le family.typeThings
      (fun qualityType => Costed.tick (u.val == qualityType) 1) 1 (by simp)
    simpa [Nat.mul_comm] using h

/-- Check the declared record without constructing a replacement family.
Raw records can contain invalid coordinates or unequal arrays, so validation
precedes all dependent array reads. Duplicate records are handled by the
surrounding existential scan, which can accept a later valid witness. -/
def productFamilyDiagnosticCosted (W T : Nat) (tables : FactTables)
    (x t w : Nat) (family : ProductFamilySpec) : Costed Bool :=
  ((Costed.tick (family.domain == x) 1).andThen fun _ =>
    Costed.tick (family.qualityType == t) 1).andThen fun _ =>
    if hx : x < T then
      if ht : t < T then
        if hw : w < W then
          if hs : family.dimensionThings.size = family.typeThings.size then
            Costed.charge 8 <|
              (allArrayCosted family.dimensionThings fun y => Costed.tick (decide (y < T)) 1).andThen fun _ =>
                (allArrayCosted family.typeThings fun z => Costed.tick (decide (z < T)) 1).andThen fun _ =>
                  ((familyProjectionRowsCosted tables family ⟨x, hx⟩ ⟨w, hw⟩).andThen fun _ =>
                    familyAssociationRowsCosted tables family hs ⟨t, ht⟩ ⟨w, hw⟩).andThen fun _ =>
                      familyCoverageRowsCosted tables family ⟨t, ht⟩ ⟨w, hw⟩
          else .tick false 8
        else .tick false 6
      else .tick false 4
    else .tick false 2

/-- `T` counts things; `D` and `Z` count supplied dimension and type slots.
World lookup has constant unit cost, so only the selected world is inspected. -/
def productFamilyDiagnosticBound (T D Z : Nat) : Nat :=
  T * (31 * D + 15) + 39 * D + T * (4 * Z + 15) + 4 * D + 4 * Z + 16

theorem productFamilyDiagnosticCosted_cost_le (W T : Nat) (tables : FactTables)
    (x t w : Nat) (family : ProductFamilySpec) :
    (productFamilyDiagnosticCosted W T tables x t w family).cost ≤
      productFamilyDiagnosticBound T family.dimensionThings.size family.typeThings.size := by
  have hd := allArrayCosted_cost_le family.dimensionThings
    (fun y => Costed.tick (decide (y < T)) 1) 1 (by simp)
  have hz := allArrayCosted_cost_le family.typeThings
    (fun z => Costed.tick (decide (z < T)) 1) 1 (by simp)
  unfold productFamilyDiagnosticCosted
  apply le_trans (Costed.andThen_cost_le _ _ 3
    (productFamilyDiagnosticBound T family.dimensionThings.size family.typeThings.size - 4)
    (Costed.andThen_cost_le _ _ 1 1 (Nat.le_refl _) (Nat.le_refl _)) ?_) ?_
  · split <;> rename_i hx
    · split <;> rename_i ht
      · split <;> rename_i hw
        · split <;> rename_i hs
          · have hp := familyProjectionRowsCosted_cost_le tables family ⟨x, hx⟩ ⟨w, hw⟩
            have ha := familyAssociationRowsCosted_cost_le tables family hs ⟨t, ht⟩ ⟨w, hw⟩
            have hc := familyCoverageRowsCosted_cost_le tables family ⟨t, ht⟩ ⟨w, hw⟩
            have hpair := Costed.andThen_cost_le _
              (fun _ => familyAssociationRowsCosted tables family hs ⟨t, ht⟩ ⟨w, hw⟩) _ _ hp ha
            have hbody := Costed.andThen_cost_le _
              (fun _ => familyCoverageRowsCosted tables family ⟨t, ht⟩ ⟨w, hw⟩) _ _ hpair hc
            have htypes := Costed.andThen_cost_le _
              (fun _ => ((familyProjectionRowsCosted tables family ⟨x, hx⟩ ⟨w, hw⟩).andThen fun _ =>
                familyAssociationRowsCosted tables family hs ⟨t, ht⟩ ⟨w, hw⟩).andThen fun _ =>
                  familyCoverageRowsCosted tables family ⟨t, ht⟩ ⟨w, hw⟩) _ _ hz hbody
            have hall := Costed.andThen_cost_le _
              (fun _ => (allArrayCosted family.typeThings fun z => Costed.tick (decide (z < T)) 1).andThen fun _ =>
                ((familyProjectionRowsCosted tables family ⟨x, hx⟩ ⟨w, hw⟩).andThen fun _ =>
                  familyAssociationRowsCosted tables family hs ⟨t, ht⟩ ⟨w, hw⟩).andThen fun _ =>
                    familyCoverageRowsCosted tables family ⟨t, ht⟩ ⟨w, hw⟩) _ _ hd htypes
            simp only [Costed.charge_cost]
            unfold productFamilyDiagnosticBound
            omega
          · simp [Costed.tick, productFamilyDiagnosticBound]
        · simp [Costed.tick, productFamilyDiagnosticBound]
      · simp [Costed.tick, productFamilyDiagnosticBound]
    · simp [Costed.tick, productFamilyDiagnosticBound]
  · unfold productFamilyDiagnosticBound
    omega

theorem productFamilyDiagnosticBound_mono {T T' D D' Z Z' : Nat}
    (hT : T ≤ T') (hD : D ≤ D') (hZ : Z ≤ Z') :
    productFamilyDiagnosticBound T D Z ≤ productFamilyDiagnosticBound T' D' Z' := by
  unfold productFamilyDiagnosticBound
  repeat' first
    | assumption
    | exact Nat.le_refl _
    | apply Nat.add_le_add
    | apply Nat.mul_le_mul

/-- For finite, equally sized witness arrays, success means exactly the three
relational conditions of a product-family witness. The statement uses dense
table semantics; compiler table agreement supplies the sparse interpretation.
Coverage permits repeated listed types, as does the certification checker. -/
theorem productFamilyDiagnosticCosted_valid_iff (tables : FactTables)
    (x t : Fin T) (w : Fin W) (ys zs : Array (Fin T)) (sameSize : ys.size = zs.size) :
    (productFamilyDiagnosticCosted W T tables x.val t.val w.val
      { domain := x.val, qualityType := t.val,
        dimensionThings := ys.map Fin.val, typeThings := zs.map Fin.val }).value = true ↔
      (∀ p : Fin T, tables.binaryTypedTableDense .memberOf p x w = true →
        ∀ i : Fin ys.size, tables.binaryTypedTableDense .memberOf
          (tables.tupleProjectionTypedTableDense p i.val w) ys[i.val] w = true) ∧
      (∀ i : Fin ys.size,
        tables.binaryTypedTableDense .associatedWith ys[i.val] (zs[i.val]'(by omega)) w = true ∧
        tables.binaryTypedTableDense .characterization t (zs[i.val]'(by omega)) w = true) ∧
      (∀ u : Fin T, tables.binaryTypedTableDense .characterization t u w = true →
        ∃ z ∈ zs, u = z) := by
  have valid (values : Array (Fin T)) :
      (allArrayCosted (values.map Fin.val) fun a => Costed.tick (decide (a < T)) 1).value = true := by
    rw [allArrayCosted_value]
    simp
  simp only [productFamilyDiagnosticCosted, Costed.andThen_value, Costed.tick_value,
    beq_self_eq_true, x.isLt, t.isLt, w.isLt, ↓reduceDIte, Array.size_map, sameSize,
    Costed.charge_value, valid, Bool.true_and]
  simp [familyProjectionRowsCosted, familyAssociationRowsCosted, familyCoverageRowsCosted,
    allFinEvalCosted_value, Costed.implies_value, Costed.andThen_value,
    Bind.bind, Costed.bind, Costed.tick, diagnosticBinaryCosted,
    FactTables.binaryTypedTableCosted_value_dense,
    FactTables.tupleProjectionTypedTableCosted_value_dense,
    anyArrayCosted_eq_list, anyListCosted_eq_true_iff, Fin.ext_iff]
  have implication (b : Bool) (p : Prop) : (b = false ∨ p) ↔ (b = true → p) := by
    cases b <;> simp
  simp only [implication, and_assoc]
  constructor
  all_goals
    rintro ⟨hp, ha, hc⟩
    refine ⟨?_, ?_, ?_⟩
    · intro p h i
      exact hp p h ⟨i.val, by
        have hi := i.isLt
        simp only [Array.size_map] at hi ⊢
        exact hi⟩
    · intro i
      exact ha ⟨i.val, by
        have hi := i.isLt
        simp only [Array.size_map] at hi ⊢
        exact hi⟩
    · intro u hu
      rcases hc u hu with ⟨z, hz, heq⟩
      exact ⟨z, hz, heq.symm⟩

/-- The diagnostic checks the same relational witness conditions as the
certification checker when both interpret the same tables. This theorem does
not identify their costs: the diagnostic includes concrete dense-query work.
Conversion of a raw registry into finite witnesses is a separate obligation. -/
theorem productFamilyDiagnosticCosted_checker_iff (M : FiniteModel4)
    (tables : FactTables) (pf : ProductFamilyWitness M.thingCount M.worldCount)
    (member : (fun x y w => tables.binaryTypedTableDense .memberOf x y w) = M.memberOf)
    (associated : (fun x y w => tables.binaryTypedTableDense .associatedWith x y w) = M.associatedWith)
    (characterization : (fun x y w => tables.binaryTypedTableDense .characterization x y w) = M.characterization)
    (projection : ∀ {n : Nat} (p : Fin M.thingCount) (i : Fin n) (w : Fin M.worldCount),
      tables.tupleProjectionTypedTableDense p i.val w = M.tupleProjection p i w) :
    (productFamilyDiagnosticCosted M.worldCount M.thingCount tables
      pf.domain.val pf.qualityType.val pf.world.val
      { domain := pf.domain.val, qualityType := pf.qualityType.val,
        dimensionThings := pf.dimensionThings.map Fin.val,
        typeThings := pf.typeThings.map Fin.val }).value = true ↔
      productFamilyWitnessProp M pf pf.domain pf.qualityType pf.world := by
  rw [productFamilyDiagnosticCosted_valid_iff tables pf.domain pf.qualityType pf.world
    pf.dimensionThings pf.typeThings pf.sameSize]
  have coverage (u : Fin M.thingCount) :
      (∃ z ∈ pf.typeThings, u = z) ↔
        ∃ i : Fin pf.dimensionThings.size, u = productFamilyTypes pf i := by
    constructor
    · rintro ⟨z, hz, rfl⟩
      rcases Array.mem_iff_getElem.mp hz with ⟨i, hi, heq⟩
      refine ⟨⟨i, by have := pf.sameSize; omega⟩, ?_⟩
      simpa [productFamilyTypes] using heq.symm
    · rintro ⟨i, rfl⟩
      exact ⟨productFamilyTypes pf i, Array.getElem_mem .., rfl⟩
  simp only [member, associated, characterization, projection, coverage]
  simp [productFamilyWitnessProp, productFamilyDimensions, productFamilyTypes]

/-- Search supplied records in source order. A malformed record does not hide
a later valid witness for the same domain and quality type. -/
def productFamiliesDiagnosticCosted (W T : Nat) (tables : FactTables)
    (x t w : Nat) : Costed Bool :=
  anyArrayCosted tables.productFamilies (productFamilyDiagnosticCosted W T tables x t w)

def productFamiliesDiagnosticBound (T : Nat) (families : Array ProductFamilySpec) : Nat :=
  (families.toList.map fun family =>
    productFamilyDiagnosticBound T family.dimensionThings.size family.typeThings.size + 3).sum

/-- The registry bound depends only on the record count and total slot counts.
Redistributing slots between records does not change this bound. These totals
are independent of the thing count, even for malformed input records. -/
theorem productFamiliesDiagnosticBound_eq_sizes (T : Nat) (families : Array ProductFamilySpec) :
    productFamiliesDiagnosticBound T families =
      (31 * T + 43) * (families.toList.map fun f => f.dimensionThings.size).sum +
      (4 * T + 4) * (families.toList.map fun f => f.typeThings.size).sum +
      (30 * T + 19) * families.size := by
  have sum_formula (fs : List ProductFamilySpec) :
      (fs.map fun f => productFamilyDiagnosticBound T f.dimensionThings.size f.typeThings.size + 3).sum =
        (31 * T + 43) * (fs.map fun f => f.dimensionThings.size).sum +
        (4 * T + 4) * (fs.map fun f => f.typeThings.size).sum +
        (30 * T + 19) * fs.length := by
    induction fs with
    | nil => simp
    | cons f fs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [ih]
      simp only [productFamilyDiagnosticBound, Nat.mul_add, Nat.add_mul,
        Nat.mul_left_comm T 31, Nat.mul_left_comm T 4, Nat.mul_comm T 15, Nat.mul_assoc,
        Nat.mul_one]
      omega
  simpa [productFamiliesDiagnosticBound] using sum_formula families.toList

/-- Size growth cannot reduce the upper bound. Actual execution can still
stop earlier after a new fact or a valid witness changes the answer. -/
theorem productFamiliesDiagnosticBound_mono {T T' : Nat}
    {families families' : Array ProductFamilySpec} (hT : T ≤ T')
    (hR : families.size ≤ families'.size)
    (hD : (families.toList.map fun f => f.dimensionThings.size).sum ≤
      (families'.toList.map fun f => f.dimensionThings.size).sum)
    (hZ : (families.toList.map fun f => f.typeThings.size).sum ≤
      (families'.toList.map fun f => f.typeThings.size).sum) :
    productFamiliesDiagnosticBound T families ≤ productFamiliesDiagnosticBound T' families' := by
  rw [productFamiliesDiagnosticBound_eq_sizes, productFamiliesDiagnosticBound_eq_sizes]
  repeat' first
    | assumption
    | exact Nat.le_refl _
    | apply Nat.add_le_add
    | apply Nat.mul_le_mul

theorem productFamiliesDiagnosticCosted_cost_le (W T : Nat) (tables : FactTables)
    (x t w : Nat) :
    (productFamiliesDiagnosticCosted W T tables x t w).cost ≤
      productFamiliesDiagnosticBound T tables.productFamilies := by
  unfold productFamiliesDiagnosticCosted
  rw [anyArrayCosted_eq_list]
  have h := anyListCosted_cost_le_sum tables.productFamilies.toList
    (fun family => Costed.charge 1 (productFamilyDiagnosticCosted W T tables x t w family))
    (fun family => productFamilyDiagnosticBound T family.dimensionThings.size family.typeThings.size + 1)
    (by
      intro family _
      have h := productFamilyDiagnosticCosted_cost_le W T tables x t w family
      simp only [Costed.charge_cost]
      omega)
  simpa [productFamiliesDiagnosticBound, Nat.add_assoc] using h

end LeanUfo.UFO.DSL.Complexity
