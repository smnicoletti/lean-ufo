import LeanUfo.UFO.DSL.Certificate.Reuse
import LeanUfo.UFO.DSL.Complexity.Compiler

/-!
# Operational costs of certificate reuse planning

Reuse planning compares source records and the ordered rows named by a field's
reuse footprint. A footprint lists the relations that the checker reads.
These comparisons only select a candidate parent proof. The generated checked
theorem still proves equality of the parent and child checker results.

The proofs compose the executed short-circuit comparisons, following Niu et al.
(POPL 2022, doi:10.1145/3498670). Map lookups use the compiler's abstract map
interface. They are counted, but no native hash-table or character-level bound
is claimed. See `docs/dsl/complexity.md` for the machine model.
-/

namespace LeanUfo.UFO.DSL.Complexity
open private pairEqCosted natPairEqCosted natTripleEqCosted natQuadEqCosted
  namedScopeEqCosted namedDerivedEqCosted namedFactEqCosted
  namedFamilyEqCosted familyEqCosted sameTableFieldsCosted
  from LeanUfo.UFO.DSL.Certificate.Reuse

private theorem pairEq_value [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (first : α → α → Costed Bool) (second : β → β → Costed Bool)
    (hf : ∀ a b, (first a b).value = (a == b))
    (hs : ∀ a b, (second a b).value = (a == b)) (a b : α × β) :
    (pairEqCosted first second a b).value = (a == b) := by
  cases a
  cases b
  apply Bool.eq_iff_iff.mpr
  simp [pairEqCosted, Costed.andThen_value, hf, hs, beq_iff_eq]

private theorem pairEq_cost_le (first : α → α → Costed Bool) (second : β → β → Costed Bool)
    (f s : Nat) (hf : ∀ a b, (first a b).cost ≤ f)
    (hs : ∀ a b, (second a b).cost ≤ s) (a b : α × β) :
    (pairEqCosted first second a b).cost ≤ f + 1 + s :=
  Costed.andThen_cost_le _ _ f s (hf _ _) (hs _ _)

private theorem natPairEq_value (a b : Nat × Nat) :
    (natPairEqCosted a b).value = (a == b) :=
  pairEq_value _ _ (by intros; rfl) (by intros; rfl) a b

private theorem natTripleEq_value (a b : Nat × Nat × Nat) :
    (natTripleEqCosted a b).value = (a == b) :=
  pairEq_value _ _ (by intros; rfl) natPairEq_value a b

private theorem natQuadEq_value (a b : Nat × Nat × Nat × Nat) :
    (natQuadEqCosted a b).value = (a == b) :=
  pairEq_value _ _ (by intros; rfl) natTripleEq_value a b

private theorem natPairEq_cost_le (a b : Nat × Nat) : (natPairEqCosted a b).cost ≤ 3 :=
  pairEq_cost_le _ _ 1 1 (by intros; rfl) (by intros; rfl) a b

private theorem natTripleEq_cost_le (a b : Nat × Nat × Nat) : (natTripleEqCosted a b).cost ≤ 5 :=
  pairEq_cost_le _ _ 1 3 (by intros; rfl) natPairEq_cost_le a b

private theorem natQuadEq_cost_le (a b : Nat × Nat × Nat × Nat) : (natQuadEqCosted a b).cost ≤ 7 :=
  pairEq_cost_le _ _ 1 5 (by intros; rfl) natTripleEq_cost_le a b

private theorem namedScopeEq_value (a b : NamedFactScope) :
    (namedScopeEqCosted a b).value = (a == b) := by
  cases a <;> cases b <;> apply Bool.eq_iff_iff.mpr <;>
    simp [namedScopeEqCosted, beq_iff_eq]

private theorem namedScopeEq_cost_le (a b : NamedFactScope) :
    (namedScopeEqCosted a b).cost ≤ 2 := by
  cases a <;> cases b <;> simp [namedScopeEqCosted, Costed.charge]

private theorem namedDerivedEq_value (a b : NamedDerivedFact) :
    (namedDerivedEqCosted a b).value = (a == b) := by
  cases a <;> cases b <;> apply Bool.eq_iff_iff.mpr <;>
    simp [namedDerivedEqCosted, Costed.andThen_value, beq_iff_eq]

private theorem namedDerivedEq_cost_le (a b : NamedDerivedFact) :
    (namedDerivedEqCosted a b).cost ≤ 10 := by
  cases a <;> cases b <;>
    simp only [namedDerivedEqCosted, Costed.charge_cost, Costed.tick_cost]
  all_goals try omega
  all_goals simp only [Costed.andThen, Costed.tick]
  all_goals repeat' (first | omega | (split_ifs <;> simp_all))

private theorem binaryField_beq_iff (a b : BinaryField) : (a == b) = true ↔ a = b := by
  cases a <;> cases b <;> decide

private theorem ternaryField_beq_iff (a b : TernaryField) : (a == b) = true ↔ a = b := by
  cases a <;> cases b <;> decide

private theorem namedFactEq_value (a b : NamedScopedFact) :
    (namedFactEqCosted a b).value = (a == b) := by
  cases a <;> cases b <;> apply Bool.eq_iff_iff.mpr <;>
    simp [namedFactEqCosted, Costed.andThen_value, namedScopeEq_value,
      namedDerivedEq_value, beq_iff_eq, binaryField_beq_iff, ternaryField_beq_iff]

private theorem namedFactEq_cost_le (a b : NamedScopedFact) :
    (namedFactEqCosted a b).cost ≤ 14 := by
  cases a <;> cases b <;>
    simp only [namedFactEqCosted, Costed.charge_cost, Costed.tick_cost]
  all_goals try omega
  case unary.unary af ax asc bf bx bsc =>
    have hs := namedScopeEq_cost_le asc bsc
    simp only [Costed.andThen, Costed.tick]
    all_goals repeat' (first | omega | (split_ifs <;> simp_all))
  case binary.binary af ax ay asc bf bx byy bsc =>
    have hs := namedScopeEq_cost_le asc bsc
    simp only [Costed.andThen, Costed.tick]
    all_goals repeat' (first | omega | (split_ifs <;> simp_all))
  case ternary.ternary af ax ay az asc bf bx byy bz bsc =>
    have hs := namedScopeEq_cost_le asc bsc
    simp only [Costed.andThen, Costed.tick]
    all_goals repeat' (first | omega | (split_ifs <;> simp_all))
  case tupleProjection.tupleProjection ax ai ar asc bx bi br bsc =>
    have hs := namedScopeEq_cost_le asc bsc
    simp only [Costed.andThen, Costed.tick]
    all_goals repeat' (first | omega | (split_ifs <;> simp_all))
  case derived.derived af asc bf bsc =>
    have hs := namedScopeEq_cost_le asc bsc
    have hd := namedDerivedEq_cost_le af bf
    simp only [Costed.andThen]
    all_goals repeat' (first | omega | (split_ifs <;> simp_all))

private theorem namedFamilyEq_value (a b : NamedProductFamily) :
    (namedFamilyEqCosted a b).value = (a == b) := by
  cases a
  cases b
  apply Bool.eq_iff_iff.mpr
  simp [namedFamilyEqCosted, Costed.andThen_value,
    arrayEqCosted_value _ _ (fun (x y : String) => Costed.tick (x == y)) (by intros; rfl),
    beq_iff_eq, NamedProductFamily.mk.injEq]

private theorem namedFamilyEq_cost_le (a b : NamedProductFamily) :
    (namedFamilyEqCosted a b).cost ≤ 9 + 5 * (a.dimensionThings.size + a.typeThings.size) := by
  have hd := arrayEqCosted_cost_le a.dimensionThings b.dimensionThings
    (fun x y => Costed.tick (x == y)) 1 (by intros; rfl)
  have ht := arrayEqCosted_cost_le a.typeThings b.typeThings
    (fun x y => Costed.tick (x == y)) 1 (by intros; rfl)
  simp only [namedFamilyEqCosted, Costed.andThen, Costed.tick]
  simp only [Costed.tick] at hd ht
  all_goals repeat' (first | omega | (split_ifs <;> simp_all))

private theorem familyEq_value (a b : ProductFamilySpec) :
    (familyEqCosted a b).value = (a == b) := by
  cases a
  cases b
  apply Bool.eq_iff_iff.mpr
  simp [familyEqCosted, Costed.andThen_value,
    arrayEqCosted_value _ _ (fun (x y : Nat) => Costed.tick (x == y)) (by intros; rfl),
    beq_iff_eq, ProductFamilySpec.mk.injEq]

private theorem familyEq_cost_le (a b : ProductFamilySpec) :
    (familyEqCosted a b).cost ≤ 9 + 5 * (a.dimensionThings.size + a.typeThings.size) := by
  have hd := arrayEqCosted_cost_le a.dimensionThings b.dimensionThings
    (fun x y => Costed.tick (x == y)) 1 (by intros; rfl)
  have ht := arrayEqCosted_cost_le a.typeThings b.typeThings
    (fun x y => Costed.tick (x == y)) 1 (by intros; rfl)
  simp only [familyEqCosted, Costed.andThen, Costed.tick]
  simp only [Costed.tick] at hd ht
  all_goals repeat' (first | omega | (split_ifs <;> simp_all))

/-- The source shortcut preserves all fields, array order, and duplicates. -/
theorem modelSourceEq_value (a b : ModelSource) :
    (modelSourceEqCosted a b).value = (a == b) := by
  cases a
  cases b
  apply Bool.eq_iff_iff.mpr
  simp [modelSourceEqCosted, Costed.andThen_value,
    arrayEqCosted_value _ _ (fun (x y : String) => Costed.tick (x == y)) (by intros; rfl),
    arrayEqCosted_value _ _ _ namedFactEq_value,
    arrayEqCosted_value _ _ _ namedFamilyEq_value, beq_iff_eq, ModelSource.mk.injEq]

private theorem sum_affine (xs : List α) (f : α → Nat) (constant factor : Nat) :
    (xs.map (fun x => constant + factor * f x)).sum =
      constant * xs.length + factor * (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, ih, Nat.mul_add]
      omega

/-- Source equality is linear in names, facts, families, and their slots.
The left input supplies the sizes: a length mismatch returns immediately. -/
theorem modelSourceEq_cost_le (a b : ModelSource) :
    (modelSourceEqCosted a b).cost ≤
      13 + 5 * (sourceMetrics a).worlds + 5 * (sourceMetrics a).things +
        18 * (sourceMetrics a).facts + 13 * (sourceMetrics a).productFamilies +
        5 * (sourceMetrics a).productFamilySlots := by
  have hw := arrayEqCosted_cost_le a.worlds b.worlds
    (fun x y => Costed.tick (x == y)) 1 (by intros; rfl)
  have ht := arrayEqCosted_cost_le a.things b.things
    (fun x y => Costed.tick (x == y)) 1 (by intros; rfl)
  have hf := arrayEqCosted_cost_le a.facts b.facts namedFactEqCosted 14 namedFactEq_cost_le
  have hp := arrayEqCosted_cost_le_sum a.productFamilies b.productFamilies namedFamilyEqCosted
    (fun p => 9 + 5 * p.slotCount) namedFamilyEq_cost_le
  have hslots : (a.productFamilies.toList.map (fun p => 9 + 5 * p.slotCount + 4)).sum =
      13 * a.productFamilies.size + 5 * (sourceMetrics a).productFamilySlots := by
    simpa only [sourceMetrics, Array.length_toList, Nat.add_right_comm] using
      sum_affine a.productFamilies.toList NamedProductFamily.slotCount 13 5
  rw [hslots] at hp
  simp only [sourceMetrics, Costed.tick] at hw ht hf hp ⊢
  simp only [modelSourceEqCosted, Costed.andThen, Costed.tick]
  all_goals repeat' (first | omega | (split_ifs <;> simp_all))

/-- The scalar input size includes every component used by source equality. -/
theorem modelSourceEq_scalar_bound (a b : ModelSource) :
    (modelSourceEqCosted a b).cost ≤ 18 * (sourceMetrics a).inputSize := by
  have h := modelSourceEq_cost_le a b
  simp only [SourceMetrics.inputSize]
  omega

private theorem sameTableFields_value [BEq α] [LawfulBEq α]
    (fields : Array String) (left right : Std.HashMap String (Array α))
    (compare : α → α → Costed Bool) (hc : ∀ a b, (compare a b).value = (a == b)) :
    (sameTableFieldsCosted fields left right compare).value =
      fields.all (fun field => left.getD field #[] == right.getD field #[]) := by
  simp [sameTableFieldsCosted, allArrayCosted_value, Bind.bind,
    arrayEqCosted_value _ _ compare hc]

/-- Each named table uses two abstract map reads; each visited row is compared
coordinate by coordinate. The sum includes repeated names in the footprint. -/
private theorem sameTableFields_cost_le (fields : Array String)
    (left right : Std.HashMap String (Array α)) (compare : α → α → Costed Bool)
    (k : Nat) (hc : ∀ a b, (compare a b).cost ≤ k) :
    (sameTableFieldsCosted fields left right compare).cost ≤
      (fields.toList.map (fun field => 7 + (k + 4) * (left.getD field #[]).size)).sum := by
  have h := allArrayCosted_cost_le_sum fields
    (fun field => do
      let a ← Costed.tick (left.getD field #[])
      let b ← Costed.tick (right.getD field #[])
      arrayEqCosted a b compare)
    (fun field => 4 + (k + 4) * (left.getD field #[]).size) (by
      intro field _
      have h := arrayEqCosted_cost_le (left.getD field #[]) (right.getD field #[]) compare k hc
      rw [Nat.mul_comm] at h
      simp only [Bind.bind, Costed.bind_cost, Costed.tick_cost, Costed.tick_value]
      omega)
  simpa only [sameTableFieldsCosted, Nat.add_right_comm] using h

theorem sameUnaryFootprint_value (fields : Array String) (left right : FactTables) :
    sameUnaryFootprint fields left right =
      fields.all (fun field => left.unary.getD field #[] == right.unary.getD field #[]) :=
  sameTableFields_value _ _ _ _ natPairEq_value

theorem sameBinaryFootprint_value (fields : Array String) (left right : FactTables) :
    sameBinaryFootprint fields left right =
      fields.all (fun field => left.binary.getD field #[] == right.binary.getD field #[]) :=
  sameTableFields_value _ _ _ _ natTripleEq_value

theorem sameTernaryFootprint_value (fields : Array String) (left right : FactTables) :
    sameTernaryFootprint fields left right =
      fields.all (fun field => left.ternary.getD field #[] == right.ternary.getD field #[]) :=
  sameTableFields_value _ _ _ _ natQuadEq_value

/-- The counted footprint check preserves the former ordered-table policy.
An unused projection or family component is not evaluated. -/
theorem footprintUnchanged_value (fp : ReusableFieldFootprint) (left right : FactTables) :
    footprintUnchanged fp left right =
      (sameUnaryFootprint fp.unary left right &&
        sameBinaryFootprint fp.binary left right &&
        sameTernaryFootprint fp.ternary left right &&
        (!fp.tupleProjection || left.tupleProjection == right.tupleProjection) &&
        (!fp.productFamilies || left.productFamilies == right.productFamilies)) := by
  simp only [footprintUnchanged, footprintUnchangedCosted, Costed.andThen_value,
    Costed.branch_value, Costed.pure_value,
    arrayEqCosted_value _ _ _ natQuadEq_value, arrayEqCosted_value _ _ _ familyEq_value]
  cases fp.tupleProjection <;> cases fp.productFamilies <;>
    simp [sameUnaryFootprint, sameBinaryFootprint, sameTernaryFootprint, Bool.and_assoc]

/-- Bound for one footprint in the stored parent tables. Relation-name lists
may repeat a table; each such visit is included. Projection rows and family
slots are included even when their optional comparison is skipped. -/
def reuseFootprintCostBound (fp : ReusableFieldFootprint) (tables : FactTables) : Nat :=
  10 +
    (fp.unary.toList.map (fun f => 7 + 7 * (tables.unary.getD f #[]).size)).sum +
    (fp.binary.toList.map (fun f => 7 + 9 * (tables.binary.getD f #[]).size)).sum +
    (fp.ternary.toList.map (fun f => 7 + 11 * (tables.ternary.getD f #[]).size)).sum +
    11 * tables.tupleProjection.size +
    (tables.productFamilies.toList.map
      (fun p => 13 + 5 * (p.dimensionThings.size + p.typeThings.size))).sum

theorem footprintUnchanged_cost_le (fp : ReusableFieldFootprint) (left right : FactTables) :
    (footprintUnchangedCosted fp left right).cost ≤ reuseFootprintCostBound fp left := by
  have hu := sameTableFields_cost_le fp.unary left.unary right.unary
    natPairEqCosted 3 natPairEq_cost_le
  have hb := sameTableFields_cost_le fp.binary left.binary right.binary
    natTripleEqCosted 5 natTripleEq_cost_le
  have ht := sameTableFields_cost_le fp.ternary left.ternary right.ternary
    natQuadEqCosted 7 natQuadEq_cost_le
  have hp := arrayEqCosted_cost_le left.tupleProjection right.tupleProjection
    natQuadEqCosted 7 natQuadEq_cost_le
  have hf := arrayEqCosted_cost_le_sum left.productFamilies right.productFamilies
    familyEqCosted (fun p => 9 + 5 * (p.dimensionThings.size + p.typeThings.size)) familyEq_cost_le
  change (sameUnaryFootprintCosted fp.unary left right).cost ≤ _ at hu
  change (sameBinaryFootprintCosted fp.binary left right).cost ≤ _ at hb
  change (sameTernaryFootprintCosted fp.ternary left right).cost ≤ _ at ht
  simp only [Nat.add_right_comm] at hf
  simp only [footprintUnchangedCosted, reuseFootprintCostBound, Costed.andThen,
    Costed.branch, Costed.pure]
  all_goals repeat' (first | omega | (split_ifs <;> simp_all))

private theorem firstMatch_fold (xs : List α) (p : α → Bool) :
    (match xs.foldlM (fun (_ : Unit) x =>
      ((if p x then .error x else .ok ()) : Except α Unit)) () with
      | .error x => some x | .ok _ => none) = xs.find? p := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases h : p x <;>
        simp [List.foldlM_cons, h, Bind.bind, Except.bind, ih]

/-- Registry lookup returns the first matching footprint, as before. -/
theorem reusableFieldFootprint_value (field : String) :
    (reusableFieldFootprintCosted field).value =
      reusableFieldFootprints.find? (fun fp => fp.field == field) := by
  simp only [reusableFieldFootprintCosted, Costed.charge_value, Costed.map_value,
    Costed.foldArrayExcept_value, Costed.tick_value, ← Array.foldlM_toList]
  have h := firstMatch_fold reusableFieldFootprints.toList (fun fp => fp.field == field)
  rw [Array.find?_toList] at h
  cases he : reusableFieldFootprints.toList.foldlM
      (fun (_ : Unit) fp => ((if fp.field == field then .error fp else .ok ()) :
        Except ReusableFieldFootprint Unit)) () <;>
    simpa only [he] using h

theorem reusableFieldFootprint_cost_le (field : String) :
    (reusableFieldFootprintCosted field).cost ≤ 4 * reusableFieldFootprints.size + 1 := by
  have h := Costed.foldArrayExcept_cost_le reusableFieldFootprints ()
    (fun _ fp => Costed.tick (if fp.field == field then .error fp else .ok ()) 2)
    2 (by intros; rfl)
  simp only [reusableFieldFootprintCosted, Costed.charge_cost, Costed.map_cost]
  omega

/-- Missing registry fields reject reuse. A matching field uses the same
footprint comparison policy as the uninstrumented planner. -/
theorem fieldFootprintReusable_value (field : String) (left right : FactTables) :
    fieldFootprintReusable field left right =
      match reusableFieldFootprints.find? (fun fp => fp.field == field) with
      | none => false
      | some fp => footprintUnchanged fp left right := by
  simp only [fieldFootprintReusable, fieldFootprintReusableCosted, Bind.bind,
    Costed.bind_value, reusableFieldFootprint_value]
  split <;> rename_i h <;>
    simp only [h, Costed.tick_value, Costed.charge_value, footprintUnchanged]

/-- Erasing the planner preserves fresh mode, the source-equality shortcut,
and the footprint fallback. A candidate is not itself a certificate. -/
theorem certificateReuseSource_value (parentName : Lean.Name)
    (parentSource childSource : ModelSource) (parentTables childTables : FactTables)
    (fresh : Bool) (field : String) :
    certificateReuseSource? parentName parentSource childSource parentTables childTables fresh field =
      if fresh then none else
      if childSource == parentSource || fieldFootprintReusable field parentTables childTables
      then some parentName else none := by
  simp [certificateReuseSource?, certificateReuseSourceCosted, Costed.branch_value,
    Bind.bind, Costed.orElse_value, modelSourceEq_value, fieldFootprintReusable]

private theorem member_le_sum (xs : List α) (f : α → Nat) (x : α) (hx : x ∈ xs) :
    f x ≤ (xs.map f).sum := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
      simp only [List.mem_cons] at hx
      simp only [List.map_cons, List.sum_cons]
      rcases hx with rfl | hx
      · omega
      · have := ih hx; omega

/-- A field search and at most one table footprint check. The registry sum
is a conservative size bound; it is not charged as executed work. -/
theorem fieldFootprintReusable_cost_le (field : String) (left right : FactTables) :
    (fieldFootprintReusableCosted field left right).cost ≤
      4 * reusableFieldFootprints.size + 2 +
        (reusableFieldFootprints.toList.map (fun fp => reuseFootprintCostBound fp left)).sum := by
  have hl := reusableFieldFootprint_cost_le field
  simp only [fieldFootprintReusableCosted, Bind.bind, Costed.bind_cost]
  cases h : (reusableFieldFootprintCosted field).value with
  | none => simp only [Costed.tick_cost]; omega
  | some fp =>
      have hm : fp ∈ reusableFieldFootprints :=
        Array.mem_of_find?_eq_some (by rwa [reusableFieldFootprint_value] at h)
      have hs := member_le_sum reusableFieldFootprints.toList
        (fun fp => reuseFootprintCostBound fp left) fp (by simpa using hm)
      have hc := footprintUnchanged_cost_le fp left right
      simp only [Costed.charge_cost]
      omega

/-- Bound for the executed reuse planner. Source sizes come from the child;
table-row and slot sizes come from the parent. Early exits can reduce the
actual count but cannot increase this bound. -/
theorem certificateReuseSource_cost_le (parentName : Lean.Name)
    (parentSource childSource : ModelSource) (parentTables childTables : FactTables)
    (fresh : Bool) (field : String) :
    (certificateReuseSourceCosted parentName parentSource childSource parentTables childTables fresh field).cost ≤
      18 + 5 * (sourceMetrics childSource).worlds + 5 * (sourceMetrics childSource).things +
        18 * (sourceMetrics childSource).facts + 13 * (sourceMetrics childSource).productFamilies +
        5 * (sourceMetrics childSource).productFamilySlots +
        4 * reusableFieldFootprints.size +
        (reusableFieldFootprints.toList.map (fun fp => reuseFootprintCostBound fp parentTables)).sum := by
  have hs := modelSourceEq_cost_le childSource parentSource
  have hf := fieldFootprintReusable_cost_le field parentTables childTables
  simp only [certificateReuseSourceCosted, Costed.branch, Costed.pure, Bind.bind,
    Costed.orElse]
  all_goals repeat' (first | omega | (split_ifs <;> simp_all))

private theorem rowBudget_le (fields : Array String) (rows : Std.HashMap String (Array α))
    (k n : Nat) (bounded : ∀ field, (rows.getD field #[]).size ≤ n) :
    (fields.toList.map (fun f => 7 + k * (rows.getD f #[]).size)).sum ≤
      fields.size * (7 + k * n) := by
  have aux (xs : List String) :
      (xs.map (fun f => 7 + k * (rows.getD f #[]).size)).sum ≤ xs.length * (7 + k * n) := by
    induction xs with
    | nil => simp
    | cons f fs ih =>
        have h := Nat.mul_le_mul_left k (bounded f)
        simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
        omega
  simpa only [Array.length_toList] using aux fields.toList

/-- Reuse reads the compiler's stored rows, not arbitrary tables of an
independently supplied size. Source success bounds each row array by expanded
facts and preserves the number of family records and both slot arrays. -/
theorem reuseFootprintCostBound_le_sourceMetrics (fp : ReusableFieldFootprint)
    (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled) :
    reuseFootprintCostBound fp compiled.tables ≤
      10 + fp.unary.size * (7 + 7 * (sourceMetrics source).specializationFactsUpper) +
        fp.binary.size * (7 + 9 * (sourceMetrics source).specializationFactsUpper) +
        fp.ternary.size * (7 + 11 * (sourceMetrics source).specializationFactsUpper) +
        11 * (sourceMetrics source).specializationFactsUpper +
        13 * (sourceMetrics source).productFamilies + 5 * (sourceMetrics source).productFamilySlots := by
  rcases compiledRowSizes_le_sourceMetrics source compiled success with ⟨hu, hb, ht, hp⟩
  have u := rowBudget_le fp.unary compiled.tables.unary 7 _ hu
  have b := rowBudget_le fp.binary compiled.tables.binary 9 _ hb
  have t := rowBudget_le fp.ternary compiled.tables.ternary 11 _ ht
  have families := compileModelSource_ok_tableFamilies source compiled success
  obtain ⟨count, slots⟩ := compileModelSource_ok_familySizes source compiled success
  have familyBudget :
      (compiled.tables.productFamilies.toList.map
        (fun p => 13 + 5 * (p.dimensionThings.size + p.typeThings.size))).sum =
      13 * (sourceMetrics source).productFamilies + 5 * (sourceMetrics source).productFamilySlots := by
    rw [families, sum_affine]
    simp only [Array.length_toList, count, slots, sourceMetrics]
  unfold reuseFootprintCostBound
  rw [familyBudget]
  omega

/-- Linear bound for one footprint in a successfully compiled source. The
coefficient counts repeated relation names in the footprint; `N` includes
expanded facts, family records, and all slots. -/
theorem reuseFootprint_source_scalar_bound (fp : ReusableFieldFootprint)
    (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled) :
    reuseFootprintCostBound fp compiled.tables ≤
      (39 + 18 * (fp.unary.size + fp.binary.size + fp.ternary.size)) *
        (sourceMetrics source).inputSize := by
  have bound := reuseFootprintCostBound_le_sourceMetrics fp source compiled success
  have pos := sourceMetrics_inputSize_pos source
  have facts : (sourceMetrics source).specializationFactsUpper ≤ (sourceMetrics source).inputSize := by
    simp only [SourceMetrics.inputSize]; omega
  have families : (sourceMetrics source).productFamilies ≤ (sourceMetrics source).inputSize := by
    simp only [SourceMetrics.inputSize]; omega
  have slots : (sourceMetrics source).productFamilySlots ≤ (sourceMetrics source).inputSize := by
    simp only [SourceMetrics.inputSize]; omega
  have u := Nat.mul_le_mul_left fp.unary.size
    (show 7 + 7 * (sourceMetrics source).specializationFactsUpper ≤
      18 * (sourceMetrics source).inputSize by omega)
  have b := Nat.mul_le_mul_left fp.binary.size
    (show 7 + 9 * (sourceMetrics source).specializationFactsUpper ≤
      18 * (sourceMetrics source).inputSize by omega)
  have t := Nat.mul_le_mul_left fp.ternary.size
    (show 7 + 11 * (sourceMetrics source).specializationFactsUpper ≤
      18 * (sourceMetrics source).inputSize by omega)
  rw [Nat.mul_left_comm fp.unary.size 18] at u
  rw [Nat.mul_left_comm fp.binary.size 18] at b
  rw [Nat.mul_left_comm fp.ternary.size 18] at t
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc] at u b t bound ⊢
  omega

/-- The fixed registry has 113 rows and 328 relation-name occurrences.
The coefficient sums `39 + 18D` for each row with `D` relation names.
This closed arithmetic fact is checked by the kernel, without native decision. -/
private theorem reuseRegistry_source_coefficient :
    (reusableFieldFootprints.toList.map (fun fp =>
      39 + 18 * (fp.unary.size + fp.binary.size + fp.ternary.size))).sum = 10311 := by
  decide

/-- A source-linked bound for the production reuse planner: `18C + 11023P`,
where `C` and `P` are the complete child and parent source sizes. Parent
compilation supplies the rows and family slots that the fallback scans.
The child table sizes need no separate bound: unequal lengths stop comparison. -/
theorem certificateReuseSource_source_bound (parentName : Lean.Name)
    (parentSource childSource : ModelSource) (parent : CompiledModelSource)
    (childTables : FactTables) (fresh : Bool) (field : String)
    (success : compileModelSource parentSource = .ok parent) :
    (certificateReuseSourceCosted parentName parentSource childSource parent.tables childTables fresh field).cost ≤
      18 * (sourceMetrics childSource).inputSize + 11023 * (sourceMetrics parentSource).inputSize := by
  have allRows (rows : List ReusableFieldFootprint) :
      (rows.map (fun fp => reuseFootprintCostBound fp parent.tables)).sum ≤
        (rows.map (fun fp => 39 + 18 * (fp.unary.size + fp.binary.size + fp.ternary.size))).sum *
          (sourceMetrics parentSource).inputSize := by
    induction rows with
    | nil => simp
    | cons fp rows ih =>
        have h := reuseFootprint_source_scalar_bound fp parentSource parent success
        simp only [Nat.add_mul] at h
        simp only [List.map_cons, List.sum_cons, Nat.add_mul]
        omega
  have rows := allRows reusableFieldFootprints.toList
  rw [reuseRegistry_source_coefficient] at rows
  have count : reusableFieldFootprints.size = 113 := by decide
  have footprint := fieldFootprintReusable_cost_le field parent.tables childTables
  rw [count] at footprint
  have pos := sourceMetrics_inputSize_pos parentSource
  have hf : (fieldFootprintReusableCosted field parent.tables childTables).cost ≤
      11020 * (sourceMetrics parentSource).inputSize := by omega
  have hs := modelSourceEq_scalar_bound childSource parentSource
  simp only [certificateReuseSourceCosted, Costed.branch, Costed.pure, Bind.bind, Costed.orElse]
  all_goals repeat' (first | omega | (split_ifs <;> simp_all))

/-- The size bound is monotone even when a larger input causes earlier exit. -/
theorem certificateReuseSource_bound_mono {C C' P P' : Nat} (child : C ≤ C') (parent : P ≤ P') :
    18 * C + 11023 * P ≤ 18 * C' + 11023 * P' := by omega

end LeanUfo.UFO.DSL.Complexity
