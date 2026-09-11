import LeanUfo.UFO.DSL.FiniteModel
import LeanUfo.UFO.DSL.Compiler.AST
import LeanUfo.UFO.DSL.Complexity.CostModel

/-!
# Counted conversion of product-family witnesses

The finite model stores bounded coordinates (`Fin`) where the resolved source
stores natural numbers. Conversion rejects invalid coordinates and unequal
witness-array lengths. Valid records retain family order and ascending world
order, including duplicates.

`ProductFamilySpec.WellFormed` states only coordinate and length conditions.
For such inputs, readback recovers each family and world exactly. The checker
must separately establish the semantic relation conditions of axiom 99.

Validation stops at the first failed field. Array traversal continues after a
failed element, but performs no further coordinate checks or writes. Conversion
is repeated for each world, so its bound includes both witness-array lengths
multiplied by the world count. Value proofs compare the counted computation with
cost-free specifications. This separates cost instrumentation from results,
following the cost-aware semantics approach of Niu et al. (POPL 2022),
doi:10.1145/3498670. String characters and allocation are outside this model.
-/

namespace LeanUfo.UFO.DSL

/-- Read back a witness's natural-number coordinates for correspondence proofs.
The source family applies in every world, so this record omits the world; a
readback theorem must retain or state the witness's world separately. -/
def ProductFamilyWitness.toSpec {T W : Nat} (witness : ProductFamilyWitness T W) : ProductFamilySpec :=
  { domain := witness.domain.val
    qualityType := witness.qualityType.val
    dimensionThings := witness.dimensionThings.map Fin.val
    typeThings := witness.typeThings.map Fin.val }

namespace FactTables

open Complexity

private def natToFinSpec (n x : Nat) : Option (Fin n) :=
  if h : x < n then some ⟨x, h⟩ else none

private def natToFinCosted (n x : Nat) : Costed (Option (Fin n)) :=
  .tick (if h : x < n then some ⟨x, h⟩ else none) 2

@[simp] private theorem natToFinCosted_value (n x : Nat) :
    (natToFinCosted n x).value = natToFinSpec n x := rfl

private def natArrayToFinArraySpec (n : Nat) (xs : Array Nat) : Option (Array (Fin n)) :=
  xs.foldl (fun acc? x =>
    match acc?, natToFinSpec n x with
    | some acc, some x => some (acc.push x)
    | _, _ => none) (some #[])

private def appendFiniteCoordinateCosted (n : Nat)
    (acc? : Option (Array (Fin n))) (x : Nat) : Costed (Option (Array (Fin n))) :=
  .charge 1 <| match acc? with
  | none => .pure none
  | some acc => (natToFinCosted n x).bind fun coordinate =>
      .charge 1 <| match coordinate with
      | none => .pure none
      | some value => .tick (some (acc.push value)) 1

private def natArrayToFinArrayCosted (n : Nat) (xs : Array Nat) :
    Costed (Option (Array (Fin n))) :=
  .charge 1 (Costed.foldArray xs (some #[]) (appendFiniteCoordinateCosted n))

@[simp] private theorem natArrayToFinArrayCosted_value (n : Nat) (xs : Array Nat) :
    (natArrayToFinArrayCosted n xs).value = natArrayToFinArraySpec n xs := by
  simp only [natArrayToFinArrayCosted, Costed.charge_value, Costed.foldArray_value,
    natArrayToFinArraySpec]
  congr 1
  funext acc x
  cases acc <;> simp [appendFiniteCoordinateCosted, natToFinCosted_value]
  cases natToFinSpec n x <;> rfl

/-- Each element charges a traversal/read pair and at most five callback
operations: accumulator test, comparison and branch, result test, and push.
The initial empty output array costs one, even when the input is empty. -/
private theorem natArrayToFinArrayCosted_cost_le (n : Nat) (xs : Array Nat) :
    (natArrayToFinArrayCosted n xs).cost ≤ 7 * xs.size + 1 := by
  have perStep (acc : Option (Array (Fin n))) (x : Nat) :
      (appendFiniteCoordinateCosted n acc x).cost ≤ 5 := by
    cases acc <;> simp [appendFiniteCoordinateCosted, natToFinCosted, Costed.tick]
    split <;> simp
  have bound := Costed.foldArray_cost_le xs (some #[]) (appendFiniteCoordinateCosted n)
    5 (fun acc x _ => perStep acc x)
  simp only [natArrayToFinArrayCosted, Costed.charge_cost]
  omega

/-- Bounded input cannot enter the failure branch. Reading the resulting
finite coordinates back as naturals recovers every input entry in order. -/
private theorem natArrayToFinArrayCosted_of_bounded (n : Nat) (xs : Array Nat)
    (bounded : ∀ x ∈ xs, x < n) :
    ∃ ys, (natArrayToFinArrayCosted n xs).value = some ys ∧ ys.map Fin.val = xs := by
  have foldBounded (items : List Nat) (acc : Array (Fin n))
      (valid : ∀ x ∈ items, x < n) :
      ∃ ys, items.foldl (fun acc? x =>
        match acc?, natToFinSpec n x with
        | some acc, some x => some (acc.push x)
        | _, _ => none) (some acc) = some ys ∧
          ys.map Fin.val = acc.map Fin.val ++ items.toArray := by
    induction items generalizing acc with
    | nil => exact ⟨acc, rfl, by simp⟩
    | cons x items ih =>
        have hx := valid x (by simp)
        obtain ⟨ys, result, readback⟩ := ih (acc.push ⟨x, hx⟩)
          (fun x member => valid x (by simp [member]))
        refine ⟨ys, ?_, ?_⟩
        · simpa only [List.foldl_cons, natToFinSpec, dif_pos hx] using result
        · apply Array.toList_inj.mp
          simpa [List.append_assoc] using congrArg Array.toList readback
  obtain ⟨ys, result, readback⟩ := foldBounded xs.toList #[]
    (fun x member => bounded x (by simpa using member))
  refine ⟨ys, ?_, ?_⟩
  · simpa only [natArrayToFinArrayCosted_value, natArrayToFinArraySpec,
      ← Array.foldl_toList] using result
  · simpa using readback

private def appendProductFamilySpec (W T : Nat) (family : ProductFamilySpec)
    (out : Array (ProductFamilyWitness T W)) (w : Nat) :
    Array (ProductFamilyWitness T W) :=
  match natToFinSpec T family.domain, natToFinSpec T family.qualityType,
      natToFinSpec W w, natArrayToFinArraySpec T family.dimensionThings,
      natArrayToFinArraySpec T family.typeThings with
  | some domain, some qualityType, some world, some dimensions, some types =>
      if h : dimensions.size = types.size then
        out.push
          { domain := domain
            qualityType := qualityType
            world := world
            dimensionThings := dimensions
            typeThings := types
            sameSize := h }
      else out
  | _, _, _, _, _ => out

/-- Nested binds make the validation order explicit. A failed field does not
evaluate later fields. The final six operations are two size reads, comparison,
branch, witness construction, and output push. -/
private def appendProductFamilyCosted (W T : Nat) (family : ProductFamilySpec)
    (out : Array (ProductFamilyWitness T W)) (w : Nat) :
    Costed (Array (ProductFamilyWitness T W)) :=
  (natToFinCosted T family.domain).bind fun domain? => .charge 1 <| match domain? with
  | none => .pure out
  | some domain =>
    (natToFinCosted T family.qualityType).bind fun qualityType? => .charge 1 <|
      match qualityType? with
      | none => .pure out
      | some qualityType =>
        (natToFinCosted W w).bind fun world? => .charge 1 <| match world? with
        | none => .pure out
        | some world =>
          (natArrayToFinArrayCosted T family.dimensionThings).bind fun dimensions? => .charge 1 <|
            match dimensions? with
            | none => .pure out
            | some dimensions =>
              (natArrayToFinArrayCosted T family.typeThings).bind fun types? => .charge 1 <|
                match types? with
                | none => .pure out
                | some types => .charge 4 <|
                    if h : dimensions.size = types.size then
                      .tick (out.push
                        { domain := domain
                          qualityType := qualityType
                          world := world
                          dimensionThings := dimensions
                          typeThings := types
                          sameSize := h }) 2
                    else .pure out

private theorem appendProductFamilyCosted_value (W T : Nat) (family : ProductFamilySpec)
    (out : Array (ProductFamilyWitness T W)) (w : Nat) :
    (appendProductFamilyCosted W T family out w).value = appendProductFamilySpec W T family out w := by
  simp only [appendProductFamilyCosted, Costed.bind_value, Costed.charge_value,
    natToFinCosted_value, appendProductFamilySpec]
  cases natToFinSpec T family.domain <;> simp
  cases natToFinSpec T family.qualityType <;> simp
  cases natToFinSpec W w <;> simp
  cases natArrayToFinArraySpec T family.dimensionThings <;> simp
  cases natArrayToFinArraySpec T family.typeThings <;> simp
  split <;> rfl

/-- A well-formed family emits one witness at the requested valid world.
Reading it back recovers the complete family, including array order. -/
private theorem appendProductFamilyCosted_readback (W T : Nat) (family : ProductFamilySpec)
    (valid : family.WellFormed T) (out : Array (ProductFamilyWitness T W))
    (w : Nat) (worldBound : w < W) :
    ((appendProductFamilyCosted W T family out w).value.map
      (fun witness => (witness.toSpec, witness.world.val))) =
      (out.map (fun witness => (witness.toSpec, witness.world.val))).push (family, w) := by
  obtain ⟨dimensions, dimensionsResult, dimensionsReadback⟩ :=
    natArrayToFinArrayCosted_of_bounded T family.dimensionThings valid.dimensions_lt
  obtain ⟨types, typesResult, typesReadback⟩ :=
    natArrayToFinArrayCosted_of_bounded T family.typeThings valid.types_lt
  have dimensionsSize : dimensions.size = family.dimensionThings.size := by
    simpa using congrArg Array.size dimensionsReadback
  have typesSize : types.size = family.typeThings.size := by
    simpa using congrArg Array.size typesReadback
  have sameSize : dimensions.size = types.size := by
    rw [dimensionsSize, typesSize, valid.sameSize]
  simp only [natArrayToFinArrayCosted_value] at dimensionsResult typesResult
  rw [appendProductFamilyCosted_value]
  simp [appendProductFamilySpec, natToFinSpec, valid.domain_lt, valid.qualityType_lt,
    worldBound, dimensionsResult, typesResult, sameSize, ProductFamilyWitness.toSpec,
    dimensionsReadback, typesReadback]

private theorem appendProductFamilyCosted_cost_le (W T : Nat) (family : ProductFamilySpec)
    (out : Array (ProductFamilyWitness T W)) (w : Nat) :
    (appendProductFamilyCosted W T family out w).cost ≤
      7 * (family.dimensionThings.size + family.typeThings.size) + 19 := by
  have dimensions := natArrayToFinArrayCosted_cost_le T family.dimensionThings
  have types := natArrayToFinArrayCosted_cost_le T family.typeThings
  simp only [appendProductFamilyCosted, Costed.bind_cost, Costed.charge_cost]
  simp only [natToFinCosted, Costed.tick_value, Costed.tick_cost]
  repeat' first | split | simp only [Costed.pure_cost, Costed.tick_cost,
    Costed.bind_cost, Costed.charge_cost]
  all_goals omega

/-- Each family is converted once per world. Empty world domains skip all
validation, while the outer array traversal still visits each family. -/
def productFamilyWitnessesCosted (W T : Nat) (families : Array ProductFamilySpec) :
    Costed (Array (ProductFamilyWitness T W)) :=
  .charge 1 <| Costed.foldArray families #[] fun out family =>
    Costed.foldFin W out fun out w => appendProductFamilyCosted W T family out w.val

def productFamilyWitnesses (W T : Nat) (families : Array ProductFamilySpec) :
    Array (ProductFamilyWitness T W) := (productFamilyWitnessesCosted W T families).value

private def productFamilyWitnessesSpec (W T : Nat) (families : Array ProductFamilySpec) :
    Array (ProductFamilyWitness T W) := Id.run do
  let mut out := #[]
  for family in families do
    for w in [:W] do
      out := appendProductFamilySpec W T family out w
  return out

private theorem foldFin_eq_range_foldl (n : Nat) (initial : α) (step : α → Nat → α) :
    Fin.foldl n (fun out i => step out i.val) initial = (List.range n).foldl step initial := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simpa [Fin.foldl_succ_last, List.range_succ, List.foldl_append] using
        congrArg (fun out => step out n) ih

/-- The specification retains the original nested loops and validation result.
The equality includes malformed families, duplicates, empty inputs, and order. -/
theorem productFamilyWitnessesCosted_value (W T : Nat) (families : Array ProductFamilySpec) :
    (productFamilyWitnessesCosted W T families).value = productFamilyWitnessesSpec W T families := by
  simp only [productFamilyWitnessesCosted, Costed.charge_value, Costed.foldArray_value,
    Costed.foldFin_value, appendProductFamilyCosted_value, foldFin_eq_range_foldl]
  simp [productFamilyWitnessesSpec, Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl, Array.forIn_pure_yield_eq_foldl, List.range_eq_range']

/-- Reading back a well-formed registry gives exactly its family/world pairs.
This equality preserves order and duplicates and proves that no valid family
is lost. The list on the right is a specification, not a runtime traversal. -/
theorem productFamilyWitnessesCosted_readback (W T : Nat) (families : Array ProductFamilySpec)
    (valid : ∀ family ∈ families, family.WellFormed T) :
    ((productFamilyWitnessesCosted W T families).value.map
      (fun witness => (witness.toSpec, witness.world.val))) =
      (families.toList.flatMap (fun family =>
        (List.range W).map (fun world => (family, world)))).toArray := by
  let readback (witness : ProductFamilyWitness T W) := (witness.toSpec, witness.world.val)
  have worldsReadback (family : ProductFamilySpec) (familyValid : family.WellFormed T)
      (worlds : List Nat) (out : Array (ProductFamilyWitness T W))
      (worldsValid : ∀ w ∈ worlds, w < W) :
      (worlds.foldl (fun out w => (appendProductFamilyCosted W T family out w).value) out).map
        readback = out.map readback ++ (worlds.map (fun w => (family, w))).toArray := by
    induction worlds generalizing out with
    | nil => simp
    | cons w worlds ih =>
        simp only [List.foldl_cons]
        rw [ih _ (fun w member => worldsValid w (by simp [member]))]
        rw [appendProductFamilyCosted_readback W T family familyValid out w
          (worldsValid w (by simp))]
        apply Array.toList_inj.mp
        simp [readback]
  have familyReadback (items : List ProductFamilySpec) (out : Array (ProductFamilyWitness T W))
      (itemsValid : ∀ family ∈ items, family.WellFormed T) :
      (items.foldl (fun out family =>
        (Costed.foldFin W out fun out w => appendProductFamilyCosted W T family out w.val).value)
        out).map readback = out.map readback ++
          (items.flatMap (fun family => (List.range W).map (fun w => (family, w)))).toArray := by
    induction items generalizing out with
    | nil => simp
    | cons family items ih =>
        simp only [List.foldl_cons]
        rw [ih _ (fun family member => itemsValid family (by simp [member]))]
        rw [Costed.foldFin_value,
          foldFin_eq_range_foldl W out (fun state world =>
            (appendProductFamilyCosted W T family state world).value),
          worldsReadback family (itemsValid family (by simp)) _ _
            (by intro w member; simpa using member)]
        apply Array.toList_inj.mp
        simp
  simpa only [productFamilyWitnessesCosted, Costed.charge_value, Costed.foldArray_value,
    ← Array.foldl_toList, Array.map_empty, Array.empty_append, readback] using
    familyReadback families.toList #[] (fun family member => valid family (by simpa using member))

/-- Add the per-family world traversal and the outer array traversal. The sum
keeps the two witness-array lengths independent of the number of things. -/
theorem productFamilyWitnessesCosted_cost_le (W T : Nat) (families : Array ProductFamilySpec) :
    (productFamilyWitnessesCosted W T families).cost ≤
      1 + (families.toList.map (fun family =>
        W * (7 * (family.dimensionThings.size + family.typeThings.size) + 20) + 2)).sum := by
  have bound := Costed.foldArray_cost_le_sum families #[]
    (fun out family => Costed.foldFin W out fun out w =>
      appendProductFamilyCosted W T family out w.val)
    (fun family => W * (7 * (family.dimensionThings.size + family.typeThings.size) + 20))
    (by
      intro out family _
      exact Costed.foldFin_cost_le W out _
        (7 * (family.dimensionThings.size + family.typeThings.size) + 19)
        (fun out w => appendProductFamilyCosted_cost_le W T family out w.val))
  exact Nat.add_le_add_left bound 1

/-- A multivariate bound in worlds, family count, and total stored witness
slots. The thing count affects validation results but not its unit-cost bound. -/
theorem productFamilyWitnessesCosted_cost_le_slots
    (W T : Nat) (families : Array ProductFamilySpec) :
    (productFamilyWitnessesCosted W T families).cost ≤
      1 + W * (7 * (families.toList.map (fun family =>
        family.dimensionThings.size + family.typeThings.size)).sum + 20 * families.size) +
        2 * families.size := by
  have sumEq (items : List ProductFamilySpec) :
      (items.map (fun family =>
        W * (7 * (family.dimensionThings.size + family.typeThings.size) + 20) + 2)).sum =
      W * (7 * (items.map (fun family =>
        family.dimensionThings.size + family.typeThings.size)).sum + 20 * items.length) +
        2 * items.length := by
    induction items with
    | nil => simp
    | cons family items ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        rw [ih]
        simp only [Nat.mul_add]
        omega
  have bound := productFamilyWitnessesCosted_cost_le W T families
  rw [sumEq] at bound
  simpa [Nat.add_assoc] using bound

end FactTables
end LeanUfo.UFO.DSL
