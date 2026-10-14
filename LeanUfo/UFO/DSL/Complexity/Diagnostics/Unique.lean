import LeanUfo.UFO.DSL.Complexity.CostModel
import Init.Data.List.Range

/-!
# Counted search for a unique finite witness

The search returns the only matching index, or no index when there are zero
or multiple matches. It stops at the second match. Predicate costs are supplied
by the caller and added only for visited indices.

As in Niu et al.'s cost-aware semantics (POPL 2022), the value theorem and
cost bound state separate properties of one computation. Here a list specifies
uniqueness, while the executable loop retains one index and stops at the second
match. See `CostModel.lean` and `docs/dsl/complexity.md` for the cost model and
literature references.
-/

namespace LeanUfo.UFO.DSL.Complexity

private def uniqueIndexFromSpec (predicate : Nat → Bool) :
    List Nat → Option Nat → Option Nat
  | [], found => found
  | i :: rest, found =>
      if predicate i then
        match found with
        | none => uniqueIndexFromSpec predicate rest (some i)
        | some _ => none
      else uniqueIndexFromSpec predicate rest found

/-- One domain test occurs at every call, including the terminal call.
A visited index adds its predicate cost and a Boolean branch. Continuing adds
an index increment. A match also tests whether a witness was already found. -/
def uniqueIndexCosted (count : Nat) (predicate : Nat → Costed Bool) :
    Costed (Option Nat) :=
  go 0 count none 0
where
  go (start remaining : Nat) (found : Option Nat) (cost : Nat) : Costed (Option Nat) :=
    match remaining with
    | 0 => ⟨found, cost + 1⟩
    | remaining + 1 =>
        let checked := predicate start
        if checked.value then
          match found with
          | none => go (start + 1) remaining (some start) (cost + checked.cost + 4)
          | some _ => ⟨none, cost + checked.cost + 3⟩
        else go (start + 1) remaining found (cost + checked.cost + 3)

private theorem uniqueIndexCosted_go_value (predicate : Nat → Costed Bool)
    (start remaining : Nat) (found : Option Nat) (cost : Nat) :
    (uniqueIndexCosted.go predicate start remaining found cost).value =
      uniqueIndexFromSpec (fun i => (predicate i).value) (List.range' start remaining) found := by
  induction remaining generalizing start found cost with
  | zero => rfl
  | succ remaining ih =>
      simp only [uniqueIndexCosted.go, List.range'_succ, uniqueIndexFromSpec]
      split
      · cases found <;> simp [ih]
      · exact ih _ _ _

private theorem uniqueIndexFromSpec_eq_filter (predicate : Nat → Bool)
    (indices : List Nat) (found : Option Nat) :
    uniqueIndexFromSpec predicate indices found =
      match found.toList ++ indices.filter predicate with
      | [i] => some i
      | _ => none := by
  induction indices generalizing found with
  | nil => cases found <;> rfl
  | cons i rest ih =>
      simp only [uniqueIndexFromSpec, List.filter_cons]
      split
      · cases found with
        | none =>
            rw [ih]
            rfl
        | some previous => rfl
      · exact ih found

/-- The result is the sole element of the filtered domain. The list is only a
specification: execution neither allocates it nor visits entries after a second
match. -/
theorem uniqueIndexCosted_value (count : Nat) (predicate : Nat → Costed Bool) :
    (uniqueIndexCosted count predicate).value =
      match (List.range count).filter (fun i => (predicate i).value) with
      | [i] => some i
      | _ => none := by
  rw [uniqueIndexCosted, uniqueIndexCosted_go_value, uniqueIndexFromSpec_eq_filter]
  simp [List.range_eq_range']

private theorem uniqueIndexCosted_go_cost_le (predicate : Nat → Costed Bool)
    (start remaining : Nat) (found : Option Nat) (cost perItem : Nat)
    (bounded : ∀ i, start ≤ i → i < start + remaining → (predicate i).cost ≤ perItem) :
    (uniqueIndexCosted.go predicate start remaining found cost).cost ≤
      cost + remaining * (perItem + 4) + 1 := by
  induction remaining generalizing start found cost with
  | zero => simp [uniqueIndexCosted.go]
  | succ remaining ih =>
      have hhead := bounded start (by omega) (by omega)
      have htail := fun found cost =>
        ih (start + 1) found cost (by intro i hlo hhi; exact bounded i (by omega) (by omega))
      simp only [uniqueIndexCosted.go]
      split
      · cases found with
        | none =>
            have h := htail (some start) (cost + (predicate start).cost + 4)
            simp only [Nat.succ_mul]
            omega
        | some previous =>
            simp only [Nat.succ_mul]
            omega
      · have h := htail found (cost + (predicate start).cost + 3)
        simp only [Nat.succ_mul]
        omega

theorem uniqueIndexCosted_cost_le (count : Nat) (predicate : Nat → Costed Bool)
    (perItem : Nat) (bounded : ∀ i, i < count → (predicate i).cost ≤ perItem) :
    (uniqueIndexCosted count predicate).cost ≤ count * (perItem + 4) + 1 := by
  simpa [uniqueIndexCosted] using
    uniqueIndexCosted_go_cost_le predicate 0 count none 0 perItem
      (by intro i hlo hi; exact bounded i (by omega))

end LeanUfo.UFO.DSL.Complexity
