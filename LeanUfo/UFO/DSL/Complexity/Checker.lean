import LeanUfo.UFO.DSL.Complexity.CostModel

/-!
# Counted finite quantifiers and checker registries

These combinators expose the actual left-to-right evaluation order.  A stopped
scan does not charge or evaluate later elements.  Per-axiom counted checkers are
therefore built compositionally from the same operations that compute their
Boolean values, following cost-aware operational semantics (Niu et al., POPL
2022; Haslbeck, 2018).  See `docs/dsl/complexity.md` for full references.
-/

namespace LeanUfo.UFO.DSL.Complexity

/-- Structural counted universal scan used to expose short-circuit semantics. -/
def allListCosted : List α → (α → Costed Bool) → Costed Bool
  | [], _ => .pure true
  | x :: xs, p => Costed.andThen (Costed.charge 1 (p x))
      (fun _ => allListCosted xs p)

theorem allListCosted_value (xs : List α) (p : α → Costed Bool) :
    (allListCosted xs p).value = xs.all (fun x => (p x).value) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases h : (p x).value <;>
        simp [allListCosted, Costed.andThen, Costed.charge, h, ih]

/-- Counted existential scan over a list, stopping at its first true item. -/
def anyListCosted : List α → (α → Costed Bool) → Costed Bool
  | [], _ => .pure false
  | x :: xs, p => Costed.orElse (Costed.charge 1 (p x))
      (fun _ => anyListCosted xs p)

/-- Visit finite coordinates directly. The decreasing remainder controls the
loop; the proof supplies the coordinate bound and is erased at runtime. No
candidate list is constructed before the first predicate evaluation. -/
def allFinFromCosted {n : Nat} (p : Fin n → Costed Bool) :
    (start remaining : Nat) → start + remaining ≤ n → Costed Bool
  | _, 0, _ => .pure true
  | start, remaining + 1, h =>
      Costed.andThen (Costed.charge 1 (p ⟨start, by omega⟩))
        (fun _ => allFinFromCosted p (start + 1) remaining (by omega))

def anyFinFromCosted {n : Nat} (p : Fin n → Costed Bool) :
    (start remaining : Nat) → start + remaining ≤ n → Costed Bool
  | _, 0, _ => .pure false
  | start, remaining + 1, h =>
      Costed.orElse (Costed.charge 1 (p ⟨start, by omega⟩))
        (fun _ => anyFinFromCosted p (start + 1) remaining (by omega))

def allFinCosted (n : Nat) (p : Fin n → Costed Bool) : Costed Bool :=
  allFinFromCosted p 0 n (by omega)

def anyFinCosted (n : Nat) (p : Fin n → Costed Bool) : Costed Bool :=
  anyFinFromCosted p 0 n (by omega)

/-- The list occurs only in the specification. Equality includes both the
Boolean result and the charges for the visited prefix. -/
theorem allFinFromCosted_eq_list {n : Nat} (p : Fin n → Costed Bool)
    (start remaining : Nat) (h : start + remaining ≤ n) :
    allFinFromCosted p start remaining h =
      allListCosted (List.ofFn fun i : Fin remaining =>
        (⟨start + i.val, by omega⟩ : Fin n)) p := by
  induction remaining generalizing start with
  | zero => simp [allFinFromCosted, allListCosted]
  | succ remaining ih =>
      rw [List.ofFn_succ]
      simp only [allFinFromCosted, allListCosted]
      congr 1
      funext _
      rw [ih]
      congr 1
      apply congrArg List.ofFn
      funext i
      apply Fin.ext
      simp [Nat.add_comm, Nat.add_left_comm]

theorem anyFinFromCosted_eq_list {n : Nat} (p : Fin n → Costed Bool)
    (start remaining : Nat) (h : start + remaining ≤ n) :
    anyFinFromCosted p start remaining h =
      anyListCosted (List.ofFn fun i : Fin remaining =>
        (⟨start + i.val, by omega⟩ : Fin n)) p := by
  induction remaining generalizing start with
  | zero => simp [anyFinFromCosted, anyListCosted]
  | succ remaining ih =>
      rw [List.ofFn_succ]
      simp only [anyFinFromCosted, anyListCosted]
      congr 1
      funext _
      rw [ih]
      congr 1
      apply congrArg List.ofFn
      funext i
      apply Fin.ext
      simp [Nat.add_comm, Nat.add_left_comm]

theorem allFinCosted_eq_list (n : Nat) (p : Fin n → Costed Bool) :
    allFinCosted n p = allListCosted (List.finRange n) p := by
  simpa [allFinCosted, List.finRange] using allFinFromCosted_eq_list p 0 n (by omega)

theorem anyFinCosted_eq_list (n : Nat) (p : Fin n → Costed Bool) :
    anyFinCosted n p = anyListCosted (List.finRange n) p := by
  simpa [anyFinCosted, List.finRange] using anyFinFromCosted_eq_list p 0 n (by omega)

-- Each visited index charges one loop iteration, one Boolean branch, and the
-- predicate's own cost. An empty or unvisited suffix allocates no index list.
example : allFinCosted 0 (fun _ => .tick false 10) = ⟨true, 0⟩ := rfl
example : anyFinCosted 0 (fun _ => .tick true 10) = ⟨false, 0⟩ := rfl
example : allFinCosted 3 (fun _ => .tick true 2) = ⟨true, 12⟩ := rfl
example : allFinCosted 1000000 (fun _ => .tick false 1) = ⟨false, 3⟩ := rfl
example : anyFinCosted 1000000 (fun _ => .tick true 1) = ⟨true, 3⟩ := rfl
example : anyFinCosted 5 (fun i => .tick (i.val == 2) (i.val + 1)) = ⟨true, 12⟩ := rfl

/-- Indexed array traversal charges the cell access as well as the finite-loop
iteration and Boolean branch. No array-to-list conversion precedes the scan. -/
def allArrayCosted (xs : Array α) (p : α → Costed Bool) : Costed Bool :=
  allFinCosted xs.size fun i => Costed.charge 1 (p xs[i.val])

def anyArrayCosted (xs : Array α) (p : α → Costed Bool) : Costed Bool :=
  anyFinCosted xs.size fun i => Costed.charge 1 (p xs[i.val])

theorem allListCosted_map (xs : List α) (f : α → β) (p : β → Costed Bool) :
    allListCosted (xs.map f) p = allListCosted xs (fun x => p (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, allListCosted, ih]

theorem anyListCosted_map (xs : List α) (f : α → β) (p : β → Costed Bool) :
    anyListCosted (xs.map f) p = anyListCosted xs (fun x => p (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, anyListCosted, ih]

private theorem array_indices_toList (xs : Array α) :
    (List.finRange xs.size).map (fun i => xs[i.val]) = xs.toList := by
  rw [List.finRange, List.map_ofFn]
  change (List.ofFn fun i : Fin xs.size => xs[i.val]) = xs.toList
  rw [← Array.toList_ofFn, Array.ofFn_getElem]

/-- List specifications retain the charge for each visited array cell. -/
theorem allArrayCosted_eq_list (xs : Array α) (p : α → Costed Bool) :
    allArrayCosted xs p = allListCosted xs.toList (fun x => Costed.charge 1 (p x)) := by
  unfold allArrayCosted
  rw [allFinCosted_eq_list,
    ← allListCosted_map (List.finRange xs.size) (fun i => xs[i.val])
      (fun x => Costed.charge 1 (p x)), array_indices_toList]

theorem anyArrayCosted_eq_list (xs : Array α) (p : α → Costed Bool) :
    anyArrayCosted xs p = anyListCosted xs.toList (fun x => Costed.charge 1 (p x)) := by
  unfold anyArrayCosted
  rw [anyFinCosted_eq_list,
    ← anyListCosted_map (List.finRange xs.size) (fun i => xs[i.val])
      (fun x => Costed.charge 1 (p x)), array_indices_toList]

theorem allArrayCosted_value (xs : Array α) (p : α → Costed Bool) :
    (allArrayCosted xs p).value = xs.toList.all (fun x => (p x).value) := by
  rw [allArrayCosted_eq_list, allListCosted_value]
  rfl

theorem allListCosted_eq_true_iff (xs : List α) (p : α → Costed Bool) :
    (allListCosted xs p).value = true ↔ ∀ x ∈ xs, (p x).value = true := by
  induction xs with
  | nil => simp [allListCosted]
  | cons x xs ih =>
      by_cases h : (p x).value = true
      · simp [allListCosted, Costed.andThen, Costed.charge, h, ih]
      · have hf : (p x).value = false := by
          cases hv : (p x).value
          · rfl
          · exact False.elim (h hv)
        simp [allListCosted, Costed.andThen, Costed.charge, hf]

theorem anyListCosted_eq_true_iff (xs : List α) (p : α → Costed Bool) :
    (anyListCosted xs p).value = true ↔ ∃ x ∈ xs, (p x).value = true := by
  induction xs with
  | nil => simp [anyListCosted]
  | cons x xs ih =>
      by_cases h : (p x).value = true
      · simp [anyListCosted, Costed.orElse, Costed.charge, h]
      · have hf : (p x).value = false := by
          cases hv : (p x).value
          · rfl
          · exact False.elim (h hv)
        simp [anyListCosted, Costed.orElse, Costed.charge, hf, ih]

/--
Bound a finite universal scan by its length and a supplied predicate bound.
The proof follows the executable's short-circuit branches. Registry length
can vary here; it becomes a constant for the fixed 116-axiom UFO registry.
This distinction follows Vardi and Madelaine--Martin's treatment of data and
combined complexity. The supplied predicate bound is a separate obligation.
-/
theorem allListCosted_cost_le (xs : List α) (p : α → Costed Bool) (perItem : Nat)
    (hItem : ∀ x ∈ xs, (p x).cost ≤ perItem) :
    (allListCosted xs p).cost ≤ xs.length * (perItem + 2) := by
  induction xs with
  | nil => simp [allListCosted]
  | cons x xs ih =>
      have hx := hItem x (by simp)
      have hxs : ∀ y ∈ xs, (p y).cost ≤ perItem := by
        intro y hy
        exact hItem y (by simp [hy])
      have htail := ih hxs
      cases hv : (p x).value <;>
        simp [allListCosted, Costed.andThen, Costed.charge, hv,
          Nat.succ_mul] <;> omega

theorem allArrayCosted_cost_le (xs : Array α) (p : α → Costed Bool)
    (perItem : Nat) (hItem : ∀ x ∈ xs, (p x).cost ≤ perItem) :
    (allArrayCosted xs p).cost ≤ xs.size * (perItem + 3) := by
  rw [allArrayCosted_eq_list]
  have h := allListCosted_cost_le xs.toList (fun x => Costed.charge 1 (p x))
    (perItem + 1) (by
      intro x hx
      have := hItem x (by simpa using hx)
      simp only [Costed.charge_cost]
      omega)
  simpa [Nat.add_assoc] using h

/--
Heterogeneous counterpart of `allListCosted_cost_le`.  This is useful for a
registry whose checks have genuinely different operational bounds: replacing
them all by the largest bound is sound but obscures how the program computes.
-/
theorem allListCosted_cost_le_sum (xs : List α) (p : α → Costed Bool)
    (bound : α → Nat) (hItem : ∀ x ∈ xs, (p x).cost ≤ bound x) :
    (allListCosted xs p).cost ≤ (xs.map fun x => bound x + 2).sum := by
  induction xs with
  | nil => simp [allListCosted]
  | cons x xs ih =>
      have hx := hItem x (by simp)
      have hxs : ∀ y ∈ xs, (p y).cost ≤ bound y := by
        intro y hy
        exact hItem y (by simp [hy])
      have htail := ih hxs
      cases hv : (p x).value <;>
        simp [allListCosted, Costed.andThen, Costed.charge, hv] <;> omega

/-- Existential counterpart of `allListCosted_cost_le`, with actual early exit. -/
theorem anyListCosted_cost_le (xs : List α) (p : α → Costed Bool) (perItem : Nat)
    (hItem : ∀ x ∈ xs, (p x).cost ≤ perItem) :
    (anyListCosted xs p).cost ≤ xs.length * (perItem + 2) := by
  induction xs with
  | nil => simp [anyListCosted]
  | cons x xs ih =>
      have hx := hItem x (by simp)
      have hxs : ∀ y ∈ xs, (p y).cost ≤ perItem := by
        intro y hy
        exact hItem y (by simp [hy])
      have htail := ih hxs
      cases hv : (p x).value <;>
        simp [anyListCosted, Costed.orElse, Costed.charge, hv,
          Nat.succ_mul] <;> omega

/-- Heterogeneous existential-scan bound.  Product-family witnesses have
different arities, so retaining the per-item sum is both tighter and more
faithful than postulating one global maximum. -/
theorem anyListCosted_cost_le_sum (xs : List α) (p : α → Costed Bool)
    (bound : α → Nat) (hItem : ∀ x ∈ xs, (p x).cost ≤ bound x) :
    (anyListCosted xs p).cost ≤ (xs.map fun x => bound x + 2).sum := by
  induction xs with
  | nil => simp [anyListCosted]
  | cons x xs ih =>
      have hx := hItem x (by simp)
      have hxs : ∀ y ∈ xs, (p y).cost ≤ bound y := by
        intro y hy
        exact hItem y (by simp [hy])
      have htail := ih hxs
      cases hv : (p x).value <;>
        simp [anyListCosted, Costed.orElse, Costed.charge, hv] <;> omega

theorem anyArrayCosted_cost_le (xs : Array α) (p : α → Costed Bool)
    (perItem : Nat) (hItem : ∀ x ∈ xs, (p x).cost ≤ perItem) :
    (anyArrayCosted xs p).cost ≤ xs.size * (perItem + 3) := by
  rw [anyArrayCosted_eq_list]
  have h := anyListCosted_cost_le xs.toList (fun x => Costed.charge 1 (p x))
    (perItem + 1) (by
      intro x hx
      have := hItem x (by simpa using hx)
      simp only [Costed.charge_cost]
      omega)
  simpa [Nat.add_assoc] using h

theorem allArrayCosted_cost_le_sum (xs : Array α) (p : α → Costed Bool)
    (bound : α → Nat) (hItem : ∀ x ∈ xs, (p x).cost ≤ bound x) :
    (allArrayCosted xs p).cost ≤ (xs.toList.map fun x => bound x + 3).sum := by
  rw [allArrayCosted_eq_list]
  have h := allListCosted_cost_le_sum xs.toList (fun x => Costed.charge 1 (p x))
    (fun x => bound x + 1) (by
      intro x hx
      have := hItem x (by simpa using hx)
      simp only [Costed.charge_cost]
      omega)
  simpa [Nat.add_assoc] using h

/-- A checker is delayed so the registry can genuinely stop at first failure. -/
abbrev CheckThunk := Unit → Costed Bool

/-- A delayed executable check paired with its own proved operational bound. -/
structure BoundedCheck where
  run : CheckThunk
  bound : Nat
  valid : (run ()).cost ≤ bound

namespace BoundedCheck

/-- Constructor whose bound is inferred from the supplied cost theorem. -/
def of (run : CheckThunk) {bound : Nat} (valid : (run ()).cost ≤ bound) :
    BoundedCheck := ⟨run, bound, valid⟩

end BoundedCheck

/-- Evaluate registered checks sequentially and stop at the first failure. -/
def checkRegistryCosted (checks : Array CheckThunk) : Costed Bool :=
  allArrayCosted checks (fun check => check ())

/-- Production registry evaluation is the erasure of the counted evaluator. -/
def checkRegistry (checks : Array CheckThunk) : Bool :=
  (checkRegistryCosted checks).value

/-- Evaluate a heterogeneous proved registry using the same early-exit scan. -/
def checkBoundedRegistryCosted (checks : Array BoundedCheck) : Costed Bool :=
  allArrayCosted checks (fun check => check.run ())

def boundedRegistryCostBound (checks : Array BoundedCheck) : Nat :=
  (checks.toList.map fun check => check.bound + 3).sum

theorem checkBoundedRegistryCosted_cost_le (checks : Array BoundedCheck) :
    (checkBoundedRegistryCosted checks).cost ≤ boundedRegistryCostBound checks := by
  unfold checkBoundedRegistryCosted boundedRegistryCostBound
  exact allArrayCosted_cost_le_sum checks (fun check => check.run ())
    (fun check => check.bound) (by
      intro check _
      exact check.valid)

theorem checkBoundedRegistryCosted_value (checks : Array BoundedCheck) :
    (checkBoundedRegistryCosted checks).value =
      checks.toList.all (fun check => (check.run ()).value) := by
  exact allArrayCosted_value checks (fun check => check.run ())

@[simp] theorem checkRegistryCosted_value (checks : Array CheckThunk) :
    (checkRegistryCosted checks).value = checkRegistry checks := rfl

theorem checkRegistryCosted_value_eq_all (checks : Array CheckThunk) :
    (checkRegistryCosted checks).value =
      checks.toList.all (fun check => (check ()).value) := by
  exact allArrayCosted_value checks (fun check => check ())

/-- Registry-size-parameterized bound; no fixed-registry assumption is hidden. -/
theorem checkRegistryCosted_cost_le (checks : Array CheckThunk) (perCheck : Nat)
    (hCheck : ∀ check ∈ checks, (check ()).cost ≤ perCheck) :
    (checkRegistryCosted checks).cost ≤ checks.size * (perCheck + 3) := by
  exact allArrayCosted_cost_le checks (fun check => check ()) perCheck hCheck

/-- Sum the individual bounds of a heterogeneous delayed checker registry. -/
theorem checkRegistryCosted_cost_le_sum (checks : Array CheckThunk)
    (bound : CheckThunk → Nat)
    (hCheck : ∀ check ∈ checks, (check ()).cost ≤ bound check) :
    (checkRegistryCosted checks).cost ≤
      (checks.toList.map fun check => bound check + 3).sum := by
  exact allArrayCosted_cost_le_sum checks (fun check => check ()) bound
    (by
      intro check hcheck
      exact hCheck check (by simpa using hcheck))

example : allArrayCosted #[1, 2, 3] (fun n => .tick (n < 2) 2) = ⟨false, 10⟩ := by
  native_decide

example : anyArrayCosted #[1, 2, 3] (fun n => .tick (n == 2) 2) = ⟨true, 10⟩ := by
  native_decide

end LeanUfo.UFO.DSL.Complexity
