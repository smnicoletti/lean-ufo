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

/-- Counted universal scan over an array, stopping at its first false item. -/
def allArrayCosted (xs : Array α) (p : α → Costed Bool) : Costed Bool :=
  allListCosted xs.toList p

theorem allListCosted_value (xs : List α) (p : α → Costed Bool) :
    (allListCosted xs p).value = xs.all (fun x => (p x).value) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases h : (p x).value <;>
        simp [allListCosted, Costed.andThen, Costed.charge, h, ih]

/-- Counted existential scan over an array, stopping at its first true item. -/
def anyListCosted : List α → (α → Costed Bool) → Costed Bool
  | [], _ => .pure false
  | x :: xs, p => Costed.orElse (Costed.charge 1 (p x))
      (fun _ => anyListCosted xs p)

def anyArrayCosted (xs : Array α) (p : α → Costed Bool) : Costed Bool :=
  anyListCosted xs.toList p

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
Operational combined-complexity bound for a finite universal scan.  The
registry length is explicit input here; for the fixed 116-axiom UFO registry
it becomes a constant in the later data-complexity corollary.  This separation
follows the finite-model-checking convention of Vardi and
Madelaine--Martin, while the proof follows the short-circuiting executable
rather than charging an independently postulated envelope.
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
    (allArrayCosted xs p).cost ≤ xs.size * (perItem + 2) := by
  apply allListCosted_cost_le
  intro x hx
  exact hItem x (by simpa using hx)

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
    (anyArrayCosted xs p).cost ≤ xs.size * (perItem + 2) := by
  apply anyListCosted_cost_le
  intro x hx
  exact hItem x (by simpa using hx)

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
  (checks.toList.map fun check => check.bound + 2).sum

theorem checkBoundedRegistryCosted_cost_le (checks : Array BoundedCheck) :
    (checkBoundedRegistryCosted checks).cost ≤ boundedRegistryCostBound checks := by
  unfold checkBoundedRegistryCosted boundedRegistryCostBound allArrayCosted
  exact allListCosted_cost_le_sum checks.toList (fun check => check.run ())
    (fun check => check.bound) (by
      intro check _
      exact check.valid)

theorem checkBoundedRegistryCosted_value (checks : Array BoundedCheck) :
    (checkBoundedRegistryCosted checks).value =
      checks.toList.all (fun check => (check.run ()).value) := by
  exact allListCosted_value checks.toList (fun check => check.run ())

@[simp] theorem checkRegistryCosted_value (checks : Array CheckThunk) :
    (checkRegistryCosted checks).value = checkRegistry checks := rfl

theorem checkRegistryCosted_value_eq_all (checks : Array CheckThunk) :
    (checkRegistryCosted checks).value =
      checks.toList.all (fun check => (check ()).value) := by
  exact allListCosted_value checks.toList (fun check => check ())

/-- Registry-size-parameterized bound; no fixed-registry assumption is hidden. -/
theorem checkRegistryCosted_cost_le (checks : Array CheckThunk) (perCheck : Nat)
    (hCheck : ∀ check ∈ checks, (check ()).cost ≤ perCheck) :
    (checkRegistryCosted checks).cost ≤ checks.size * (perCheck + 2) := by
  exact allArrayCosted_cost_le checks (fun check => check ()) perCheck hCheck

/-- Sum the individual bounds of a heterogeneous delayed checker registry. -/
theorem checkRegistryCosted_cost_le_sum (checks : Array CheckThunk)
    (bound : CheckThunk → Nat)
    (hCheck : ∀ check ∈ checks, (check ()).cost ≤ bound check) :
    (checkRegistryCosted checks).cost ≤
      (checks.toList.map fun check => bound check + 2).sum := by
  exact allListCosted_cost_le_sum checks.toList (fun check => check ()) bound
    (by
      intro check hcheck
      exact hCheck check (by simpa using hcheck))

example : allArrayCosted #[1, 2, 3] (fun n => .tick (n < 2) 2) = ⟨false, 8⟩ := by
  native_decide

example : anyArrayCosted #[1, 2, 3] (fun n => .tick (n == 2) 2) = ⟨true, 8⟩ := by
  native_decide

end LeanUfo.UFO.DSL.Complexity
