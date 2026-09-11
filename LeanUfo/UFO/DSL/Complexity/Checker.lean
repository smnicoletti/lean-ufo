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

theorem anyListCosted_value (xs : List α) (p : α → Costed Bool) :
    (anyListCosted xs p).value = xs.any (fun x => (p x).value) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [anyListCosted, Costed.orElse_value, Costed.charge_value,
        List.any_cons, ih]

/-- Visit finite coordinates directly. The decreasing remainder controls the
loop; the proof supplies the coordinate bound and is erased at runtime. No
candidate list is constructed before the first predicate evaluation. -/
private def allFinFromCosted.go {n : Nat} (p : Fin n → Costed Bool) :
    (start remaining : Nat) → start + remaining ≤ n → Nat → Costed Bool
  | _, 0, _, cost => ⟨true, cost⟩
  | start, remaining + 1, h, cost =>
      let current := p ⟨start, by omega⟩
      let cost := cost + current.cost + 2
      if current.value then
        allFinFromCosted.go p (start + 1) remaining (by omega) cost
      else ⟨false, cost⟩

private def anyFinFromCosted.go {n : Nat} (p : Fin n → Costed Bool) :
    (start remaining : Nat) → start + remaining ≤ n → Nat → Costed Bool
  | _, 0, _, cost => ⟨false, cost⟩
  | start, remaining + 1, h, cost =>
      let current := p ⟨start, by omega⟩
      let cost := cost + current.cost + 2
      if current.value then ⟨true, cost⟩
      else anyFinFromCosted.go p (start + 1) remaining (by omega) cost

/-- Accumulate each visited predicate's cost before continuing. The recursive
call is in tail position, so a full scan needs no stack of pending additions. -/
def allFinFromCosted {n : Nat} (p : Fin n → Costed Bool)
    (start remaining : Nat) (h : start + remaining ≤ n) : Costed Bool :=
  allFinFromCosted.go p start remaining h 0

def anyFinFromCosted {n : Nat} (p : Fin n → Costed Bool)
    (start remaining : Nat) (h : start + remaining ≤ n) : Costed Bool :=
  anyFinFromCosted.go p start remaining h 0

def allFinCosted (n : Nat) (p : Fin n → Costed Bool) : Costed Bool :=
  allFinFromCosted p 0 n (by omega)

def anyFinCosted (n : Nat) (p : Fin n → Costed Bool) : Costed Bool :=
  anyFinFromCosted p 0 n (by omega)

/-- The list occurs only in the specification. Equality includes both the
Boolean result and the charges for the visited prefix. -/
private theorem allFinFromCosted_go_eq_list {n : Nat} (p : Fin n → Costed Bool)
    (start remaining : Nat) (h : start + remaining ≤ n) (cost : Nat) :
    allFinFromCosted.go p start remaining h cost =
      Costed.charge cost (allListCosted (List.ofFn fun i : Fin remaining =>
        (⟨start + i.val, by omega⟩ : Fin n)) p) := by
  induction remaining generalizing start cost with
  | zero => simp [allFinFromCosted.go, allListCosted, Costed.pure, Costed.charge]
  | succ remaining ih =>
      rw [List.ofFn_succ]
      cases hc : (p ⟨start, by omega⟩).value <;>
        simp only [allFinFromCosted.go, Fin.val_zero, Nat.add_zero,
          allListCosted, Costed.andThen, Costed.charge, hc,
          Bool.false_eq_true, ↓reduceIte]
      · congr 1 <;> omega
      · rw [ih]
        simp only [Costed.charge, Fin.val_succ]
        have indices :
            (List.ofFn fun i : Fin remaining => (⟨start + 1 + i.val, by omega⟩ : Fin n)) =
              List.ofFn (fun i : Fin remaining => (⟨start + (i.val + 1), by omega⟩ : Fin n)) := by
          congr 1
          funext i
          apply Fin.ext
          change start + 1 + i.val = start + (i.val + 1)
          omega
        rw [indices]
        congr 1 <;> omega

private theorem anyFinFromCosted_go_eq_list {n : Nat} (p : Fin n → Costed Bool)
    (start remaining : Nat) (h : start + remaining ≤ n) (cost : Nat) :
    anyFinFromCosted.go p start remaining h cost =
      Costed.charge cost (anyListCosted (List.ofFn fun i : Fin remaining =>
        (⟨start + i.val, by omega⟩ : Fin n)) p) := by
  induction remaining generalizing start cost with
  | zero => simp [anyFinFromCosted.go, anyListCosted, Costed.pure, Costed.charge]
  | succ remaining ih =>
      rw [List.ofFn_succ]
      cases hc : (p ⟨start, by omega⟩).value <;>
        simp only [anyFinFromCosted.go, Fin.val_zero, Nat.add_zero,
          anyListCosted, Costed.orElse, Costed.charge, hc,
          Bool.false_eq_true, ↓reduceIte]
      · rw [ih]
        simp only [Costed.charge, Fin.val_succ]
        have indices :
            (List.ofFn fun i : Fin remaining => (⟨start + 1 + i.val, by omega⟩ : Fin n)) =
              List.ofFn (fun i : Fin remaining => (⟨start + (i.val + 1), by omega⟩ : Fin n)) := by
          congr 1
          funext i
          apply Fin.ext
          change start + 1 + i.val = start + (i.val + 1)
          omega
        rw [indices]
        congr 1 <;> omega
      · congr 1 <;> omega

theorem allFinFromCosted_eq_list {n : Nat} (p : Fin n → Costed Bool)
    (start remaining : Nat) (h : start + remaining ≤ n) :
    allFinFromCosted p start remaining h =
      allListCosted (List.ofFn fun i : Fin remaining =>
        (⟨start + i.val, by omega⟩ : Fin n)) p := by
  simpa [allFinFromCosted, Costed.charge] using
    allFinFromCosted_go_eq_list p start remaining h 0

theorem anyFinFromCosted_eq_list {n : Nat} (p : Fin n → Costed Bool)
    (start remaining : Nat) (h : start + remaining ≤ n) :
    anyFinFromCosted p start remaining h =
      anyListCosted (List.ofFn fun i : Fin remaining =>
        (⟨start + i.val, by omega⟩ : Fin n)) p := by
  simpa [anyFinFromCosted, Costed.charge] using
    anyFinFromCosted_go_eq_list p start remaining h 0

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

/-- Natural-number consumers use the same finite loop. The range list is a
proof specification, so even an immediate answer requires no list allocation.
The equality preserves both the result and the cost of the visited prefix. -/
theorem allListCosted_range_eq_fin (n : Nat) (p : Nat → Costed Bool) :
    allListCosted (List.range n) p = allFinCosted n (fun i => p i.val) := by
  symm
  rw [allFinCosted_eq_list, ← allListCosted_map]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

theorem anyListCosted_range_eq_fin (n : Nat) (p : Nat → Costed Bool) :
    anyListCosted (List.range n) p = anyFinCosted n (fun i => p i.val) := by
  symm
  rw [anyFinCosted_eq_list, ← anyListCosted_map]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

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

/-- Compare lengths before visiting paired coordinates. The scan stops at the
first unequal item. Each visit charges two array reads in addition to the
finite loop and its Boolean branch. No zip or index array is allocated. -/
def arrayEqCosted (left right : Array α) (compare : α → α → Costed Bool) : Costed Bool :=
  if h : left.size = right.size then
    Costed.charge 2 <| allFinCosted left.size fun i =>
      Costed.charge 2 (compare left[i.val] (getElem right i.val (by omega)))
  else Costed.tick false 2

theorem arrayEqCosted_value [BEq α] [LawfulBEq α]
    (left right : Array α) (compare : α → α → Costed Bool)
    (hcompare : ∀ a b, (compare a b).value = (a == b)) :
    (arrayEqCosted left right compare).value = (left == right) := by
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq]
  by_cases hs : left.size = right.size
  · simp only [arrayEqCosted, hs, ↓reduceDIte, Costed.charge_value,
      allFinCosted_eq_list, allListCosted_eq_true_iff, hcompare, beq_iff_eq]
    constructor
    · intro h
      apply Array.ext hs
      intro i hi hj
      exact h ⟨i, hi⟩ (by simp)
    · intro h
      subst right
      simp
  · simp only [arrayEqCosted, hs, ↓reduceDIte, Costed.tick_value, Bool.false_eq_true, false_iff]
    intro h
    exact hs (congrArg Array.size h)

/-- Heterogeneous item budgets include variable-length records such as
product families. The left array supplies the scan length and item sizes. -/
theorem arrayEqCosted_cost_le_sum (left right : Array α)
    (compare : α → α → Costed Bool) (bound : α → Nat)
    (hcompare : ∀ a b, (compare a b).cost ≤ bound a) :
    (arrayEqCosted left right compare).cost ≤
      2 + (left.toList.map (fun a => bound a + 4)).sum := by
  by_cases hs : left.size = right.size
  · simp only [arrayEqCosted, hs, ↓reduceDIte, Costed.charge_cost, allFinCosted_eq_list]
    have h := allListCosted_cost_le_sum (List.finRange left.size)
      (fun i => Costed.charge 2 (compare left[i.val] (getElem right i.val (by omega))))
      (fun i => bound left[i.val] + 2) (by
        intro i _
        have h := hcompare left[i.val] (getElem right i.val (by omega))
        simp only [Costed.charge_cost]
        omega)
    have rows : ((List.finRange left.size).map (fun i => bound left[i.val] + 2 + 2)).sum =
        (left.toList.map (fun a => bound a + 4)).sum := by
      rw [← array_indices_toList left, List.map_map]
      simp only [Nat.add_assoc]
      rfl
    rw [rows] at h
    exact Nat.add_le_add_left h 2
  · simp [arrayEqCosted, hs]

theorem arrayEqCosted_cost_le (left right : Array α)
    (compare : α → α → Costed Bool) (perItem : Nat)
    (hcompare : ∀ a b, (compare a b).cost ≤ perItem) :
    (arrayEqCosted left right compare).cost ≤ 2 + left.size * (perItem + 4) := by
  have sum (xs : List α) : (xs.map (fun _ => perItem + 4)).sum = xs.length * (perItem + 4) := by
    induction xs with
    | nil => simp
    | cons x xs ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih,
        Nat.succ_mul, Nat.add_comm]
  simpa only [sum, Array.length_toList] using
    arrayEqCosted_cost_le_sum left right compare (fun _ => perItem) hcompare

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

/-- A separately invoked entry needs its own bound: the registry's actual
early-exit count can be smaller than the cost of an entry it never reaches. -/
theorem boundedCheck_cost_le_registryBound (checks : Array BoundedCheck)
    (check : BoundedCheck) (member : check ∈ checks.toList) :
    (check.run ()).cost ≤ boundedRegistryCostBound checks := by
  have bound : ∀ xs : List BoundedCheck, check ∈ xs →
      check.bound ≤ (xs.map fun entry => entry.bound + 3).sum := by
    intro xs
    induction xs with
    | nil => simp
    | cons head tail ih =>
        intro member
        rcases List.mem_cons.mp member with same | later
        · subst head
          simp only [List.map_cons, List.sum_cons]
          omega
        · have rest := ih later
          simp only [List.map_cons, List.sum_cons]
          omega
  exact Nat.le_trans check.valid (bound checks.toList member)

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
