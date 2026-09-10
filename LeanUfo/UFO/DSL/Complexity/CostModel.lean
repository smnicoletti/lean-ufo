import Init.Data.Vector.OfFn
import Init.Data.Fin.Fold

/-!
# Operational unit-cost computations

`Costed α` pairs an executable value with the number of abstract operations
performed to produce it. Production functions either project `value`—an
operation called cost **erasure**—or use a separate implementation with a
theorem proving that both implementations return the same value.

The model counts explicitly selected source-level operations.  It does not claim
to count CPU instructions, allocation, Lean elaboration, kernel reduction, or
native compiler work.

This value/cost separation follows the cost-aware semantic methodology of Niu,
Sterling, Grodin, and Harper (POPL 2022), and Haslbeck's time-bound Hoare
logics. The implementation constraint rules out costs assigned to an unrelated
function. Most production code projects `value`. The explicit compiler and
native table lookups instead have named correspondence theorems, which keep
certificate reduction compact. Forster et al. (ITP 2021) motivate this explicit
implementation-to-machine connection in mechanized complexity claims. The full
references and machine-model limits are in `docs/dsl/complexity.md`.
-/

namespace LeanUfo.UFO.DSL.Complexity

structure Costed (α : Type u) where
  value : α
  cost : Nat
deriving Repr, Inhabited, DecidableEq

namespace Costed

-- These record operations must inline so an executable `value` projection
-- can discard cost bookkeeping. Their equations, and therefore the proved
-- counts, are unchanged by this native-code optimization.
@[inline] def pure (value : α) : Costed α := ⟨value, 0⟩

@[inline] def tick (value : α) (cost : Nat := 1) : Costed α := ⟨value, cost⟩

@[inline] def map (f : α → β) (x : Costed α) : Costed β :=
  ⟨f x.value, x.cost⟩

@[inline] def bind (x : Costed α) (f : α → Costed β) : Costed β :=
  let y := f x.value
  ⟨y.value, x.cost + y.cost⟩

instance : Monad Costed where
  pure := pure
  bind := bind

instance : LawfulMonad Costed := LawfulMonad.mk' Costed
  (by intro α x; cases x; simp [Functor.map, bind, pure])
  (by intro α β x f; simp [Bind.bind, Pure.pure, bind, pure])
  (by intro α β γ x f g; simp [Bind.bind, bind, Nat.add_assoc])

@[inline] def charge (extra : Nat) (x : Costed α) : Costed α :=
  ⟨x.value, extra + x.cost⟩

/-- Count one string concatenation after producing both operands. Character
copying and allocation are outside this primitive-call model. Keeping this
operation separate lets text proofs use its value equation without expanding
the cost bookkeeping inside each preceding concatenation. -/
@[inline] def appendString (left right : Costed String) : Costed String :=
  ⟨left.value ++ right.value, left.cost + right.cost + 1⟩

@[simp] theorem appendString_value (left right : Costed String) :
    (appendString left right).value = left.value ++ right.value := rfl

@[simp] theorem appendString_cost (left right : Costed String) :
    (appendString left right).cost = left.cost + right.cost + 1 := rfl

/-- Count one Boolean negation after the computation of its operand. -/
def not (x : Costed Bool) : Costed Bool :=
  ⟨!x.value, x.cost + 1⟩

/-- Counted Boolean conjunction with Lean's left-to-right short circuit. -/
def andThen (left : Costed Bool) (right : Unit → Costed Bool) : Costed Bool :=
  if left.value then
    let r := right ()
    ⟨r.value, left.cost + 1 + r.cost⟩
  else
    ⟨false, left.cost + 1⟩

/-- Counted Boolean disjunction with Lean's left-to-right short circuit. -/
def orElse (left : Costed Bool) (right : Unit → Costed Bool) : Costed Bool :=
  if left.value then
    ⟨true, left.cost + 1⟩
  else
    let r := right ()
    ⟨r.value, left.cost + 1 + r.cost⟩

/-- Evaluate only the selected branch and charge its Boolean test. -/
def branch (condition : Costed Bool) (yes no : Unit → Costed α) : Costed α :=
  let result := if condition.value then yes () else no ()
  ⟨result.value, condition.cost + 1 + result.cost⟩

@[simp] theorem branch_value (condition : Costed Bool) (yes no : Unit → Costed α) :
    (branch condition yes no).value =
      if condition.value then (yes ()).value else (no ()).value := by
  cases h : condition.value <;> simp [branch, h]

theorem branch_cost_le (condition : Costed Bool) (yes no : Unit → Costed α)
    (testBound branchBound : Nat) (hc : condition.cost ≤ testBound)
    (hy : (yes ()).cost ≤ branchBound) (hn : (no ()).cost ≤ branchBound) :
    (branch condition yes no).cost ≤ testBound + 1 + branchBound := by
  cases h : condition.value <;> simp [branch, h] <;> omega

/--
Counted implication with the executable order of `!p || q`: compute and
negate the antecedent first, and evaluate the consequent only when `p` is
true.  This explicit order is important for the operational bounds below.
-/
def implies (left : Costed Bool) (right : Unit → Costed Bool) : Costed Bool :=
  orElse left.not right

/--
Counted Boolean equivalence.  The right operand is evaluated after the left;
when the left is false, negating the right result contributes one operation.
-/
def iff (left : Costed Bool) (right : Unit → Costed Bool) : Costed Bool :=
  let r := right ()
  if left.value then
    ⟨r.value, left.cost + 1 + r.cost⟩
  else
    ⟨!r.value, left.cost + 1 + r.cost + 1⟩

@[simp] theorem pure_value (x : α) : (pure x).value = x := rfl
@[simp] theorem pure_cost (x : α) : (pure x).cost = 0 := rfl
@[simp] theorem tick_value (x : α) (n : Nat) : (tick x n).value = x := rfl
@[simp] theorem tick_cost (x : α) (n : Nat) : (tick x n).cost = n := rfl
@[simp] theorem map_value (f : α → β) (x : Costed α) : (map f x).value = f x.value := rfl
@[simp] theorem map_cost (f : α → β) (x : Costed α) : (map f x).cost = x.cost := rfl
@[simp] theorem bind_value (x : Costed α) (f : α → Costed β) :
    (bind x f).value = (f x.value).value := rfl
@[simp] theorem bind_cost (x : Costed α) (f : α → Costed β) :
    (bind x f).cost = x.cost + (f x.value).cost := rfl
@[simp] theorem charge_value (extra : Nat) (x : Costed α) :
    (charge extra x).value = x.value := rfl
@[simp] theorem charge_cost (extra : Nat) (x : Costed α) :
    (charge extra x).cost = extra + x.cost := rfl
@[simp] theorem not_value (x : Costed Bool) : x.not.value = !x.value := rfl
@[simp] theorem not_cost (x : Costed Bool) : x.not.cost = x.cost + 1 := rfl

@[simp] theorem implies_value (left : Costed Bool) (right : Unit → Costed Bool) :
    (implies left right).value = (!left.value || (right ()).value) := by
  cases h : left.value <;> simp [implies, orElse, not, h]

/-- Compositional worst-case bound for executable short-circuit conjunction. -/
theorem andThen_cost_le (left : Costed Bool) (right : Unit → Costed Bool)
    (leftBound rightBound : Nat) (hl : left.cost ≤ leftBound)
    (hr : (right ()).cost ≤ rightBound) :
    (andThen left right).cost ≤ leftBound + 1 + rightBound := by
  cases h : left.value <;> simp [andThen, h] <;> omega

/-- Compositional worst-case bound for executable short-circuit disjunction. -/
theorem orElse_cost_le (left : Costed Bool) (right : Unit → Costed Bool)
    (leftBound rightBound : Nat) (hl : left.cost ≤ leftBound)
    (hr : (right ()).cost ≤ rightBound) :
    (orElse left right).cost ≤ leftBound + 1 + rightBound := by
  cases h : left.value <;> simp [orElse, h] <;> omega

/-- Compositional worst-case bound for executable implication. -/
theorem implies_cost_le (left : Costed Bool) (right : Unit → Costed Bool)
    (leftBound rightBound : Nat) (hl : left.cost ≤ leftBound)
    (hr : (right ()).cost ≤ rightBound) :
    (implies left right).cost ≤ leftBound + rightBound + 2 := by
  cases h : left.value <;> simp [implies, orElse, not, h] <;> omega

/-- Both operands of executable equivalence are evaluated; the false-left case
adds the second Boolean negation, giving two units of connective overhead. -/
theorem iff_cost_le (left : Costed Bool) (right : Unit → Costed Bool)
    (leftBound rightBound : Nat) (hl : left.cost ≤ leftBound)
    (hr : (right ()).cost ≤ rightBound) :
    (iff left right).cost ≤ leftBound + rightBound + 2 := by
  cases h : left.value <;> simp [iff, h] <;> omega

@[simp] theorem orElse_value (left : Costed Bool) (right : Unit → Costed Bool) :
    (orElse left right).value = (left.value || (right ()).value) := by
  cases h : left.value <;> simp [orElse, h]

@[simp] theorem andThen_value (left : Costed Bool) (right : Unit → Costed Bool) :
    (andThen left right).value = (left.value && (right ()).value) := by
  cases h : left.value <;> simp [andThen, h]

@[simp] theorem iff_value (left : Costed Bool) (right : Unit → Costed Bool) :
    (iff left right).value = (left.value == (right ()).value) := by
  cases h : left.value <;> simp [iff, h]

theorem cost_noninterference (x y : Costed α)
    (h : x.value = y.value) : (x.charge 1).value = y.value := by
  simpa [charge] using h

/-- Construct a vector while accumulating the cost of each cell. Lean's
`Vector.ofFnM` visits indices directly and pushes into a capacity-reserved
array. A state accumulator adds each callback's cost before the next iteration,
avoiding deferred additions on the call stack. Each callback also charges one
loop iteration and one cell write. No intermediate list is constructed. -/
def vectorOfFn {n : Nat} (f : Fin n → Costed α) : Costed (Vector α n) :=
  let result := (Vector.ofFnM (m := StateM Nat) fun i => fun cost =>
    let next := f i
    (next.value, cost + 2 + next.cost)) 0
  ⟨result.1, result.2⟩

/-- The accumulator implementation preserves both components of the monadic
specification, not just its returned vector. -/
theorem vectorOfFn_eq_ofFnM {n : Nat} (f : Fin n → Costed α) :
    vectorOfFn f = Vector.ofFnM (fun i => charge 2 (f i)) := by
  have aux {n : Nat} (f : Fin n → Costed α) (cost : Nat) :
      (Vector.ofFnM (m := StateM Nat) (fun i => fun cost =>
        let next := f i
        (next.value, cost + 2 + next.cost))) cost =
        let result := Vector.ofFnM (fun i => charge 2 (f i))
        (result.value, cost + result.cost) := by
    induction n with
    | zero => simp [Pure.pure, StateT.pure, pure]
    | succ n ih =>
        simp only [Vector.ofFnM_succ, Bind.bind, Pure.pure, StateT.bind,
          StateT.pure, bind, pure, charge]
        rw [ih]
        simp [charge, Nat.add_assoc]
  have h := aux f 0
  simp only [Nat.zero_add] at h
  unfold vectorOfFn
  rw [h]

@[simp] theorem vectorOfFn_value {n : Nat} (f : Fin n → Costed α) :
    (vectorOfFn f).value = Vector.ofFn (fun i => (f i).value) := by
  simp only [vectorOfFn_eq_ofFnM]
  induction n with
  | zero => simp [Pure.pure, pure, Vector.ofFn]
  | succ n ih =>
      simp only [Vector.ofFnM_succ, Bind.bind, Pure.pure, bind,
        pure, charge]
      simp only [charge] at ih
      rw [ih, Vector.ofFn_succ]
      rfl

/-- Constant callback costs give an exact constructor cost. Induction follows
the executed constructor. The two extra units count traversal and storage. -/
theorem vectorOfFn_cost_eq {n : Nat} (f : Fin n → Costed α) (perCell : Nat)
    (h : ∀ i, (f i).cost = perCell) :
    (vectorOfFn f).cost = n * (perCell + 2) := by
  simp only [vectorOfFn_eq_ofFnM]
  induction n with
  | zero => simp [Pure.pure, pure]
  | succ n ih =>
      have hInit := ih (fun i => f i.castSucc) (fun i => h i.castSucc)
      simp only [Vector.ofFnM_succ, Bind.bind, Pure.pure, bind, pure, charge]
      simp only [charge] at hInit
      rw [hInit, h]
      simp only [Nat.succ_mul]
      omega

theorem vectorOfFn_cost_le {n : Nat} (f : Fin n → Costed α) (perCell : Nat)
    (h : ∀ i, (f i).cost ≤ perCell) :
    (vectorOfFn f).cost ≤ n * (perCell + 2) := by
  simp only [vectorOfFn_eq_ofFnM]
  induction n with
  | zero => simp [Pure.pure, pure]
  | succ n ih =>
      have hInit := ih (fun i => f i.castSucc) (fun i => h i.castSucc)
      have hLast := h (Fin.last n)
      simp only [Vector.ofFnM_succ, Bind.bind, Pure.pure, bind,
        pure, charge]
      simpa [charge, Nat.succ_mul] using Nat.add_le_add hInit (by omega :
        2 + (f (Fin.last n)).cost ≤ perCell + 2)

/-- Initialize explicit storage with array and cost accumulators. Updating
the count before the tail call avoids retaining one call frame per cell. Each
iteration and cell write still contributes one unit. -/
def replicateArray (size : Nat) (value : α) : Costed (Array α) :=
  go value size (Array.emptyWithCapacity size) 0
where
  go (value : α) : Nat → Array α → Nat → Costed (Array α)
    | 0, cells, cost => ⟨cells, cost⟩
    | remaining + 1, cells, cost => go value remaining (cells.push value) (cost + 2)

private theorem replicateArray_go_value (value : α) (remaining : Nat)
    (cells : Array α) (cost : Nat) :
    (replicateArray.go value remaining cells cost).value =
      cells ++ Array.replicate remaining value := by
  induction remaining generalizing cells cost with
  | zero => simp [replicateArray.go]
  | succ remaining ih =>
      simp [replicateArray.go, ih, Array.replicate_succ']

private theorem replicateArray_go_cost (value : α) (remaining : Nat)
    (cells : Array α) (cost : Nat) :
    (replicateArray.go value remaining cells cost).cost = cost + 2 * remaining := by
  induction remaining generalizing cells cost with
  | zero => simp [replicateArray.go]
  | succ remaining ih => simp [replicateArray.go, ih, Nat.mul_succ, Nat.add_assoc, Nat.add_comm]

@[simp] theorem replicateArray_value (size : Nat) (value : α) :
    (replicateArray size value).value = Array.replicate size value := by
  simp [replicateArray, replicateArray_go_value]

@[simp] theorem replicateArray_cost (size : Nat) (value : α) :
    (replicateArray size value).cost = 2 * size := by
  simp [replicateArray, replicateArray_go_cost]

/-- Accumulator traversal with one iteration and one array read per entry. -/
def foldArray (xs : Array α) (initial : β) (step : β → α → Costed β) : Costed β :=
  xs.foldl (fun accumulated x =>
    let next := step accumulated.value x
    ⟨next.value, accumulated.cost + 2 + next.cost⟩) (pure initial)

/-- Accumulating costs during the forward loop agrees with the monadic
specification, including its exact cost. The executable loop does not retain
callbacks while waiting to add their costs on return. -/
theorem foldArray_eq_foldlM (xs : Array α) (initial : β) (step : β → α → Costed β) :
    foldArray xs initial step =
      xs.foldlM (fun state x => charge 2 (step state x)) initial := by
  have aux (ys : List α) (state : β) (cost : Nat) :
      ys.foldl (fun (accumulated : Costed β) x =>
        let next := step accumulated.value x
        ⟨next.value, accumulated.cost + 2 + next.cost⟩) ⟨state, cost⟩ =
      charge cost (ys.foldlM (fun state x => charge 2 (step state x)) state) := by
    induction ys generalizing state cost with
    | nil => simp [Pure.pure, pure, charge]
    | cons x ys ih =>
        simp only [List.foldl_cons, List.foldlM_cons, Bind.bind, ih]
        simp [bind, charge, Nat.add_assoc]
  simpa [foldArray, pure, charge] using aux xs.toList initial 0

@[simp] theorem foldArray_value (xs : Array α) (initial : β) (step : β → α → Costed β) :
    (foldArray xs initial step).value = xs.foldl (fun state x => (step state x).value) initial := by
  have aux (ys : List α) : ∀ state,
      (ys.foldlM (fun state x => charge 2 (step state x)) state).value =
        ys.foldl (fun state x => (step state x).value) state := by
    induction ys with
    | nil => intro state; rfl
    | cons x ys ih =>
        intro state
        simp only [List.foldlM_cons, Bind.bind, bind_value, charge_value, List.foldl_cons]
        exact ih _
  simpa [foldArray_eq_foldlM] using aux xs.toList initial

theorem foldArray_cost_eq (xs : Array α) (initial : β) (step : β → α → Costed β)
    (perStep : Nat) (h : ∀ state, ∀ x ∈ xs, (step state x).cost = perStep) :
    (foldArray xs initial step).cost = xs.size * (perStep + 2) := by
  have aux (ys : List α) (hh : ∀ state, ∀ x ∈ ys, (step state x).cost = perStep) :
      ∀ state, (ys.foldlM (fun state x => charge 2 (step state x)) state).cost =
        ys.length * (perStep + 2) := by
    induction ys with
    | nil => intro state; simp [Pure.pure, pure]
    | cons x ys ih =>
        intro state
        have hx := hh state x (by simp)
        have ht := ih (fun state y hy => hh state y (by simp [hy]))
        simp only [List.foldlM_cons, Bind.bind, bind_cost, charge_cost, charge_value,
          ht, hx, List.length_cons, Nat.succ_mul]
        omega
  simpa [foldArray_eq_foldlM] using aux xs.toList (by simpa using h) initial

/-- Append by traversing the right array, as Lean's `Array.append` does.
Each entry costs an iteration, a read, and a write. Reusing the left array
adds no initialization charge. Allocation and copy-on-write are outside this
primitive-call model, so the count depends only on the right array's size. -/
def appendArray (left right : Array α) : Costed (Array α) :=
  foldArray right left fun out item => tick (out.push item) 1

@[simp] theorem appendArray_value (left right : Array α) :
    (appendArray left right).value = left ++ right := by
  simp [appendArray, foldArray_value]
  rfl

@[simp] theorem appendArray_cost (left right : Array α) :
    (appendArray left right).cost = 3 * right.size := by
  have h := foldArray_cost_eq right left (fun out item => tick (out.push item) 1)
    1 (by intros; rfl)
  simpa [appendArray, Nat.mul_comm] using h

/-- Exact traversal cost when a callback's charge depends on its input item,
but not on the accumulated state. -/
theorem foldArray_cost_eq_sum (xs : Array α) (initial : β) (step : β → α → Costed β)
    (costOf : α → Nat) (h : ∀ state x, (step state x).cost = costOf x) :
    (foldArray xs initial step).cost = (xs.toList.map (fun x => costOf x + 2)).sum := by
  have aux (ys : List α) (state : β) :
      (ys.foldlM (fun state x => charge 2 (step state x)) state).cost =
        (ys.map (fun x => costOf x + 2)).sum := by
    induction ys generalizing state with
    | nil => simp [Pure.pure, pure]
    | cons x ys ih =>
        simp only [List.foldlM_cons, Bind.bind, bind_cost, charge_cost, charge_value,
          h, ih, List.map_cons, List.sum_cons]
        omega
  simpa [foldArray_eq_foldlM] using aux xs.toList initial

theorem foldArray_cost_le (xs : Array α) (initial : β) (step : β → α → Costed β)
    (perStep : Nat) (h : ∀ state, ∀ x ∈ xs, (step state x).cost ≤ perStep) :
    (foldArray xs initial step).cost ≤ xs.size * (perStep + 2) := by
  have aux (ys : List α) (hh : ∀ state, ∀ x ∈ ys, (step state x).cost ≤ perStep) :
      ∀ state, (ys.foldlM (fun state x => charge 2 (step state x)) state).cost ≤
        ys.length * (perStep + 2) := by
    induction ys with
    | nil => intro state; simp [Pure.pure, pure]
    | cons x ys ih =>
        intro state
        have hx := hh state x (by simp)
        have ht := ih (fun state y hy => hh state y (by simp [hy]))
        have hr := ht (step state x).value
        simp only [List.foldlM_cons, Bind.bind, bind_cost, charge_cost, charge_value,
          List.length_cons, Nat.succ_mul]
        omega
  simpa [foldArray_eq_foldlM] using aux xs.toList (by simpa using h) initial

/-- Sum item-specific callback bounds, including one iteration and one read
per array entry. This retains the sizes of differently sized input items. -/
theorem foldArray_cost_le_sum (xs : Array α) (initial : β) (step : β → α → Costed β)
    (bound : α → Nat) (h : ∀ state, ∀ x ∈ xs, (step state x).cost ≤ bound x) :
    (foldArray xs initial step).cost ≤ (xs.toList.map (fun x => bound x + 2)).sum := by
  have aux (ys : List α) (hh : ∀ state, ∀ x ∈ ys, (step state x).cost ≤ bound x) :
      ∀ state, (ys.foldlM (fun state x => charge 2 (step state x)) state).cost ≤
        (ys.map (fun x => bound x + 2)).sum := by
    induction ys with
    | nil => intro state; simp [Pure.pure, pure]
    | cons x ys ih =>
        intro state
        have hx := hh state x (by simp)
        have ht := ih (fun state y hy => hh state y (by simp [hy])) (step state x).value
        simp only [List.foldlM_cons, Bind.bind, bind_cost, charge_cost, charge_value,
          List.map_cons, List.sum_cons]
        omega
  simpa [foldArray_eq_foldlM] using aux xs.toList (by simpa using h) initial

/-- Bound a fold whose state grows by at most one unit per entry. A callback
can inspect the growing state, so its bound includes the largest reachable
state size. The proof uses this invariant without adding runtime checks. -/
theorem foldArray_cost_le_growth (xs : Array α) (initial : β) (step : β → α → Costed β)
    (size : β → Nat) (a b : Nat)
    (hcost : ∀ state, ∀ x ∈ xs, (step state x).cost ≤ a * size state + b)
    (hgrow : ∀ state, ∀ x ∈ xs, size (step state x).value ≤ size state + 1) :
    (foldArray xs initial step).cost ≤ xs.size * (a * (size initial + xs.size) + b + 2) := by
  have aux (ys : List α) (limit : Nat)
      (hc : ∀ state, ∀ x ∈ ys, (step state x).cost ≤ a * size state + b)
      (hg : ∀ state, ∀ x ∈ ys, size (step state x).value ≤ size state + 1) :
      ∀ state, size state + ys.length ≤ limit →
        (ys.foldlM (fun state x => charge 2 (step state x)) state).cost ≤
          ys.length * (a * limit + b + 2) := by
    induction ys with
    | nil => intro state hlimit; simp [Pure.pure, pure]
    | cons x ys ih =>
        intro state hlimit
        have hx := hc state x (by simp)
        have hs := hg state x (by simp)
        have ht := ih (fun state y hy => hc state y (by simp [hy]))
          (fun state y hy => hg state y (by simp [hy])) (step state x).value (by
            simp only [List.length_cons] at hlimit
            omega)
        have hscaled := Nat.mul_le_mul_left a (show size state ≤ limit by
          simp only [List.length_cons] at hlimit
          omega)
        simp only [List.foldlM_cons, Bind.bind, bind_cost, charge_cost, charge_value,
          List.length_cons, Nat.succ_mul]
        omega
  simpa [foldArray_eq_foldlM] using aux xs.toList (size initial + xs.size)
    (by simpa using hcost) (by simpa using hgrow) initial (by simp)

/-- Traverse an array directly, stopping at the first error. The accumulator
carries both state and cost. An error carries the cost reached at that point,
so the loop can return immediately without unwinding deferred additions.
Each visited entry charges one loop iteration and one array read. -/
def foldArrayExcept {β ε : Type u} (xs : Array α) (initial : β)
    (step : β → α → Costed (Except ε β)) : Costed (Except ε β) :=
  finish (xs.foldlM (advance step) (initial, 0))
where
  advance (step : β → α → Costed (Except ε β)) (accumulated : β × Nat) (x : α) :
      Except (ε × Nat) (β × Nat) :=
    let next := step accumulated.1 x
    let cost := accumulated.2 + 2 + next.cost
    match next.value with
    | .error error => .error (error, cost)
    | .ok state => .ok (state, cost)
  finish (result : Except (ε × Nat) (β × Nat)) : Costed (Except ε β) :=
    match result with
    | .error (error, cost) => ⟨.error error, cost⟩
    | .ok (state, cost) => ⟨.ok state, cost⟩

theorem foldArrayExcept_eq_foldlM (xs : Array α) (initial : β)
    (step : β → α → Costed (Except ε β)) :
    foldArrayExcept xs initial step =
      (xs.foldlM (fun state x => (ExceptT.mk (charge 2 (step state x)) : ExceptT ε Costed β))
        initial).run := by
  have aux (ys : List α) (state : β) (cost : Nat) :
      foldArrayExcept.finish (ys.foldlM (foldArrayExcept.advance step) (state, cost)) =
        charge cost ((ys.foldlM (fun state x =>
          (ExceptT.mk (charge 2 (step state x)) : ExceptT ε Costed β)) state).run) := by
    induction ys generalizing state cost with
    | nil => simp [foldArrayExcept.finish, Pure.pure, Except.pure, ExceptT.pure,
        ExceptT.mk, ExceptT.run, pure, charge]
    | cons x ys ih =>
        simp only [List.foldlM_cons, Bind.bind, foldArrayExcept.advance, Except.bind,
          ExceptT.bind, ExceptT.mk, ExceptT.run, bind, charge]
        cases h : (step state x).value with
        | error error => simp [foldArrayExcept.finish, ExceptT.bindCont, Pure.pure, pure,
            Nat.add_assoc]
        | ok next =>
            simpa [foldArrayExcept.advance, ExceptT.bindCont, ExceptT.mk, ExceptT.run,
              charge, Nat.add_assoc] using ih next (cost + 2 + (step state x).cost)
  simpa [foldArrayExcept, charge] using aux xs.toList initial 0

private theorem foldListExcept_value (xs : List α) (initial : β)
    (step : β → α → Costed (Except ε β)) :
    ((xs.foldlM (fun state x => (ExceptT.mk (charge 2 (step state x)) : ExceptT ε Costed β))
      initial).run).value = xs.foldlM (fun state x => (step state x).value) initial := by
  induction xs generalizing initial with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldlM_cons, Bind.bind, ExceptT.bind, ExceptT.mk, ExceptT.run,
        bind, charge, Except.bind]
      cases h : (step initial x).value with
      | error error => rfl
      | ok next =>
          simpa only [ExceptT.bindCont, ExceptT.mk, ExceptT.run, charge] using ih next

@[simp] theorem foldArrayExcept_value (xs : Array α) (initial : β)
    (step : β → α → Costed (Except ε β)) :
    (foldArrayExcept xs initial step).value =
      xs.foldlM (fun state x => (step state x).value) initial := by
  simpa [foldArrayExcept_eq_foldlM] using foldListExcept_value xs.toList initial step

theorem foldArrayExcept_cost_le (xs : Array α) (initial : β)
    (step : β → α → Costed (Except ε β)) (perStep : Nat)
    (h : ∀ state, ∀ x ∈ xs, (step state x).cost ≤ perStep) :
    (foldArrayExcept xs initial step).cost ≤ xs.size * (perStep + 2) := by
  have aux (ys : List α) (hh : ∀ state, ∀ x ∈ ys, (step state x).cost ≤ perStep) :
      ∀ state, ((ys.foldlM (fun state x =>
        (ExceptT.mk (charge 2 (step state x)) : ExceptT ε Costed β)) state).run).cost ≤
          ys.length * (perStep + 2) := by
    induction ys with
    | nil => intro state; simp [Pure.pure, ExceptT.pure, ExceptT.mk, ExceptT.run, pure]
    | cons x ys ih =>
        intro state
        have hx := hh state x (by simp)
        have ht := ih (fun state y hy => hh state y (by simp [hy]))
        simp only [List.foldlM_cons, Bind.bind, ExceptT.bind, ExceptT.mk, ExceptT.run,
          bind, charge]
        cases he : (step state x).value with
        | error error =>
            simp [ExceptT.bindCont, Pure.pure, pure, Nat.succ_mul]
            omega
        | ok next =>
            have hr := ht next
            simp only [ExceptT.mk, ExceptT.run, charge] at hr
            simp only [ExceptT.bindCont, List.length_cons, Nat.succ_mul]
            omega
  simpa [foldArrayExcept_eq_foldlM] using aux xs.toList (by simpa using h) initial

/-- Traverse numeric coordinates in ascending order. The state carries the
cost already incurred, so neither an index list nor deferred additions are
needed. Each callback adds one loop-iteration charge. -/
def foldFin (n : Nat) (initial : α) (step : α → Fin n → Costed α) : Costed α :=
  Fin.foldl n (fun accumulated i =>
    let next := step accumulated.value i
    ⟨next.value, accumulated.cost + 1 + next.cost⟩) (pure initial)

@[simp] theorem foldFin_value (n : Nat) (initial : α) (step : α → Fin n → Costed α) :
    (foldFin n initial step).value =
      Fin.foldl n (fun state i => (step state i).value) initial := by
  induction n with
  | zero => simp [foldFin, pure]
  | succ n ih =>
      simp only [foldFin, Fin.foldl_succ_last]
      change (step (foldFin n initial (fun state i => step state i.castSucc)).value
        (Fin.last n)).value = _
      rw [ih]

theorem foldFin_cost_eq (n : Nat) (initial : α) (step : α → Fin n → Costed α)
    (perStep : Nat) (h : ∀ state i, (step state i).cost = perStep) :
    (foldFin n initial step).cost = n * (perStep + 1) := by
  induction n with
  | zero => simp [foldFin, pure]
  | succ n ih =>
      have hr := ih (fun state i => step state i.castSucc) (fun state i => h state i.castSucc)
      simp only [foldFin, Fin.foldl_succ_last]
      change (foldFin n initial (fun state i => step state i.castSucc)).cost + 1 +
        (step _ (Fin.last n)).cost = _
      rw [hr, h]
      simp [Nat.succ_mul, Nat.add_assoc, Nat.add_comm]

/-- Fold a finite interval from its last index to its first. The recursion
uses numeric indices, without constructing a list. Each applied step charges
one loop iteration in addition to the callback's own operations. -/
def foldFinFromRight {n : Nat} (step : Fin n → α → Costed α) (initial : Costed α) :
    (start remaining : Nat) → start + remaining ≤ n → Costed α
  | _, 0, _ => initial
  | start, remaining + 1, _ =>
      (foldFinFromRight step initial (start + 1) remaining (by omega)).bind
        (fun state => charge 1 (step ⟨start, by omega⟩ state))

theorem foldFinFromRight_value {n : Nat} (step : Fin n → α → Costed α)
    (initial : Costed α) (start remaining : Nat) (h : start + remaining ≤ n) :
    (foldFinFromRight step initial start remaining h).value =
      (List.ofFn (fun i : Fin remaining => (⟨start + i.val, by omega⟩ : Fin n))).foldr
        (fun i state => (step i state).value) initial.value := by
  induction remaining generalizing start with
  | zero => simp [foldFinFromRight]
  | succ remaining ih =>
      rw [List.ofFn_succ]
      simp only [foldFinFromRight, bind_value, charge_value, List.foldr_cons]
      rw [ih]
      congr 1
      congr 1
      congr 1
      apply congrArg List.ofFn
      funext i
      apply Fin.ext
      simp [Nat.add_comm, Nat.add_left_comm]

theorem foldFinFromRight_cost_le {n : Nat} (step : Fin n → α → Costed α)
    (initial : Costed α) (start remaining : Nat) (h : start + remaining ≤ n)
    (perStep : Nat) (hs : ∀ i state, (step i state).cost ≤ perStep) :
    (foldFinFromRight step initial start remaining h).cost ≤
      initial.cost + remaining * (perStep + 1) := by
  induction remaining generalizing start with
  | zero => simp [foldFinFromRight]
  | succ remaining ih =>
      have hr := ih (start + 1) (by omega)
      have hc := hs ⟨start, by omega⟩
        (foldFinFromRight step initial (start + 1) remaining (by omega)).value
      simp only [foldFinFromRight, bind_cost, charge_cost, Nat.succ_mul]
      omega

/-!
Hand-checkable calibration cases for the unit-cost semantics.  These pin down
the distinction between a skipped consequent and an evaluated consequent, and
between the two branches of equivalence. They are exact rather
than asymptotic tests.
-/

example : implies (tick false 1) (fun _ => tick false 7) = ⟨true, 3⟩ := by
  native_decide

example : implies (tick true 1) (fun _ => tick false 2) = ⟨false, 5⟩ := by
  native_decide

example : iff (tick true 1) (fun _ => tick false 2) = ⟨false, 4⟩ := by
  native_decide

example : iff (tick false 1) (fun _ => tick false 2) = ⟨true, 5⟩ := by
  native_decide

end Costed
end LeanUfo.UFO.DSL.Complexity
