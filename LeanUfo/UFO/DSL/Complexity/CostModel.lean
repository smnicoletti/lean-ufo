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

def pure (value : α) : Costed α := ⟨value, 0⟩

def tick (value : α) (cost : Nat := 1) : Costed α := ⟨value, cost⟩

def map (f : α → β) (x : Costed α) : Costed β :=
  ⟨f x.value, x.cost⟩

def bind (x : Costed α) (f : α → Costed β) : Costed β :=
  let y := f x.value
  ⟨y.value, x.cost + y.cost⟩

instance : Monad Costed where
  pure := pure
  bind := bind

def charge (extra : Nat) (x : Costed α) : Costed α :=
  ⟨x.value, extra + x.cost⟩

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
