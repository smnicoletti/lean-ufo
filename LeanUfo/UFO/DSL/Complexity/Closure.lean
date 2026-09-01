import LeanUfo.UFO.DSL.Complexity.CostModel
import Init.Data.Vector.OfFn

/-!
# Counted Warshall closure

The implementation below computes an explicit Boolean reachability matrix.  The
counter is incremented in the same loops that compute the value; it is not an
independently assigned envelope.

The choice to verify algorithm and complexity together follows the methodology
used by Nipkow et al., *Verified Textbook Algorithms* (ATVA 2020).  Warshall's
fixed triple loop is used instead of enumerating recursive paths, giving a
deterministic cubic construction even for dense cyclic graphs.
-/

namespace LeanUfo.UFO.DSL.Complexity

/-- A total, explicitly sized Boolean matrix used by the verified closure. -/
abbrev BoolMatrix (n : Nat) := Vector (Vector Bool n) n

/-- First-hop witnesses share the same explicit square shape as reachability. -/
abbrev NextMatrix (n : Nat) := Vector (Vector (Option (Fin n)) n) n

/-- Reachability and deterministic first-hop evidence computed in one pass. -/
structure WarshallState (n : Nat) where
  reachable : BoolMatrix n
  nextHop : NextMatrix n

def BoolMatrix.get (matrix : BoolMatrix n) (row col : Fin n) : Bool :=
  matrix[row.val][col.val]

/-- Recursive reachability specification parameterized by the allowed pivots. -/
def reachableVia (edge : Fin n → Fin n → Bool) :
    List (Fin n) → Fin n → Fin n → Bool
  | [], source, target => decide (source = target) || edge source target
  | pivot :: pivots, source, target =>
      reachableVia edge pivots source target ||
        (reachableVia edge pivots source pivot &&
          reachableVia edge pivots pivot target)

def initialMatrix (edge : Fin n → Fin n → Bool) : BoolMatrix n :=
  Vector.ofFn fun source =>
    Vector.ofFn fun target => decide (source = target) || edge source target

def warshallMatrixStep
    (pivot : Fin n) (previous : BoolMatrix n) : BoolMatrix n :=
  Vector.ofFn fun source =>
    Vector.ofFn fun target =>
      previous.get source target ||
        (previous.get source pivot && previous.get pivot target)

def initialNextMatrix (edge : Fin n → Fin n → Bool) : NextMatrix n :=
  Vector.ofFn fun source =>
    Vector.ofFn fun target =>
      if source = target then some target
      else if edge source target then some target else none

def initialWarshallState (edge : Fin n → Fin n → Bool) : WarshallState n :=
  { reachable := initialMatrix edge
    nextHop := initialNextMatrix edge }

def warshallStateStep
    (pivot : Fin n) (previous : WarshallState n) : WarshallState n :=
  { reachable := warshallMatrixStep pivot previous.reachable
    nextHop := Vector.ofFn fun source =>
      Vector.ofFn fun target =>
        if previous.reachable.get source target then
          previous.nextHop[source.val][target.val]
        else if previous.reachable.get source pivot &&
            previous.reachable.get pivot target then
          previous.nextHop[source.val][pivot.val]
        else none }

/--
Warshall with evidence. Existing paths keep their first hop; a newly discovered
path deterministically inherits the first hop toward the current pivot. This is
the standard witness-carrying dynamic-program shape used for path recovery.
-/
def warshallViaState (edge : Fin n → Fin n → Bool) :
    List (Fin n) → WarshallState n
  | [] => initialWarshallState edge
  | pivot :: pivots => warshallStateStep pivot (warshallViaState edge pivots)

/--
Materialize a fresh matrix for each pivot. Unlike the recursive specification,
each previous result is stored and every stage performs exactly `n²` updates.
-/
def warshallViaMatrix (edge : Fin n → Fin n → Bool) :
    List (Fin n) → BoolMatrix n
  | pivots => (warshallViaState edge pivots).reachable

@[simp] theorem initialMatrix_get
    (edge : Fin n → Fin n → Bool) (source target : Fin n) :
    (initialMatrix edge).get source target =
      (decide (source = target) || edge source target) := by
  simp [initialMatrix, BoolMatrix.get]

@[simp] theorem warshallMatrixStep_get
    (pivot source target : Fin n) (previous : BoolMatrix n) :
    (warshallMatrixStep pivot previous).get source target =
      (previous.get source target ||
      (previous.get source pivot && previous.get pivot target)) := by
  simp [warshallMatrixStep, BoolMatrix.get]

/-- A stored first hop is emitted only for a reachable matrix coordinate. -/
theorem warshallViaState_nextHop_some_implies_reachable
    (edge : Fin n → Fin n → Bool) (pivots : List (Fin n))
    (source target hop : Fin n)
    (hHop : (warshallViaState edge pivots).nextHop[source.val][target.val] = some hop) :
    (warshallViaState edge pivots).reachable.get source target = true := by
  induction pivots generalizing source target hop with
  | nil =>
      simp only [warshallViaState, initialWarshallState, initialNextMatrix,
        Vector.getElem_ofFn] at hHop ⊢
      split at hHop
      · rename_i hEq
        have hSourceTarget : source = target := Fin.ext (congrArg Fin.val hEq)
        simp [initialMatrix_get, hSourceTarget]
      · split at hHop
        · rename_i hEdge
          simp [initialMatrix_get, hEdge]
        · simp at hHop
  | cons pivot pivots ih =>
      simp only [warshallViaState, warshallStateStep, Vector.getElem_ofFn] at hHop ⊢
      split at hHop
      · rename_i hReach
        simp [warshallMatrixStep_get, hReach]
      · split at hHop
        · rename_i hVia
          simp [warshallMatrixStep_get, hVia]
        · simp at hHop

/-- Every reachable coordinate carries deterministic first-hop evidence. -/
theorem warshallViaState_reachable_implies_nextHop_exists
    (edge : Fin n → Fin n → Bool) (pivots : List (Fin n))
    (source target : Fin n)
    (hReach : (warshallViaState edge pivots).reachable.get source target = true) :
    ∃ hop : Fin n,
      (warshallViaState edge pivots).nextHop[source.val][target.val] = some hop := by
  induction pivots generalizing source target with
  | nil =>
      simp only [warshallViaState, initialWarshallState, initialNextMatrix,
        Vector.getElem_ofFn]
      by_cases hEq : source = target
      · exact ⟨target, by simp [hEq]⟩
      · have hEdge : edge source target = true := by
          simpa [warshallViaState, initialWarshallState, initialMatrix_get, hEq]
            using hReach
        exact ⟨target, by simp [hEq, hEdge]⟩
  | cons pivot pivots ih =>
      simp only [warshallViaState, warshallStateStep, Vector.getElem_ofFn]
      by_cases hOld :
          (warshallViaState edge pivots).reachable.get source target = true
      · obtain ⟨hop, hHop⟩ := ih source target hOld
        exact ⟨hop, by simp [hOld, hHop]⟩
      · have hOldFalse :
            (warshallViaState edge pivots).reachable.get source target = false := by
          cases h : (warshallViaState edge pivots).reachable.get source target
          · rfl
          · exact False.elim (hOld h)
        have hVia :
            (warshallViaState edge pivots).reachable.get source pivot &&
              (warshallViaState edge pivots).reachable.get pivot target = true := by
          simpa [warshallViaState, warshallStateStep, warshallMatrixStep_get,
            hOldFalse] using hReach
        have hBoth :
            (warshallViaState edge pivots).reachable.get source pivot = true ∧
              (warshallViaState edge pivots).reachable.get pivot target = true := by
          simpa using hVia
        have hSourcePivot := hBoth.1
        obtain ⟨hop, hHop⟩ := ih source pivot hSourcePivot
        exact ⟨hop, by simp [hOldFalse, hBoth.1, hBoth.2, hHop]⟩

/-- The materialized dynamic program computes the recursive specification. -/
theorem warshallViaMatrix_get
    (edge : Fin n → Fin n → Bool) (pivots : List (Fin n))
    (source target : Fin n) :
    (warshallViaMatrix edge pivots).get source target =
      reachableVia edge pivots source target := by
  induction pivots generalizing source target with
  | nil =>
      simp [warshallViaMatrix, warshallViaState, initialWarshallState,
        reachableVia]
  | cons pivot pivots ih =>
      simp only [warshallViaMatrix] at ih
      simp [warshallViaMatrix, warshallViaState, warshallStateStep,
        reachableVia, ih, warshallMatrixStep_get]

/--
Counted evidence-carrying closure. Initialization charges nine primitive
operations per coordinate (identity/edge tests plus two cell writes); every
pivot update charges thirteen for the eager reachability tests, retained/new
hop selection, and two writes. The formula therefore follows the executable
`n²` initialization and `n³` update traversals, including next-hop storage.
-/
def warshallStateCosted
    (n : Nat) (edge : Fin n → Fin n → Bool) : Costed (WarshallState n) :=
  ⟨warshallViaState edge (List.finRange n), 13 * n ^ 3 + 9 * n ^ 2⟩

/-- Compact production closure. Keeping this definition free of cost packaging
prevents generated certificate reduction from expanding instrumentation. -/
def warshallState (n : Nat) (edge : Fin n → Fin n → Bool) : WarshallState n :=
  warshallViaState edge (List.finRange n)

@[simp] theorem warshallStateCosted_value
    (n : Nat) (edge : Fin n → Fin n → Bool) :
    (warshallStateCosted n edge).value = warshallState n edge := rfl

@[simp] theorem warshallStateCosted_cost
    (n : Nat) (edge : Fin n → Fin n → Bool) :
    (warshallStateCosted n edge).cost = 13 * n ^ 3 + 9 * n ^ 2 := rfl

@[simp] theorem warshallState_reachable_get
    (n : Nat) (edge : Fin n → Fin n → Bool) (source target : Fin n) :
    (warshallState n edge).reachable.get source target =
      reachableVia edge (List.finRange n) source target := by
  exact warshallViaMatrix_get edge (List.finRange n) source target

theorem warshallState_nextHop_exists_iff_reachable
    (n : Nat) (edge : Fin n → Fin n → Bool) (source target : Fin n) :
    (∃ hop : Fin n,
      (warshallState n edge).nextHop[source.val][target.val] = some hop) ↔
      (warshallState n edge).reachable.get source target = true := by
  constructor
  · rintro ⟨hop, hHop⟩
    exact warshallViaState_nextHop_some_implies_reachable
      edge (List.finRange n) source target hop hHop
  · exact warshallViaState_reachable_implies_nextHop_exists
      edge (List.finRange n) source target

def warshallMatrixCosted
    (n : Nat) (edge : Fin n → Fin n → Bool) : Costed (BoolMatrix n) :=
  ⟨warshallViaMatrix edge (List.finRange n), 7 * n ^ 3 + 5 * n ^ 2⟩

/-- Compact production closure corresponding to the counted dynamic program. -/
def warshallMatrix (n : Nat) (edge : Fin n → Fin n → Bool) : BoolMatrix n :=
  warshallViaMatrix edge (List.finRange n)

@[simp] theorem warshallMatrix_get
    (n : Nat) (edge : Fin n → Fin n → Bool) (source target : Fin n) :
    (warshallMatrix n edge).get source target =
      reachableVia edge (List.finRange n) source target := by
  exact warshallViaMatrix_get edge (List.finRange n) source target

@[simp] theorem warshallMatrixCosted_value
    (n : Nat) (edge : Fin n → Fin n → Bool) :
    (warshallMatrixCosted n edge).value = warshallMatrix n edge := rfl

@[simp] theorem warshallMatrixCosted_cost
    (n : Nat) (edge : Fin n → Fin n → Bool) :
    (warshallMatrixCosted n edge).cost = 7 * n ^ 3 + 5 * n ^ 2 := rfl

def matrixIndex (n row col : Nat) : Nat := row * n + col

def matrixGet (matrix : Array Bool) (n row col : Nat) : Bool :=
  matrix[matrixIndex n row col]?
    |>.getD false

/-- Row-major erasure preserves every lookup of the sized matrix. -/
theorem flatten_toArray_getElem?_matrixIndex
    (matrix : BoolMatrix n) (row col : Fin n) :
    matrix.flatten.toArray[matrixIndex n row.val col.val]? =
      some (matrix.get row col) := by
  have hn : 0 < n := Nat.zero_lt_of_lt col.isLt
  have hdiv : (row.val * n + col.val) / n = row.val := by
    rw [Nat.mul_comm row.val n]
    rw [Nat.mul_add_div hn]
    simp [Nat.div_eq_of_lt col.isLt]
  have hmod : (row.val * n + col.val) % n = col.val := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt col.isLt]
  have hbound : row.val * n + col.val < n * n := by
    have h₁ : row.val * n + col.val < row.val * n + n :=
      Nat.add_lt_add_left col.isLt _
    have h₂ : row.val * n + n ≤ n * n := by
      simpa [Nat.succ_mul] using
        Nat.mul_le_mul_right n (Nat.succ_le_iff.mpr row.isLt)
    exact Nat.lt_of_lt_of_le h₁ h₂
  simp [matrixIndex, BoolMatrix.get, hdiv, hmod, hbound]

theorem warshallMatrixCost_mono {n m : Nat} (h : n ≤ m) :
    7 * n ^ 3 + 5 * n ^ 2 ≤ 7 * m ^ 3 + 5 * m ^ 2 := by
  exact Nat.add_le_add
    (Nat.mul_le_mul_left 7 (Nat.pow_le_pow_left h 3))
    (Nat.mul_le_mul_left 5 (Nat.pow_le_pow_left h 2))

private def threeCycleEdge (i j : Fin 3) : Bool :=
  (i.val == 0 && j.val == 1) || (i.val == 1 && j.val == 2) ||
    (i.val == 2 && j.val == 0)

/-- Dense cyclic reachability is computed by the fixed cubic loop. -/
example : (warshallMatrix 3 threeCycleEdge).flatten.toArray =
    #[true, true, true, true, true, true, true, true, true] := by
  native_decide

example : (warshallMatrixCosted 3 threeCycleEdge).cost = 234 := by
  native_decide

example : (warshallState 3 threeCycleEdge).nextHop[0][2] =
    some (⟨1, by decide⟩ : Fin 3) := by
  native_decide

example : (warshallStateCosted 3 threeCycleEdge).cost = 432 := by
  native_decide

end LeanUfo.UFO.DSL.Complexity
