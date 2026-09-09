import LeanUfo.UFO.DSL.Complexity.CostModel
import Init.Data.Vector.OfFn

/-!
# Counted Warshall closure

The counted implementation constructs explicit reachability and first-hop
matrices. Its loops accumulate costs for construction, reads, and executed
tests. Inductive proofs give cubic upper bounds and equality to the compact
recurrence. Proved compiler rewrites select the counted erasures at runtime.

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

/-!
The counted cell computations preserve the tests and their order above. A
matrix access costs two array reads: one for the row and one for the cell.
The edge callback below has a one-operation interface; callers must justify
that interface for their explicit edge representation. Vector construction
also counts each row/cell write and each loop iteration.
-/

def initialMatrixCosted (edge : Fin n → Fin n → Bool) : Costed (BoolMatrix n) :=
  Costed.vectorOfFn fun source => Costed.vectorOfFn fun target =>
    Costed.orElse (.tick (decide (source = target))) (fun _ => .tick (edge source target))

def warshallMatrixStepCosted
    (pivot : Fin n) (previous : BoolMatrix n) : Costed (BoolMatrix n) :=
  Costed.vectorOfFn fun source => Costed.vectorOfFn fun target =>
    Costed.orElse (.tick (previous.get source target) 2) fun _ =>
      Costed.andThen (.tick (previous.get source pivot) 2)
        (fun _ => .tick (previous.get pivot target) 2)

def initialNextMatrixCosted (edge : Fin n → Fin n → Bool) : Costed (NextMatrix n) :=
  Costed.vectorOfFn fun source => Costed.vectorOfFn fun target =>
    Costed.branch (.tick (decide (source = target)))
      (fun _ => .pure (some target)) (fun _ =>
        Costed.branch (.tick (edge source target))
          (fun _ => .pure (some target)) (fun _ => .pure none))

def warshallNextMatrixStepCosted
    (pivot : Fin n) (previous : WarshallState n) : Costed (NextMatrix n) :=
  Costed.vectorOfFn fun source => Costed.vectorOfFn fun target =>
    Costed.branch (.tick (previous.reachable.get source target) 2)
      (fun _ => .tick previous.nextHop[source.val][target.val] 2) (fun _ =>
        Costed.branch
          (Costed.andThen (.tick (previous.reachable.get source pivot) 2)
            (fun _ => .tick (previous.reachable.get pivot target) 2))
          (fun _ => .tick previous.nextHop[source.val][pivot.val] 2)
          (fun _ => .pure none))

def initialWarshallStateCosted (edge : Fin n → Fin n → Bool) : Costed (WarshallState n) := do
  let reachable ← initialMatrixCosted edge
  let nextHop ← initialNextMatrixCosted edge
  pure { reachable, nextHop }

def warshallStateStepCosted
    (pivot : Fin n) (previous : WarshallState n) : Costed (WarshallState n) := do
  let reachable ← warshallMatrixStepCosted pivot previous.reachable
  let nextHop ← warshallNextMatrixStepCosted pivot previous
  pure { reachable, nextHop }

@[simp] theorem initialMatrixCosted_value (edge : Fin n → Fin n → Bool) :
    (initialMatrixCosted edge).value = initialMatrix edge := by
  simp [initialMatrixCosted, initialMatrix]

@[simp] theorem warshallMatrixStepCosted_value (pivot : Fin n) (previous : BoolMatrix n) :
    (warshallMatrixStepCosted pivot previous).value = warshallMatrixStep pivot previous := by
  simp [warshallMatrixStepCosted, warshallMatrixStep]

@[simp] theorem initialNextMatrixCosted_value (edge : Fin n → Fin n → Bool) :
    (initialNextMatrixCosted edge).value = initialNextMatrix edge := by
  simp only [initialNextMatrixCosted, initialNextMatrix, Costed.vectorOfFn_value,
    Costed.branch_value, Costed.tick_value, Costed.pure_value, decide_eq_true_eq]
  congr 1

@[simp] theorem initialWarshallStateCosted_value (edge : Fin n → Fin n → Bool) :
    (initialWarshallStateCosted edge).value = initialWarshallState edge := by
  simp [initialWarshallStateCosted, initialWarshallState, Bind.bind, Pure.pure, Costed.bind,
    Costed.pure]

@[simp] theorem warshallStateStepCosted_value (pivot : Fin n) (previous : WarshallState n) :
    (warshallStateStepCosted pivot previous).value = warshallStateStep pivot previous := by
  simp [warshallStateStepCosted, warshallStateStep, warshallNextMatrixStepCosted,
    Bind.bind, Pure.pure, Costed.bind, Costed.pure]

theorem initialMatrixCosted_cost_le (edge : Fin n → Fin n → Bool) :
    (initialMatrixCosted edge).cost ≤ n * (n * 5 + 2) := by
  apply Costed.vectorOfFn_cost_le
  intro source
  apply Costed.vectorOfFn_cost_le (perCell := 3)
  intro target
  exact Costed.orElse_cost_le _ _ 1 1 (by simp) (by simp)

theorem warshallMatrixStepCosted_cost_le (pivot : Fin n) (previous : BoolMatrix n) :
    (warshallMatrixStepCosted pivot previous).cost ≤ n * (n * 10 + 2) := by
  apply Costed.vectorOfFn_cost_le
  intro source
  apply Costed.vectorOfFn_cost_le (perCell := 8)
  intro target
  apply Costed.orElse_cost_le _ _ 2 5 (by simp)
  exact Costed.andThen_cost_le _ _ 2 2 (by simp) (by simp)

theorem initialNextMatrixCosted_cost_le (edge : Fin n → Fin n → Bool) :
    (initialNextMatrixCosted edge).cost ≤ n * (n * 6 + 2) := by
  apply Costed.vectorOfFn_cost_le
  intro source
  apply Costed.vectorOfFn_cost_le (perCell := 4)
  intro target
  apply Costed.branch_cost_le _ _ _ 1 2 (by simp) (by simp)
  exact Costed.branch_cost_le _ _ _ 1 0 (by simp) (by simp) (by simp)

theorem warshallNextMatrixStepCosted_cost_le (pivot : Fin n) (previous : WarshallState n) :
    (warshallNextMatrixStepCosted pivot previous).cost ≤ n * (n * 13 + 2) := by
  apply Costed.vectorOfFn_cost_le
  intro source
  apply Costed.vectorOfFn_cost_le (perCell := 11)
  intro target
  apply Costed.branch_cost_le _ _ _ 2 8 (by simp) (by simp)
  apply Costed.branch_cost_le _ _ _ 5 2
  · exact Costed.andThen_cost_le _ _ 2 2 (by simp) (by simp)
  · simp
  · simp

theorem initialWarshallStateCosted_cost_le (edge : Fin n → Fin n → Bool) :
    (initialWarshallStateCosted edge).cost ≤ n * (n * 11 + 4) := by
  have hr := initialMatrixCosted_cost_le edge
  have hn := initialNextMatrixCosted_cost_le edge
  simp only [initialWarshallStateCosted, Bind.bind, Pure.pure, Costed.bind, Costed.pure,
    Nat.add_zero]
  simp only [Nat.mul_add, ← Nat.mul_assoc] at hr hn ⊢
  omega

theorem warshallStateStepCosted_cost_le (pivot : Fin n) (previous : WarshallState n) :
    (warshallStateStepCosted pivot previous).cost ≤ n * (n * 23 + 4) := by
  have hr := warshallMatrixStepCosted_cost_le pivot previous.reachable
  have hn := warshallNextMatrixStepCosted_cost_le pivot previous
  simp only [warshallStateStepCosted, Bind.bind, Pure.pure, Costed.bind, Costed.pure,
    Nat.add_zero]
  simp only [Nat.mul_add, ← Nat.mul_assoc] at hr hn ⊢
  omega

/-- Produce a row-major array without an uncounted flatten/map pass. Each
output cell charges division, remainder, and the two matrix reads, followed
by `convert` and the constructor's iteration/write charges. -/
def matrixToArrayCosted (matrix : Vector (Vector α n) n) (convert : α → Costed β) :
    Costed (Array β) :=
  (Costed.vectorOfFn fun i : Fin (n * n) =>
    haveI : i.val / n < n :=
      (Nat.div_lt_iff_lt_mul (Nat.pos_of_lt_mul_left i.isLt)).mpr i.isLt
    haveI : i.val % n < n := Nat.mod_lt _ (Nat.pos_of_lt_mul_left i.isLt)
    Costed.charge 4 (convert matrix[i.val / n][i.val % n])).map Vector.toArray

@[simp] theorem matrixToArrayCosted_value
    (matrix : Vector (Vector α n) n) (convert : α → Costed β) :
    (matrixToArrayCosted matrix convert).value =
      matrix.flatten.toArray.map (fun x => (convert x).value) := by
  simp only [matrixToArrayCosted, Costed.map_value, Costed.vectorOfFn_value,
    Costed.charge_value]
  ext i hi
  · simp
  · simp

theorem matrixToArrayCosted_cost_le
    (matrix : Vector (Vector α n) n) (convert : α → Costed β) (perCell : Nat)
    (h : ∀ x, (convert x).cost ≤ perCell) :
    (matrixToArrayCosted matrix convert).cost ≤ n * n * (perCell + 6) := by
  apply Costed.vectorOfFn_cost_le (perCell := perCell + 4)
  intro i
  simp only [Costed.charge_cost]
  rw [Nat.add_comm]
  exact Nat.add_le_add_right (h _) 4

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
Compute reachability and next-hop evidence with counted matrix construction
and short-circuit cell tests. Pivots run from `n - 1` down to zero, preserving
the compact specification's deterministic choice among possible paths.
-/
def warshallStateCosted
    (n : Nat) (edge : Fin n → Fin n → Bool) : Costed (WarshallState n) :=
  Costed.foldFinFromRight warshallStateStepCosted
    (initialWarshallStateCosted edge) 0 n (by omega)

/-- Compact production closure. Keeping this definition free of cost packaging
prevents generated certificate reduction from expanding instrumentation. -/
def warshallState (n : Nat) (edge : Fin n → Fin n → Bool) : WarshallState n :=
  warshallViaState edge (List.finRange n)

@[simp] theorem warshallStateCosted_value
    (n : Nat) (edge : Fin n → Fin n → Bool) :
    (warshallStateCosted n edge).value = warshallState n edge := by
  have h (pivots : List (Fin n)) :
      pivots.foldr warshallStateStep (initialWarshallState edge) =
        warshallViaState edge pivots := by
    induction pivots with
    | nil => rfl
    | cons pivot pivots ih => simp [warshallViaState, ih]
  simpa [warshallStateCosted, Costed.foldFinFromRight_value,
    warshallState, List.finRange] using h (List.finRange n)

theorem warshallStateCosted_cost_le
    (n : Nat) (edge : Fin n → Fin n → Bool) :
    (warshallStateCosted n edge).cost ≤ 23 * n ^ 3 + 15 * n ^ 2 + 5 * n := by
  have h := Costed.foldFinFromRight_cost_le warshallStateStepCosted
    (initialWarshallStateCosted edge) 0 n (by omega) (n * (n * 23 + 4))
    warshallStateStepCosted_cost_le
  have hi := initialWarshallStateCosted_cost_le edge
  simp only [warshallStateCosted]
  apply Nat.le_trans h
  apply Nat.le_trans (Nat.add_le_add_right hi _)
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.mul_one, Nat.mul_add, Nat.mul_comm,
    Nat.mul_assoc]
  simp only [← Nat.mul_assoc]
  omega

private def warshallStateErased (n : Nat) (edge : Fin n → Fin n → Bool) : WarshallState n :=
  (warshallStateCosted n edge).value

/-- Native execution uses the counted core's erasure. The kernel keeps the
compact recurrence above. Unlike an unchecked replacement, this compiler
rewrite requires an unconditional equality of the two functions. -/
@[csimp] theorem warshallState_eq_erased : @warshallState = @warshallStateErased := by
  funext n edge
  exact (warshallStateCosted_value n edge).symm

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
  Costed.foldFinFromRight warshallMatrixStepCosted
    (initialMatrixCosted edge) 0 n (by omega)

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
    (warshallMatrixCosted n edge).value = warshallMatrix n edge := by
  have h (pivots : List (Fin n)) :
      pivots.foldr warshallMatrixStep (initialMatrix edge) =
        (warshallViaState edge pivots).reachable := by
    induction pivots with
    | nil => rfl
    | cons pivot pivots ih => simp [warshallViaState, warshallStateStep, ih]
  simpa [warshallMatrixCosted, Costed.foldFinFromRight_value,
    warshallMatrix, warshallViaMatrix, List.finRange] using h (List.finRange n)

theorem warshallMatrixCosted_cost_le
    (n : Nat) (edge : Fin n → Fin n → Bool) :
    (warshallMatrixCosted n edge).cost ≤ 10 * n ^ 3 + 7 * n ^ 2 + 3 * n := by
  have h := Costed.foldFinFromRight_cost_le warshallMatrixStepCosted
    (initialMatrixCosted edge) 0 n (by omega) (n * (n * 10 + 2))
    warshallMatrixStepCosted_cost_le
  have hi := initialMatrixCosted_cost_le edge
  simp only [warshallMatrixCosted]
  apply Nat.le_trans h
  apply Nat.le_trans (Nat.add_le_add_right hi _)
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.mul_one, Nat.mul_add, Nat.mul_comm,
    Nat.mul_assoc]
  simp only [← Nat.mul_assoc]
  omega

private def warshallMatrixErased (n : Nat) (edge : Fin n → Fin n → Bool) : BoolMatrix n :=
  (warshallMatrixCosted n edge).value

/-- The matrix-only executable omits first-hop construction. Equality to the
specification is proved before native compilation selects that executable. -/
@[csimp] theorem warshallMatrix_eq_erased : @warshallMatrix = @warshallMatrixErased := by
  funext n edge
  exact (warshallMatrixCosted_value n edge).symm

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

theorem warshallMatrixCostBound_mono {n m : Nat} (h : n ≤ m) :
    10 * n ^ 3 + 7 * n ^ 2 + 3 * n ≤ 10 * m ^ 3 + 7 * m ^ 2 + 3 * m := by
  exact Nat.add_le_add
    (Nat.add_le_add
      (Nat.mul_le_mul_left 10 (Nat.pow_le_pow_left h 3))
      (Nat.mul_le_mul_left 7 (Nat.pow_le_pow_left h 2)))
    (Nat.mul_le_mul_left 3 h)

-- For one vertex, initialization costs 12, the pivot costs 16, and its
-- iteration costs one. Reachability alone costs 6 + 7 + 1. With no vertices,
-- neither constructor nor pivot loop visits a cell.
-- These native regressions exercise the compiled loops. The general cost and
-- correspondence proofs above do not depend on native evaluation.
example : (warshallStateCosted 0 (fun _ _ => false)).cost = 0 := by native_decide
example : (warshallMatrixCosted 0 (fun _ _ => false)).cost = 0 := by native_decide
example : (warshallStateCosted 1 (fun _ _ => false)).cost = 29 := by native_decide
example : (warshallMatrixCosted 1 (fun _ _ => false)).cost = 14 := by native_decide

-- Exact work can decrease when edges are added: established reachability
-- skips later tests. Only the worst-case size bound is monotone.
example : (warshallStateCosted 2 (fun _ _ => false)).cost = 188 := by native_decide
example : (warshallStateCosted 2 (fun _ _ => true)).cost = 160 := by native_decide

private def threeCycleEdge (i j : Fin 3) : Bool :=
  (i.val == 0 && j.val == 1) || (i.val == 1 && j.val == 2) ||
    (i.val == 2 && j.val == 0)

/-- Dense cyclic reachability is computed by the fixed cubic loop. -/
example : (warshallMatrix 3 threeCycleEdge).flatten.toArray =
    #[true, true, true, true, true, true, true, true, true] := by
  native_decide

example : (warshallMatrixCosted 3 threeCycleEdge).cost ≤ 342 :=
  warshallMatrixCosted_cost_le 3 threeCycleEdge

example : (warshallState 3 threeCycleEdge).nextHop[0][2] =
    some (⟨1, by decide⟩ : Fin 3) := by
  native_decide

example : (warshallStateCosted 3 threeCycleEdge).cost ≤ 771 :=
  warshallStateCosted_cost_le 3 threeCycleEdge

end LeanUfo.UFO.DSL.Complexity
