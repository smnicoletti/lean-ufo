import LeanUfo.UFO.DSL.Complexity.CostModel

/-!
# Output-sensitive diagnostic costs

This module provides the deterministic output-limiter primitives. The counted
production analysis and its complete input-and-output bound are in
`Diagnostic.Analysis`, where the specialized axiom analyzers are available.
-/

namespace LeanUfo.UFO.DSL.Complexity

/-- Bounded diagnostic output with deterministic truncation. -/
structure BoundedEvidence (α : Type u) where
  items : Array α
  truncated : Bool
deriving Repr, Inhabited, DecidableEq

/--
Take at most `budget` items. The cost charges one operation per inspected and
emitted item, so diagnostics remain separate and output-sensitive.
-/
def boundedEvidenceCosted (budget : Nat) (items : Array α) : Costed (BoundedEvidence α) :=
  let kept := items.extract 0 (min budget items.size)
  ⟨{ items := kept, truncated := budget < items.size }, 2 * kept.size + 1⟩

def boundedEvidence (budget : Nat) (items : Array α) : BoundedEvidence α :=
  (boundedEvidenceCosted budget items).value

@[simp] theorem boundedEvidenceCosted_value (budget : Nat) (items : Array α) :
    (boundedEvidenceCosted budget items).value = boundedEvidence budget items := rfl

theorem boundedEvidenceCosted_cost (budget : Nat) (items : Array α) :
    (boundedEvidenceCosted budget items).cost =
      2 * min budget items.size + 1 := by
  simp [boundedEvidenceCosted]

theorem boundedEvidence_size_le_budget (budget : Nat) (items : Array α) :
    (boundedEvidence budget items).items.size ≤ budget := by
  simpa [boundedEvidence, boundedEvidenceCosted] using
    Nat.min_le_left budget items.size

theorem boundedEvidence_size_le_input (budget : Nat) (items : Array α) :
    (boundedEvidence budget items).items.size ≤ items.size := by
  simpa [boundedEvidence, boundedEvidenceCosted] using
    Nat.min_le_right budget items.size

/-- Output-sensitive form: the evidence limiter costs two operations per
emitted item plus the final truncation comparison. -/
theorem boundedEvidenceCosted_cost_eq_emitted (budget : Nat) (items : Array α) :
    (boundedEvidenceCosted budget items).cost =
      2 * (boundedEvidence budget items).items.size + 1 := by
  simp [boundedEvidence, boundedEvidenceCosted]

example : boundedEvidenceCosted 2 #["a", "b", "c"] =
    ⟨{ items := #["a", "b"], truncated := true }, 5⟩ := by
  native_decide

example : boundedEvidenceCosted 4 #["a", "b"] =
    ⟨{ items := #["a", "b"], truncated := false }, 5⟩ := by
  native_decide

end LeanUfo.UFO.DSL.Complexity
