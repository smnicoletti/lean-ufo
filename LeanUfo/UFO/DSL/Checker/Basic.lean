import Lean.Meta.Tactic.Simp
import LeanUfo.UFO.DSL.FiniteModel
import LeanUfo.UFO.DSL.Complexity.Checker

/-!
# Reflective checker basics

This module introduces the small Boolean vocabulary used by the reflective
checker. The combinators expose the finite worlds and things of a
`FiniteModel4` as executable Boolean quantifiers, so axiom checkers can be
written as ordinary finite scans over the compiled model.
-/

/-- Opt-in simp set for rewriting UFO semantic axioms to executable checker obligations. -/
register_simp_attr ufo_checker

namespace LeanUfo.UFO.DSL
namespace Checker

/-- Counted universal thing-quantifier whose body contributes its own cost. -/
def allThingsEvalCosted (M : FiniteModel4)
    (p : Fin M.thingCount → Complexity.Costed Bool) : Complexity.Costed Bool :=
  Complexity.allListCosted (List.finRange M.thingCount) p

/-- Counted existential thing-quantifier whose body contributes its own cost. -/
def anyThingsEvalCosted (M : FiniteModel4)
    (p : Fin M.thingCount → Complexity.Costed Bool) : Complexity.Costed Bool :=
  Complexity.anyListCosted (List.finRange M.thingCount) p

/-- Counted universal world-quantifier whose body contributes its own cost. -/
def allWorldsEvalCosted (M : FiniteModel4)
    (p : Fin M.worldCount → Complexity.Costed Bool) : Complexity.Costed Bool :=
  Complexity.allListCosted (List.finRange M.worldCount) p

/-- Counted existential world-quantifier whose body contributes its own cost. -/
def anyWorldsEvalCosted (M : FiniteModel4)
    (p : Fin M.worldCount → Complexity.Costed Bool) : Complexity.Costed Bool :=
  Complexity.anyListCosted (List.finRange M.worldCount) p

/-- Counted universal scan over an arbitrary finite index type. Product-family
dimensions are heterogeneous, so their size cannot be replaced by the model's
global thing count. -/
def allFinEvalCosted (n : Nat)
    (p : Fin n → Complexity.Costed Bool) : Complexity.Costed Bool :=
  Complexity.allListCosted (List.finRange n) p

/-- Counted existential scan over an arbitrary finite index type. -/
def anyFinEvalCosted (n : Nat)
    (p : Fin n → Complexity.Costed Bool) : Complexity.Costed Bool :=
  Complexity.anyListCosted (List.finRange n) p

def allThingsCosted (M : FiniteModel4) (p : Fin M.thingCount → Bool) :
    Complexity.Costed Bool :=
  allThingsEvalCosted M
    (fun x => .tick (p x) 1)

def allThings (M : FiniteModel4) (p : Fin M.thingCount → Bool) : Bool :=
  (allThingsCosted M p).value

def anyThingsCosted (M : FiniteModel4) (p : Fin M.thingCount → Bool) :
    Complexity.Costed Bool :=
  anyThingsEvalCosted M
    (fun x => .tick (p x) 1)

def anyThings (M : FiniteModel4) (p : Fin M.thingCount → Bool) : Bool :=
  (anyThingsCosted M p).value

def allWorldsCosted (M : FiniteModel4) (p : Fin M.worldCount → Bool) :
    Complexity.Costed Bool :=
  allWorldsEvalCosted M
    (fun w => .tick (p w) 1)

def allWorlds (M : FiniteModel4) (p : Fin M.worldCount → Bool) : Bool :=
  (allWorldsCosted M p).value

def anyWorldsCosted (M : FiniteModel4) (p : Fin M.worldCount → Bool) :
    Complexity.Costed Bool :=
  anyWorldsEvalCosted M
    (fun w => .tick (p w) 1)

def anyWorlds (M : FiniteModel4) (p : Fin M.worldCount → Bool) : Bool :=
  (anyWorldsCosted M p).value

def boxWorlds (M : FiniteModel4) : (Fin M.worldCount → Bool) → Bool :=
  allWorlds M

def diaWorlds (M : FiniteModel4) : (Fin M.worldCount → Bool) → Bool :=
  anyWorlds M

theorem allThingsEvalCosted_cost_le (M : FiniteModel4)
    (p : Fin M.thingCount → Complexity.Costed Bool) (perThing : Nat)
    (h : ∀ x, (p x).cost ≤ perThing) :
    (allThingsEvalCosted M p).cost ≤ M.thingCount * (perThing + 2) := by
  unfold allThingsEvalCosted
  have bound := Complexity.allListCosted_cost_le
    (List.finRange M.thingCount) p perThing (by intro x _; exact h x)
  simpa using bound

theorem allWorldsEvalCosted_cost_le (M : FiniteModel4)
    (p : Fin M.worldCount → Complexity.Costed Bool) (perWorld : Nat)
    (h : ∀ w, (p w).cost ≤ perWorld) :
    (allWorldsEvalCosted M p).cost ≤ M.worldCount * (perWorld + 2) := by
  unfold allWorldsEvalCosted
  have bound := Complexity.allListCosted_cost_le
    (List.finRange M.worldCount) p perWorld (by intro w _; exact h w)
  simpa using bound

theorem anyThingsEvalCosted_cost_le (M : FiniteModel4)
    (p : Fin M.thingCount → Complexity.Costed Bool) (perThing : Nat)
    (h : ∀ x, (p x).cost ≤ perThing) :
    (anyThingsEvalCosted M p).cost ≤ M.thingCount * (perThing + 2) := by
  unfold anyThingsEvalCosted
  have bound := Complexity.anyListCosted_cost_le
    (List.finRange M.thingCount) p perThing (by intro x _; exact h x)
  simpa using bound

theorem anyWorldsEvalCosted_cost_le (M : FiniteModel4)
    (p : Fin M.worldCount → Complexity.Costed Bool) (perWorld : Nat)
    (h : ∀ w, (p w).cost ≤ perWorld) :
    (anyWorldsEvalCosted M p).cost ≤ M.worldCount * (perWorld + 2) := by
  unfold anyWorldsEvalCosted
  have bound := Complexity.anyListCosted_cost_le
    (List.finRange M.worldCount) p perWorld (by intro w _; exact h w)
  simpa using bound

theorem allFinEvalCosted_cost_le (n : Nat)
    (p : Fin n → Complexity.Costed Bool) (perItem : Nat)
    (h : ∀ i, (p i).cost ≤ perItem) :
    (allFinEvalCosted n p).cost ≤ n * (perItem + 2) := by
  unfold allFinEvalCosted
  have bound := Complexity.allListCosted_cost_le
    (List.finRange n) p perItem (by intro i _; exact h i)
  simpa using bound

theorem anyFinEvalCosted_cost_le (n : Nat)
    (p : Fin n → Complexity.Costed Bool) (perItem : Nat)
    (h : ∀ i, (p i).cost ≤ perItem) :
    (anyFinEvalCosted n p).cost ≤ n * (perItem + 2) := by
  unfold anyFinEvalCosted
  have bound := Complexity.anyListCosted_cost_le
    (List.finRange n) p perItem (by intro i _; exact h i)
  simpa using bound

theorem anyFinEvalCosted_cost_le_sum (n : Nat)
    (p : Fin n → Complexity.Costed Bool) (bound : Fin n → Nat)
    (h : ∀ i, (p i).cost ≤ bound i) :
    (anyFinEvalCosted n p).cost ≤
      ((List.finRange n).map fun i => bound i + 2).sum := by
  unfold anyFinEvalCosted
  apply Complexity.anyListCosted_cost_le_sum
  intro i _
  exact h i

theorem allFinEvalCosted_value (n : Nat)
    (p : Fin n → Complexity.Costed Bool) :
    (allFinEvalCosted n p).value = decide (∀ i : Fin n, (p i).value = true) := by
  apply Bool.eq_iff_iff.mpr
  unfold allFinEvalCosted
  rw [Complexity.allListCosted_eq_true_iff, decide_eq_true_iff]
  simp

theorem anyFinEvalCosted_value (n : Nat)
    (p : Fin n → Complexity.Costed Bool) :
    (anyFinEvalCosted n p).value = decide (∃ i : Fin n, (p i).value = true) := by
  apply Bool.eq_iff_iff.mpr
  unfold anyFinEvalCosted
  rw [Complexity.anyListCosted_eq_true_iff, decide_eq_true_iff]
  simp

theorem allThings_eq_true_iff (M : FiniteModel4) (p : Fin M.thingCount → Bool) :
    allThings M p = true ↔ ∀ x : Fin M.thingCount, p x = true := by
  unfold allThings allThingsCosted allThingsEvalCosted
  rw [Complexity.allListCosted_eq_true_iff]
  simp

theorem anyThings_eq_true_iff (M : FiniteModel4) (p : Fin M.thingCount → Bool) :
    anyThings M p = true ↔ ∃ x : Fin M.thingCount, p x = true := by
  unfold anyThings anyThingsCosted anyThingsEvalCosted
  rw [Complexity.anyListCosted_eq_true_iff]
  simp

theorem allWorlds_eq_true_iff (M : FiniteModel4) (p : Fin M.worldCount → Bool) :
    allWorlds M p = true ↔ ∀ w : Fin M.worldCount, p w = true := by
  unfold allWorlds allWorldsCosted allWorldsEvalCosted
  rw [Complexity.allListCosted_eq_true_iff]
  simp

theorem anyWorlds_eq_true_iff (M : FiniteModel4) (p : Fin M.worldCount → Bool) :
    anyWorlds M p = true ↔ ∃ w : Fin M.worldCount, p w = true := by
  unfold anyWorlds anyWorldsCosted anyWorldsEvalCosted
  rw [Complexity.anyListCosted_eq_true_iff]
  simp

theorem allThingsEvalCosted_value (M : FiniteModel4)
    (p : Fin M.thingCount → Complexity.Costed Bool) :
    (allThingsEvalCosted M p).value = allThings M (fun x => (p x).value) := by
  apply Bool.eq_iff_iff.mpr
  unfold allThingsEvalCosted
  rw [Complexity.allListCosted_eq_true_iff, allThings_eq_true_iff]
  simp

theorem anyThingsEvalCosted_value (M : FiniteModel4)
    (p : Fin M.thingCount → Complexity.Costed Bool) :
    (anyThingsEvalCosted M p).value = anyThings M (fun x => (p x).value) := by
  apply Bool.eq_iff_iff.mpr
  unfold anyThingsEvalCosted
  rw [Complexity.anyListCosted_eq_true_iff, anyThings_eq_true_iff]
  simp

theorem allWorldsEvalCosted_value (M : FiniteModel4)
    (p : Fin M.worldCount → Complexity.Costed Bool) :
    (allWorldsEvalCosted M p).value = allWorlds M (fun w => (p w).value) := by
  apply Bool.eq_iff_iff.mpr
  unfold allWorldsEvalCosted
  rw [Complexity.allListCosted_eq_true_iff, allWorlds_eq_true_iff]
  simp

theorem anyWorldsEvalCosted_value (M : FiniteModel4)
    (p : Fin M.worldCount → Complexity.Costed Bool) :
    (anyWorldsEvalCosted M p).value = anyWorlds M (fun w => (p w).value) := by
  apply Bool.eq_iff_iff.mpr
  unfold anyWorldsEvalCosted
  rw [Complexity.anyListCosted_eq_true_iff, anyWorlds_eq_true_iff]
  simp

@[simp] theorem allThingsCosted_value_eq_decide
    (M : FiniteModel4) (p : Fin M.thingCount → Bool) :
    (allThingsCosted M p).value = decide (∀ x, p x = true) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff]
  exact allThings_eq_true_iff M p

@[simp] theorem anyThingsCosted_value_eq_decide
    (M : FiniteModel4) (p : Fin M.thingCount → Bool) :
    (anyThingsCosted M p).value = decide (∃ x, p x = true) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff]
  exact anyThings_eq_true_iff M p

@[simp] theorem allWorldsCosted_value_eq_decide
    (M : FiniteModel4) (p : Fin M.worldCount → Bool) :
    (allWorldsCosted M p).value = decide (∀ w, p w = true) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff]
  exact allWorlds_eq_true_iff M p

@[simp] theorem anyWorldsCosted_value_eq_decide
    (M : FiniteModel4) (p : Fin M.worldCount → Bool) :
    (anyWorldsCosted M p).value = decide (∃ w, p w = true) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff]
  exact anyWorlds_eq_true_iff M p

theorem boxWorlds_eq_true_iff (M : FiniteModel4) (p : Fin M.worldCount → Bool) :
    boxWorlds M p = true ↔ ∀ w : Fin M.worldCount, p w = true := by
  exact allWorlds_eq_true_iff M p

theorem diaWorlds_eq_true_iff (M : FiniteModel4) (p : Fin M.worldCount → Bool) :
    diaWorlds M p = true ↔ ∃ w : Fin M.worldCount, p w = true := by
  exact anyWorlds_eq_true_iff M p

end Checker
end LeanUfo.UFO.DSL
