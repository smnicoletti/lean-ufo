import LeanUfo.UFO.DSL.FiniteModel

/-!
# Reflective checker basics

This module introduces the small Boolean vocabulary used by the reflective
checker. The combinators expose the finite worlds and things of a
`FiniteModel4` as executable Boolean quantifiers, so axiom checkers can be
written as ordinary finite scans over the compiled model.
-/

namespace LeanUfo.UFO.DSL
namespace Checker

def allThings (M : FiniteModel4) (p : Fin M.thingCount → Bool) : Bool :=
  decide (∀ x : Fin M.thingCount, p x = true)

def anyThings (M : FiniteModel4) (p : Fin M.thingCount → Bool) : Bool :=
  decide (∃ x : Fin M.thingCount, p x = true)

def allWorlds (M : FiniteModel4) (p : Fin M.worldCount → Bool) : Bool :=
  decide (∀ w : Fin M.worldCount, p w = true)

def anyWorlds (M : FiniteModel4) (p : Fin M.worldCount → Bool) : Bool :=
  decide (∃ w : Fin M.worldCount, p w = true)

def boxWorlds (M : FiniteModel4) : (Fin M.worldCount → Bool) → Bool :=
  allWorlds M

def diaWorlds (M : FiniteModel4) : (Fin M.worldCount → Bool) → Bool :=
  anyWorlds M

theorem allThings_eq_true_iff (M : FiniteModel4) (p : Fin M.thingCount → Bool) :
    allThings M p = true ↔ ∀ x : Fin M.thingCount, p x = true := by
  unfold allThings
  exact decide_eq_true_iff

theorem anyThings_eq_true_iff (M : FiniteModel4) (p : Fin M.thingCount → Bool) :
    anyThings M p = true ↔ ∃ x : Fin M.thingCount, p x = true := by
  unfold anyThings
  exact decide_eq_true_iff

theorem allWorlds_eq_true_iff (M : FiniteModel4) (p : Fin M.worldCount → Bool) :
    allWorlds M p = true ↔ ∀ w : Fin M.worldCount, p w = true := by
  unfold allWorlds
  exact decide_eq_true_iff

theorem anyWorlds_eq_true_iff (M : FiniteModel4) (p : Fin M.worldCount → Bool) :
    anyWorlds M p = true ↔ ∃ w : Fin M.worldCount, p w = true := by
  unfold anyWorlds
  exact decide_eq_true_iff

theorem boxWorlds_eq_true_iff (M : FiniteModel4) (p : Fin M.worldCount → Bool) :
    boxWorlds M p = true ↔ ∀ w : Fin M.worldCount, p w = true := by
  exact allWorlds_eq_true_iff M p

theorem diaWorlds_eq_true_iff (M : FiniteModel4) (p : Fin M.worldCount → Bool) :
    diaWorlds M p = true ↔ ∃ w : Fin M.worldCount, p w = true := by
  exact anyWorlds_eq_true_iff M p

end Checker
end LeanUfo.UFO.DSL
