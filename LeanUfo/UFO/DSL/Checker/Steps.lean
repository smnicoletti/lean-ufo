import LeanUfo.UFO.DSL.Checker.Basic

/-!
# Step model for reflective checks

The step model is intentionally abstract. It counts checker-level evaluation
steps, not Lean kernel work, OS runtime, or Lake build time. The registered
checker-backed fields use conservative polynomial envelopes; individual axiom
checkers can refine these step counts while preserving the same interface.
-/

namespace LeanUfo.UFO.DSL
namespace Checker

structure Stepped (α : Type) where
  value : α
  steps : Nat
deriving Repr

def Stepped.map (f : α → β) (x : Stepped α) : Stepped β :=
  { value := f x.value, steps := x.steps }

def Stepped.and (x y : Stepped Bool) : Stepped Bool :=
  { value := x.value && y.value, steps := x.steps + y.steps + 1 }

def Stepped.polyEnvelope (M : FiniteModel4) : Nat :=
  (M.thingCount + 1) ^ 4 * (M.worldCount + 1) ^ 2

def Stepped.axiomEnvelope (M : FiniteModel4) (b : Bool) : Stepped Bool :=
  { value := b, steps := Stepped.polyEnvelope M }

def allThingsS (M : FiniteModel4) (p : Fin M.thingCount → Stepped Bool) : Stepped Bool :=
  { value := allThings M (fun x => (p x).value)
    steps := M.thingCount + (List.finRange M.thingCount).foldl (fun c x => c + (p x).steps) 0 }

def anyThingsS (M : FiniteModel4) (p : Fin M.thingCount → Stepped Bool) : Stepped Bool :=
  { value := anyThings M (fun x => (p x).value)
    steps := M.thingCount + (List.finRange M.thingCount).foldl (fun c x => c + (p x).steps) 0 }

def allWorldsS (M : FiniteModel4) (p : Fin M.worldCount → Stepped Bool) : Stepped Bool :=
  { value := allWorlds M (fun w => (p w).value)
    steps := M.worldCount + (List.finRange M.worldCount).foldl (fun c w => c + (p w).steps) 0 }

def anyWorldsS (M : FiniteModel4) (p : Fin M.worldCount → Stepped Bool) : Stepped Bool :=
  { value := anyWorlds M (fun w => (p w).value)
    steps := M.worldCount + (List.finRange M.worldCount).foldl (fun c w => c + (p w).steps) 0 }

end Checker
end LeanUfo.UFO.DSL
