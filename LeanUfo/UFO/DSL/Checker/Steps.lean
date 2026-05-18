import LeanUfo.UFO.DSL.Checker.Basic

/-!
# Step model for reflective checks

The step model is intentionally abstract. It records checker-level step
envelopes, not Lean kernel work, OS runtime, Lake build time, or separate
quantitative semantic metrics. The registered checker-backed fields use one
conservative global envelope; individual axiom checkers can refine that
envelope where their visible finite scans justify smaller exponents.
-/

namespace LeanUfo.UFO.DSL
namespace Checker

structure Stepped (α : Type) where
  value : α
  steps : Nat
deriving Repr

def Stepped.stepEnvelope (M : FiniteModel4) (thingPow worldPow : Nat) : Nat :=
  (M.thingCount + 1) ^ thingPow * (M.worldCount + 1) ^ worldPow

/--
Conservative global envelope for checker-backed axiom fields.

The exponent choice and final polynomial bound are documented in
`Checker.Complexity`.
-/
def Stepped.globalStepEnvelope (M : FiniteModel4) : Nat :=
  Stepped.stepEnvelope M 8 4

/--
Attach a syntactic step envelope to a Boolean axiom checker.

`thingPow` and `worldPow` count visible finite scans in the checker body under
the convention documented at the top of this file. These parameters are upper
bound exponents, not measured execution counters.
-/
def Stepped.axiomStepEnvelope
    (M : FiniteModel4) (thingPow worldPow : Nat) (b : Bool) : Stepped Bool :=
  { value := b, steps := Stepped.stepEnvelope M thingPow worldPow }

/--
Default wrapper for axioms that use the global step envelope.
-/
def Stepped.axiomEnvelope (M : FiniteModel4) (b : Bool) : Stepped Bool :=
  Stepped.axiomStepEnvelope M 8 4 b

end Checker
end LeanUfo.UFO.DSL
