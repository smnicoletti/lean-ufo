import LeanUfo.UFO.Core.Section3_9
import LeanUfo.UFO.FormalAnalysis.Satisfiability.Relator.Model3_8

/-!
# Positive relator model: section 3.9

The relator and `quaA` inhere in `bearerA`; `quaB` inheres in `bearerB`. The
bearers are terminal substantials, so every inherence chain has one edge and a
unique ultimate bearer.
-/

namespace Relator.Model3_9

open Model3_1

def inheresIn : Thing -> Thing -> Prop
  | .relator, .bearerA | .quaA, .bearerA | .quaB, .bearerB => True
  | _, _ => False

def sig : UFOSignature3_9 where
  toUFOSignature3_8 := Model3_8.sig
  InheresIn := fun x y _ => inheresIn x y

attribute [simp] inheresIn sig

/-- Each inherence edge entails the corresponding modal dependence. -/
theorem ax65_sig : ax_a65 sig := by
  intro x y w h
  change inheresIn x y at h
  cases x <;> cases y <;> simp [inheresIn] at h
  all_goals
    intro w' _hAccessible hEx
    cases w' <;> simp_all [Model3_7.ex]

/-- Inhering entities are moments and their targets are concrete individuals. -/
theorem ax66_sig : ax_a66 sig := by
  intro x y w h
  change inheresIn x y at h
  cases x <;> cases y <;> simp_all [inheresIn]

/-- The direct bearer of every moment is unique. -/
theorem ax67_sig : ax_a67 sig := by
  intro x y z w h
  change inheresIn x y ∧ inheresIn x z at h
  cases x <;> cases y <;> cases z <;> simp_all [inheresIn]

private theorem bearerA_terminal (w : World) :
    forall y, ¬ sig.InheresIn .bearerA y w := by
  intro y
  cases y <;> simp [sig, inheresIn]

private theorem bearerB_terminal (w : World) :
    forall y, ¬ sig.InheresIn .bearerB y w := by
  intro y
  cases y <;> simp [sig, inheresIn]

/-- Every moment has exactly the terminal bearer selected by the table. -/
theorem ax68_sig : ax_a68 sig := by
  intro m w hMoment
  change Model3_3.moment m at hMoment
  cases m <;> simp [Model3_3.moment] at hMoment
  · refine ⟨.bearerA, ⟨by simp, .direct (by simp [sig, inheresIn])⟩, ?_⟩
    intro b hb
    exact momentOf_eq_of_unique_direct_bearer (Sig := sig)
      (b := .bearerA) (x := b)
      (by intro y h; cases y <;> simp_all [sig, inheresIn])
      (bearerA_terminal w) hb.2
  · refine ⟨.bearerA, ⟨by simp, .direct (by simp [sig, inheresIn])⟩, ?_⟩
    intro b hb
    exact momentOf_eq_of_unique_direct_bearer (Sig := sig)
      (b := .bearerA) (x := b)
      (by intro y h; cases y <;> simp_all [sig, inheresIn])
      (bearerA_terminal w) hb.2
  · refine ⟨.bearerB, ⟨by simp, .direct (by simp [sig, inheresIn])⟩, ?_⟩
    intro b hb
    exact momentOf_eq_of_unique_direct_bearer (Sig := sig)
      (b := .bearerB) (x := b)
      (by intro y h; cases y <;> simp_all [sig, inheresIn])
      (bearerB_terminal w) hb.2

/-- Consistency witness for section 3.9 of the positive relator model chain. -/
instance : UFOAxioms3_9 sig where
  toUFOAxioms3_8 := by
    change UFOAxioms3_8 Model3_8.sig
    infer_instance
  ax65 := ax65_sig
  ax66 := ax66_sig
  ax67 := ax67_sig
  ax68 := ax68_sig

end Relator.Model3_9
