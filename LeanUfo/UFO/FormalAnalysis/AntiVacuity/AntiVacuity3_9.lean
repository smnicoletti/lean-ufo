import LeanUfo.UFO.Core.Section3_9
import LeanUfo.UFO.FormalAnalysis.AntiVacuity.AntiVacuity3_8
import LeanUfo.UFO.FormalAnalysis.Satisfiability.Relator.Model3_9

/-!
# Anti-vacuity analysis for section 3.9

The inherence table has the relator and one qua individual inhering in
`bearerA`, and the other qua individual inhering in `bearerB`. These terminal
bearers also witness the derived `MomentOf` and `UltimateBearerOf` predicates.
-/

namespace AntiVacuity.Section3_9

open Relator.Model3_1

def sig : UFOSignature3_9 where
  toUFOSignature3_8 := AntiVacuity.Section3_8.sig
  InheresIn := fun x y _ => Relator.Model3_9.inheresIn x y

attribute [simp] sig

theorem ax65_sig : ax_a65 sig := by
  intro x y w h
  change Relator.Model3_9.inheresIn x y at h
  cases x <;> cases y <;> simp [Relator.Model3_9.inheresIn] at h
  all_goals
    intro w' _ hEx
    cases w' <;> simp_all [Relator.Model3_7.ex]

theorem ax66_sig : ax_a66 sig := by
  intro x y w h
  change Relator.Model3_9.inheresIn x y at h
  change Relator.Model3_3.moment x ∧
    (Relator.Model3_1.isType y ∨ ¬ Relator.Model3_1.isType y)
  cases x <;> cases y <;> simp_all [Relator.Model3_9.inheresIn,
    Relator.Model3_3.moment, Relator.Model3_1.isType]

theorem ax67_sig : ax_a67 sig := by
  intro x y z w h
  change Relator.Model3_9.inheresIn x y ∧ Relator.Model3_9.inheresIn x z at h
  cases x <;> cases y <;> cases z <;> simp_all [Relator.Model3_9.inheresIn]
  all_goals rfl

private theorem bearerA_not_moment (w : World) : ¬ sig.Moment .bearerA w := by
  change ¬ Relator.Model3_3.moment .bearerA
  simp [Relator.Model3_3.moment]

private theorem bearerB_not_moment (w : World) : ¬ sig.Moment .bearerB w := by
  change ¬ Relator.Model3_3.moment .bearerB
  simp [Relator.Model3_3.moment]

private theorem bearerA_terminal (w : World) :
    ∀ y, ¬ sig.InheresIn .bearerA y w := by
  intro y; cases y <;> simp [Relator.Model3_9.inheresIn]

private theorem bearerB_terminal (w : World) :
    ∀ y, ¬ sig.InheresIn .bearerB y w := by
  intro y; cases y <;> simp [Relator.Model3_9.inheresIn]

theorem ax68_sig : ax_a68 sig := by
  intro m w hMoment
  change Relator.Model3_3.moment m at hMoment
  cases m <;> simp [Relator.Model3_3.moment] at hMoment
  · refine ⟨.bearerA, ⟨bearerA_not_moment w,
      .direct (by simp [Relator.Model3_9.inheresIn])⟩, ?_⟩
    intro b hb
    exact momentOf_eq_of_unique_direct_bearer (Sig := sig)
      (b := .bearerA) (x := b)
      (by intro y h; cases y <;> simp_all [Relator.Model3_9.inheresIn] <;> rfl)
      (bearerA_terminal w) hb.2
  · refine ⟨.bearerA, ⟨bearerA_not_moment w,
      .direct (by simp [Relator.Model3_9.inheresIn])⟩, ?_⟩
    intro b hb
    exact momentOf_eq_of_unique_direct_bearer (Sig := sig)
      (b := .bearerA) (x := b)
      (by intro y h; cases y <;> simp_all [Relator.Model3_9.inheresIn] <;> rfl)
      (bearerA_terminal w) hb.2
  · refine ⟨.bearerB, ⟨bearerB_not_moment w,
      .direct (by simp [Relator.Model3_9.inheresIn])⟩, ?_⟩
    intro b hb
    exact momentOf_eq_of_unique_direct_bearer (Sig := sig)
      (b := .bearerB) (x := b)
      (by intro y h; cases y <;> simp_all [Relator.Model3_9.inheresIn] <;> rfl)
      (bearerB_terminal w) hb.2

instance : UFOAxioms3_9 sig where
  toUFOAxioms3_8 := by
    change UFOAxioms3_8 AntiVacuity.Section3_8.sig
    infer_instance
  ax65 := ax65_sig
  ax66 := ax66_sig
  ax67 := ax67_sig
  ax68 := ax68_sig

theorem predicates_nonempty :
    (∃ x y w, sig.InheresIn x y w) ∧
    (∃ x y w, MomentOf sig x y w) ∧
    (∃ b m w, UltimateBearerOf sig b m w) := by
  refine ⟨⟨.quaA, .bearerA, .actual, by simp [Relator.Model3_9.inheresIn]⟩,
    ⟨.quaA, .bearerA, .actual, .direct (by simp [Relator.Model3_9.inheresIn])⟩,
    ⟨.bearerA, .quaA, .actual,
      ⟨bearerA_not_moment .actual,
        .direct (by simp [Relator.Model3_9.inheresIn])⟩⟩⟩

end AntiVacuity.Section3_9
