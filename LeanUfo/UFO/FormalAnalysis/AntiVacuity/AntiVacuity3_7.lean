import LeanUfo.UFO.Core.Section3_7
import LeanUfo.UFO.FormalAnalysis.AntiVacuity.AntiVacuity3_6
import LeanUfo.UFO.FormalAnalysis.Satisfiability.Relator.Model3_7

/-!
# Anti-vacuity analysis for section 3.7

The relator is constituted by `bearerA`. Both are endurants, but they
instantiate the distinct relator and object kinds. Constitution is asymmetric.
The world-dependent existence table is retained for the dependence analysis in
the next section.
-/

namespace AntiVacuity.Section3_7

open Relator.Model3_1

def constitutedBy : Thing -> Thing -> Prop
  | .relator, .bearerA => True
  | _, _ => False

def sig : UFOSignature3_7 where
  toUFOSignature3_6 := AntiVacuity.Section3_6.sig
  Ex := fun x w => Relator.Model3_7.ex x w
  ConstitutedBy := fun x y _ => constitutedBy x y
  GenericConstitutionalDependence := fun x' y' w =>
    ∀ x, AntiVacuity.Section3_6.sig.Inst x x' w ->
      ∃ y, AntiVacuity.Section3_6.sig.Inst y y' w ∧ constitutedBy x y
  Constitution := fun x x' y y' w =>
    AntiVacuity.Section3_6.sig.Inst x x' w ∧
    AntiVacuity.Section3_6.sig.Inst y y' w ∧
    (∀ u, AntiVacuity.Section3_6.sig.Inst u x' w ->
      ∃ v, AntiVacuity.Section3_6.sig.Inst v y' w ∧ constitutedBy u v) ∧
    constitutedBy x y

attribute [simp] constitutedBy sig

private theorem constituted_pair {x y : Thing} (h : constitutedBy x y) :
    x = .relator ∧ y = .bearerA := by
  cases x <;> cases y <;> simp_all [constitutedBy]

theorem ax56_sig : ax_a56 sig := by
  intro x y w h
  have hxy := constituted_pair h
  rcases hxy with ⟨rfl, rfl⟩
  simp

theorem ax57_sig : ax_a57 sig := by
  intro x y x' y' w h
  have hxy := constituted_pair h.1
  rcases hxy with ⟨rfl, rfl⟩
  cases x' <;> cases y' <;> simp_all [Relator.Model3_1.inst]

theorem ax58_sig : ax_a58 sig := by intro x y w; rfl
theorem ax59_sig : ax_a59 sig := by intro x x' y y' w; rfl

theorem ax60_sig : ax_a60 sig := by
  intro x y w h
  have hxy := constituted_pair h.2
  rcases hxy with ⟨rfl, rfl⟩
  simp at h

theorem ax61_sig : ax_a61 sig := by
  intro x y w h
  have hxy := constituted_pair h
  rcases hxy with ⟨rfl, rfl⟩
  simp [constitutedBy]

instance : UFOAxioms3_7 sig where
  toUFOAxioms3_6 := by
    change UFOAxioms3_6 AntiVacuity.Section3_6.sig
    infer_instance
  ax56 := ax56_sig
  ax57 := ax57_sig
  ax58 := ax58_sig
  ax59 := ax59_sig
  ax60 := ax60_sig
  ax61 := ax61_sig

private theorem constitutional_dependence_fact (w : World) :
    sig.GenericConstitutionalDependence .relatorKind .objectKind w := by
  intro x hx
  cases x <;> simp_all [Relator.Model3_1.inst]
  exact ⟨.bearerA, by simp⟩

theorem predicates_nonempty :
    (∃ x w, sig.Ex x w) ∧
    (∃ x y w, sig.ConstitutedBy x y w) ∧
    (∃ x y w, sig.GenericConstitutionalDependence x y w) ∧
    (∃ x x' y y' w, sig.Constitution x x' y y' w) := by
  refine ⟨⟨.relator, .actual, by simp [Relator.Model3_7.ex]⟩,
    ⟨.relator, .bearerA, .actual, by simp⟩,
    ⟨.relatorKind, .objectKind, .actual, constitutional_dependence_fact .actual⟩,
    ⟨.relator, .relatorKind, .bearerA, .objectKind, .actual, ?_⟩⟩
  exact ⟨by simp, by simp, constitutional_dependence_fact .actual, by simp⟩

end AntiVacuity.Section3_7
