import LeanUfo.UFO.Core.Section3_6
import LeanUfo.UFO.FormalAnalysis.Satisfiability.Relator.Model3_5

/-!
# Anti-vacuity analysis for section 3.6

The qua individual functions as a mode-kind instance and is a proper part of
the relator, which functions as a relator-kind instance. The three dependence
relations are interpreted by the clauses in axioms (a53)-(a55).
-/

namespace AntiVacuity.Section3_6

open Relator.Model3_1

def functionsAs : Thing -> Thing -> Prop
  | .quaA, .modeKind | .relator, .relatorKind => True
  | _, _ => False

def sig : UFOSignature3_6 where
  toUFOSignature3_5 := Relator.Model3_5.sig
  FunctionsAs := fun x t _ => functionsAs x t
  GenericFunctionalDependence := fun x' y' w =>
    ∀ x, (Relator.Model3_5.sig.Inst x x' w ∧ functionsAs x x') ->
      ∃ y, y ≠ x ∧ Relator.Model3_5.sig.Inst y y' w ∧ functionsAs y y'
  IndividualFunctionalDependence := fun x x' y y' w =>
    (∀ u, (Relator.Model3_5.sig.Inst u x' w ∧ functionsAs u x') ->
      ∃ v, v ≠ u ∧ Relator.Model3_5.sig.Inst v y' w ∧ functionsAs v y') ∧
    Relator.Model3_5.sig.Inst x x' w ∧ Relator.Model3_5.sig.Inst y y' w ∧
    (functionsAs x x' -> functionsAs y y')
  ComponentOf := fun x x' y y' w =>
    Relator.Model3_5.sig.ProperPart x y w ∧
    ((∀ u, (Relator.Model3_5.sig.Inst u x' w ∧ functionsAs u x') ->
      ∃ v, v ≠ u ∧ Relator.Model3_5.sig.Inst v y' w ∧ functionsAs v y') ∧
    Relator.Model3_5.sig.Inst x x' w ∧ Relator.Model3_5.sig.Inst y y' w ∧
    (functionsAs x x' -> functionsAs y y'))

attribute [simp] functionsAs sig

instance : UFOAxioms3_6 sig where
  toUFOAxioms3_5 := by
    change UFOAxioms3_5 Relator.Model3_5.sig
    infer_instance
  ax53 := by intro x y w; rfl
  ax54 := by intro x x' y y' w; rfl
  ax55 := by intro x x' y y' w; rfl

private theorem dependence_fact (w : World) :
    sig.GenericFunctionalDependence .modeKind .relatorKind w := by
  intro x hx
  cases x <;> simp_all [Relator.Model3_1.inst]
  exact ⟨.relator, by decide, by simp⟩

theorem predicates_nonempty :
    (∃ x t w, sig.FunctionsAs x t w) ∧
    (∃ x y w, sig.GenericFunctionalDependence x y w) ∧
    (∃ x x' y y' w, sig.IndividualFunctionalDependence x x' y y' w) ∧
    (∃ x x' y y' w, sig.ComponentOf x x' y y' w) := by
  refine ⟨⟨.quaA, .modeKind, .actual, by simp⟩,
    ⟨.modeKind, .relatorKind, .actual, dependence_fact .actual⟩,
    ⟨.quaA, .modeKind, .relator, .relatorKind, .actual, ?_⟩,
    ⟨.quaA, .modeKind, .relator, .relatorKind, .actual, ?_⟩⟩
  · exact ⟨dependence_fact .actual, by simp⟩
  · exact ⟨by simp [Relator.Model3_5.part], dependence_fact .actual, by simp⟩

end AntiVacuity.Section3_6
