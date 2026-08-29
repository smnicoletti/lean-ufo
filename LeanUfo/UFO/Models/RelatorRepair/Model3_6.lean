import LeanUfo.UFO.Core.Section3_6
import LeanUfo.UFO.Models.RelatorRepair.Model3_5

/-!
# Analysis model for the relator repair: section 3.6

`FunctionsAs` is empty, which makes generic functional dependence vacuously
true. Individual functional dependence then reduces to the two instantiation
conditions in (a54), and componenthood follows (a55).
-/

namespace RelatorRepair.Model3_6

def sig : UFOSignature3_6 where
  toUFOSignature3_5 := Model3_5.sig
  FunctionsAs := fun _ _ _ => False
  GenericFunctionalDependence := fun x' y' w =>
    forall x,
      (Model3_5.sig.Inst x x' w ∧ False) ->
        exists y, y ≠ x ∧ Model3_5.sig.Inst y y' w ∧ False
  IndividualFunctionalDependence := fun x x' y y' w =>
    Model3_5.sig.Inst x x' w ∧
      Model3_5.sig.Inst y y' w ∧
      (False -> False)
  ComponentOf := fun x x' y y' w =>
    Model3_5.sig.ProperPart x y w ∧
      (Model3_5.sig.Inst x x' w ∧
       Model3_5.sig.Inst y y' w ∧
       (False -> False))

attribute [simp] sig

/-- Generic functional dependence satisfies its defining biconditional. -/
theorem ax53_sig : ax_a53 sig := by
  intro x' y' w
  simp [sig]

/-- Individual functional dependence satisfies its defining biconditional. -/
theorem ax54_sig : ax_a54 sig := by
  intro x x' y y' w
  simp [sig]

/-- Componenthood satisfies its proper-part and dependence definition. -/
theorem ax55_sig : ax_a55 sig := by
  intro x x' y y' w
  rfl

/-- Consistency witness for section 3.6 of the analysis model chain. -/
instance : UFOAxioms3_6 sig where
  toUFOAxioms3_5 := by
    change UFOAxioms3_5 Model3_5.sig
    infer_instance
  ax53 := ax53_sig
  ax54 := ax54_sig
  ax55 := ax55_sig

end RelatorRepair.Model3_6
