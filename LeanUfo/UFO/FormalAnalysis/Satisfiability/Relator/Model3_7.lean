import LeanUfo.UFO.Core.Section3_7
import LeanUfo.UFO.FormalAnalysis.Satisfiability.Relator.Model3_6

/-!
# Positive relator model: section 3.7

Constitution is empty. Existence is nonconstant: the actual world contains
every individual, while each bearer and the external object also occurs in a
separate world. These worlds witness the independence claims used in §§3.8
and 3.10.
-/

namespace Relator.Model3_7

open Model3_1

def ex : Thing -> World -> Prop
  | .relator, .actual | .quaA, .actual | .quaB, .actual => True
  | .bearerA, .actual | .bearerA, .bearerA => True
  | .bearerB, .actual | .bearerB, .bearerB => True
  | .external, .actual | .external, .external => True
  | .foundation, .actual => True
  | .relatorKind, _ | .modeKind, _ | .objectKind, _ | .perdurantKind, _ => True
  | _, _ => False

def sig : UFOSignature3_7 where
  toUFOSignature3_6 := Model3_6.sig
  Ex := fun x w => ex x w
  ConstitutedBy := fun _ _ _ => False
  GenericConstitutionalDependence := fun x' y' w =>
    forall x, Model3_6.sig.Inst x x' w ->
      exists y, Model3_6.sig.Inst y y' w ∧ False
  Constitution := fun x x' y y' w =>
    Model3_6.sig.Inst x x' w ∧
      Model3_6.sig.Inst y y' w ∧
      (forall u, Model3_6.sig.Inst u x' w ->
        exists v, Model3_6.sig.Inst v y' w ∧ False) ∧
      False

attribute [simp] ex sig

/-- Empty constitution satisfies the category restriction. -/
theorem ax56_sig : ax_a56 sig := by
  intro x y w h
  simp [sig] at h

/-- Empty constitution satisfies the distinct-kind restriction. -/
theorem ax57_sig : ax_a57 sig := by
  intro x y x' y' w h
  simp [sig] at h

/-- Generic constitutional dependence is interpreted by the axiom's RHS. -/
theorem ax58_sig : ax_a58 sig := by intro x' y' w; rfl

/-- Constitution is interpreted by the axiom's RHS. -/
theorem ax59_sig : ax_a59 sig := by intro x x' y y' w; rfl

/-- The perdurant persistence condition is vacuous for empty constitution. -/
theorem ax60_sig : ax_a60 sig := by
  intro x y w h
  simp [sig] at h

/-- Empty constitution is asymmetric. -/
theorem ax61_sig : ax_a61 sig := by
  intro x y w h
  simp [sig] at h

/-- Consistency witness for section 3.7 of the positive relator model chain. -/
instance : UFOAxioms3_7 sig where
  toUFOAxioms3_6 := by
    change UFOAxioms3_6 Model3_6.sig
    infer_instance
  ax56 := ax56_sig
  ax57 := ax57_sig
  ax58 := ax58_sig
  ax59 := ax59_sig
  ax60 := ax60_sig
  ax61 := ax61_sig

end Relator.Model3_7
