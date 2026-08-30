import LeanUfo.UFO.Core.Section3_8
import LeanUfo.UFO.FormalAnalysis.Satisfiability.Relator.Model3_7

/-!
# Positive relator model: section 3.8

Existential dependence and independence follow (a63) and (a64) directly. The
existence worlds from `Model3_7` determine both relations.
-/

namespace Relator.Model3_8

def sig : UFOSignature3_8 where
  toUFOSignature3_7 := Model3_7.sig
  ExistentialDependence := fun x y w =>
    Frame.Box (F := Model3_7.sig.F)
      (fun w' => Model3_7.sig.Ex x w' -> Model3_7.sig.Ex y w') w
  ExistentialIndependence := fun x y w =>
    (¬ Frame.Box (F := Model3_7.sig.F)
      (fun w' => Model3_7.sig.Ex x w' -> Model3_7.sig.Ex y w') w) ∧
    (¬ Frame.Box (F := Model3_7.sig.F)
      (fun w' => Model3_7.sig.Ex y w' -> Model3_7.sig.Ex x w') w)

attribute [simp] sig

/-- Existence is predicated only of members of the model's entity type. -/
theorem ax62_sig : ax_a62 sig := by intro x w h; trivial

/-- Existential dependence is the modal existence implication. -/
theorem ax63_sig : ax_a63 sig := by intro x y w; rfl

/-- Independence is mutual failure of existential dependence. -/
theorem ax64_sig : ax_a64 sig := by intro x y w; rfl

/-- Consistency witness for section 3.8 of the positive relator model chain. -/
instance : UFOAxioms3_8 sig where
  toUFOAxioms3_7 := by
    change UFOAxioms3_7 Model3_7.sig
    infer_instance
  ax62 := ax62_sig
  ax63 := ax63_sig
  ax64 := ax64_sig

end Relator.Model3_8
