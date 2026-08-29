import LeanUfo.UFO.Core.Section3_3
import LeanUfo.UFO.Models.RelatorRepair.Model3_2

/-!
# Analysis model for the relator repair: section 3.3

The individual taxonomy contains three substantials (`bearerA`, `bearerB`,
and `external`) and three moments (`relator`, `quaA`, and `quaB`). The qua
individuals are intrinsic modes, while the relator occupies the disjoint
relator branch.
-/

namespace RelatorRepair.Model3_3

open Model3_1

def substantial : Thing -> Prop
  | .bearerA | .bearerB | .external => True
  | _ => False

def moment : Thing -> Prop
  | .relator | .quaA | .quaB => True
  | _ => False

def relator : Thing -> Prop
  | .relator => True
  | _ => False

def mode : Thing -> Prop
  | .quaA | .quaB => True
  | _ => False

def sig : UFOSignature3_3 where
  toUFOSignature3_2 := Model3_2.sig
  Substantial := fun x _ => substantial x
  Moment := fun x _ => moment x
  Object := fun x _ => substantial x
  Collective := fun _ _ => False
  Quantity := fun _ _ => False
  Relator := fun x _ => relator x
  IntrinsicMoment := fun x _ => mode x
  Mode := fun x _ => mode x
  QualityKind := fun _ _ => False

attribute [simp] substantial moment relator mode sig

/-- The chosen substantial/moment classifications partition the endurants. -/
theorem ax34_sig : ax_a34 sig := by intro x w; cases x <;> cases w <;> simp
theorem ax35_sig : ax_a35 sig := by
  intro w h
  rcases h with ⟨x, hx⟩
  cases x <;> simp_all

/-- Every substantial in this witness is an object. -/
theorem ax36_sig : ax_a36 sig := by intro x w; cases x <;> cases w <;> simp
theorem ax37_sig : ax_a37 sig := by intro w; simp
theorem ax38_sig : ax_a38 sig := by intro w; simp
theorem ax39_sig : ax_a39 sig := by intro w; simp

/-- The relator and intrinsic-mode branches partition the moments. -/
theorem ax40_sig : ax_a40 sig := by intro x w; cases x <;> cases w <;> simp
theorem ax41_sig : ax_a41 sig := by
  intro w h
  rcases h with ⟨x, hx⟩
  cases x <;> simp_all
theorem ax42_sig : ax_a42 sig := by
  intro x w
  cases x <;> cases w <;> simp [Quality]
theorem ax43_sig : ax_a43 sig := by intro w; simp [Quality]

/-- Consistency witness for §3.3 of the analysis model chain. -/
instance : UFOAxioms3_3 sig where
  toUFOAxioms3_2 := by
    change UFOAxioms3_2 Model3_2.sig
    infer_instance
  ax34 := ax34_sig
  ax35 := ax35_sig
  ax36 := ax36_sig
  ax37 := ax37_sig
  ax38 := ax38_sig
  ax39 := ax39_sig
  ax40 := ax40_sig
  ax41 := ax41_sig
  ax42 := ax42_sig
  ax43 := ax43_sig

end RelatorRepair.Model3_3
