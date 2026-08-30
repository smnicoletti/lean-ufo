import LeanUfo.UFO.Core.Section3_2
import LeanUfo.UFO.FormalAnalysis.Satisfiability.Relator.Model3_1

/-!
# Positive relator model: section 3.2

The three endurant types are rigid sortal kinds. The perdurant type is not
classified by the §3.2 rigidity or sortality predicates in this model.
Anti-rigid, semi-rigid, and non-sortal classifications are empty.
-/

namespace Relator.Model3_2

def sig : UFOSignature3_2 where
  toUFOSignature3_1 := Model3_1.sig
  Rigid := fun x _ => x = .relatorKind ∨ x = .modeKind ∨ x = .objectKind
  AntiRigid := fun _ _ => False
  SemiRigid := fun _ _ => False
  Kind := fun x _ => x = .relatorKind ∨ x = .modeKind ∨ x = .objectKind
  Sortal := fun x _ => x = .relatorKind ∨ x = .modeKind ∨ x = .objectKind
  NonSortal := fun _ _ => False
  SubKind := fun _ _ => False
  Phase := fun _ _ => False
  Role := fun _ _ => False
  SemiRigidSortal := fun _ _ => False
  Category := fun _ _ => False
  Mixin := fun _ _ => False
  PhaseMixin := fun _ _ => False
  RoleMixin := fun _ _ => False

attribute [simp] sig

/-- The three endurant types are rigid because instantiation is world-invariant. -/
theorem ax18_sig : ax_a18 sig := by
  intro t w
  cases t <;> simp [Frame.Box, Frame.Dia, Model3_1.frame]
  all_goals
    intro x u hInst v
    simpa [sig, Model3_1.sig, Model3_1.inst] using hInst

/-- No type in the witness is anti-rigid or semi-rigid. -/
theorem ax19_sig : ax_a19 sig := by
  intro t w
  cases t <;> simp [Frame.Dia, Model3_1.frame]
  all_goals
    first
    | exact ⟨.relator, trivial, .actual, fun _ => trivial⟩
    | exact ⟨.quaA, trivial, .actual, fun _ => trivial⟩
    | exact ⟨.bearerA, trivial, .actual, fun _ => trivial⟩

theorem ax20_sig : ax_a20 sig := by
  intro t w
  cases t <;> cases w <;> simp

/-- Every endurant necessarily instantiates its category-specific kind. -/
theorem ax21_sig : ax_a21 sig := by
  intro x w hx
  cases x <;> simp_all [Frame.Box, Model3_1.frame]
  all_goals
    first
    | exact ⟨.relatorKind, by simp⟩
    | exact ⟨.modeKind, by simp⟩
    | exact ⟨.objectKind, by simp⟩

theorem ax22_sig : ax_a22 sig := by
  intro k x w h hdia
  rcases hdia with ⟨v, _hv, z, hzKind, hzInst, hzNe⟩
  have hkInst : Model3_1.inst x k := by simpa [sig, Model3_1.sig] using h.2
  have hzInst' : Model3_1.inst x z := by simpa [sig, Model3_1.sig] using hzInst
  exact hzNe (Model3_1.inst_target_unique
    (x := x) (t₁ := k) (t₂ := z) hkInst hzInst').symm

/-- The three endurant kinds are exactly the sortals in this model. -/
theorem ax23_sig : ax_a23 sig := by
  intro t w
  cases t <;> cases w <;> simp [Frame.Box, Model3_1.frame]
  all_goals
    first
    | exact ⟨.relatorKind, by simp⟩
    | exact ⟨.modeKind, by simp⟩
    | exact ⟨.objectKind, by simp⟩

theorem ax24_sig : ax_a24 sig := by intro t w; cases t <;> cases w <;> simp
theorem ax25_sig : ax_a25 sig := by intro w; simp
theorem ax26_sig : ax_a26 sig := by intro t w; cases t <;> cases w <;> simp
theorem ax27_sig : ax_a27 sig := by intro w; simp
theorem ax28_sig : ax_a28 sig := by intro t w; simp
theorem ax29_sig : ax_a29 sig := by intro t w; simp
theorem ax30_sig : ax_a30 sig := by intro t w; simp
theorem ax31_sig : ax_a31 sig := by intro t w; simp
theorem ax32_sig : ax_a32 sig := by intro w; simp
theorem ax33_sig : ax_a33 sig := by intro t w; simp

/-- Instantiation of the endurant kind is restricted to endurants. -/
theorem ax_instEndurant_sig : ax_instEndurant_of_EndurantType (Sig := sig) := by
  intro t x w hType hInst
  cases t <;> cases x <;> cases w <;> simp_all

theorem ax_sub_kind_sortal_sig : ax_sub_of_kind_is_sortal (Sig := sig) := by
  intro a k w hSub hKind
  rcases hSub with ⟨hType, _hKindType, hBox⟩
  rcases Model3_1.type_has_instance hType with ⟨x, hxa⟩
  have hxk := hBox .actual (by trivial) x hxa
  have hak : a = k := Model3_1.inst_target_unique hxa hxk
  subst k
  simpa [sig] using hKind

theorem ax_nonSortal_up_sig : ax_nonSortal_upward (Sig := sig) := by
  intro x y w
  simp

theorem ax_kindStable_sig : ax_kindStable sig := by
  intro x w v
  simp

/-- Consistency witness for §3.2 of the positive relator model chain. -/
instance : UFOAxioms3_2 sig where
  toUFOAxioms3_1 := by
    change UFOAxioms3_1 Model3_1.sig
    infer_instance
  ax18 := ax18_sig
  ax19 := ax19_sig
  ax20 := ax20_sig
  ax21 := ax21_sig
  ax22 := ax22_sig
  ax23 := ax23_sig
  ax24 := ax24_sig
  ax25 := ax25_sig
  ax26 := ax26_sig
  ax27 := ax27_sig
  ax28 := ax28_sig
  ax29 := ax29_sig
  ax30 := ax30_sig
  ax31 := ax31_sig
  ax32 := ax32_sig
  ax33 := ax33_sig
  ax_instEndurant := ax_instEndurant_sig
  ax_sub_kind_sortal := ax_sub_kind_sortal_sig
  ax_nonSortal_up := ax_nonSortal_up_sig
  ax_kindStable := ax_kindStable_sig

end Relator.Model3_2
