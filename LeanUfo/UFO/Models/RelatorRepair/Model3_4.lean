import LeanUfo.UFO.Core.Section3_4
import LeanUfo.UFO.Models.RelatorRepair.Model3_3

/-!
# Analysis model for the relator repair: section 3.4

The three endurant kinds occupy the object, relator, and mode branches required
by (a46). Each type predicate uses the corresponding instance condition from
(a44).
-/

namespace RelatorRepair.Model3_4

open Model3_1

def typedBy (P : Thing -> World -> Prop) (t : Thing) (w : World) : Prop :=
  Model3_3.sig.Type_ t w ∧
    Frame.Box (F := Model3_1.frame)
      (fun w' => ∀ x, Model3_3.sig.Inst x t w' -> P x w') w

def sig : UFOSignature3_4 where
  toUFOSignature3_3 := Model3_3.sig
  SubstantialType := typedBy Model3_3.sig.Substantial
  MomentType := typedBy Model3_3.sig.Moment
  ObjectType := typedBy Model3_3.sig.Object
  CollectiveType := typedBy Model3_3.sig.Collective
  QuantityType := typedBy Model3_3.sig.Quantity
  RelatorType := typedBy Model3_3.sig.Relator
  ModeType := typedBy Model3_3.sig.Mode
  QualityType := typedBy (Quality Model3_3.sig)
  ObjectKind := fun t w => typedBy Model3_3.sig.Object t w ∧ Model3_3.sig.Kind t w
  CollectiveKind := fun t w => typedBy Model3_3.sig.Collective t w ∧ Model3_3.sig.Kind t w
  QuantityKind := fun t w => typedBy Model3_3.sig.Quantity t w ∧ Model3_3.sig.Kind t w
  RelatorKind := fun t w => typedBy Model3_3.sig.Relator t w ∧ Model3_3.sig.Kind t w
  ModeKind := fun t w => typedBy Model3_3.sig.Mode t w ∧ Model3_3.sig.Kind t w

attribute [simp] typedBy sig

/-- The inherited broad type categories agree with their `a44` schemas. -/
theorem ax44_endurant_sig : ax_a44_endurantType sig := by
  intro t w
  cases t <;> simp [Frame.Box, Model3_1.frame]
  all_goals
    first
    | exact ⟨World.actual, Thing.foundation, trivial, by simp⟩
    | (intro v x h; cases x <;> simp_all)

theorem ax44_perdurant_sig : ax_a44_perdurantType sig := by
  intro t w
  cases t <;> simp [Frame.Box, Model3_1.frame]
  all_goals
    first
    | exact ⟨World.actual, Thing.relator, trivial, by simp⟩
    | exact ⟨World.actual, Thing.quaA, trivial, by simp⟩
    | exact ⟨World.actual, Thing.bearerA, trivial, by simp⟩
    | (intro v x h; cases x <;> simp_all)

theorem ax44_substantial_sig : ax_a44_substantialType sig := by intro t w; rfl
theorem ax44_moment_sig : ax_a44_momentType sig := by intro t w; rfl
theorem ax44_object_sig : ax_a44_objectType sig := by intro t w; rfl
theorem ax44_collective_sig : ax_a44_collectiveType sig := by intro t w; rfl
theorem ax44_quantity_sig : ax_a44_quantityType sig := by intro t w; rfl
theorem ax44_relator_sig : ax_a44_relatorType sig := by intro t w; rfl
theorem ax44_mode_sig : ax_a44_modeType sig := by intro t w; rfl
theorem ax44_quality_sig : ax_a44_qualityType sig := by intro t w; rfl

/-- The specific type clauses and kind refinements hold by construction. -/
theorem ax44_sig : ax_a44 sig := by
  exact ⟨ax44_endurant_sig, ax44_perdurant_sig, ax44_substantial_sig,
    ax44_moment_sig, ax44_object_sig, ax44_collective_sig,
    ax44_quantity_sig, ax44_relator_sig, ax44_mode_sig, ax44_quality_sig⟩

theorem ax45_sig : ax_a45 sig := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t w; rfl
  · intro t w; rfl
  · intro t w; rfl
  · intro t w; rfl
  · intro t w; rfl
  · intro t w
    cases t <;> simp [typedBy, Frame.Box, Model3_1.frame, Quality]
    all_goals
      first
      | exact ⟨World.actual, Thing.relator, trivial⟩
      | exact ⟨World.actual, Thing.quaA, trivial⟩
      | exact ⟨World.actual, Thing.bearerA, trivial⟩

private theorem relatorKind_holds (w : World) : sig.RelatorKind .relatorKind w := by
  refine ⟨⟨by simp, ?_⟩, by simp⟩
  intro v _hv x hx
  cases x <;> simp_all

private theorem modeKind_holds (w : World) : sig.ModeKind .modeKind w := by
  refine ⟨⟨by simp, ?_⟩, by simp⟩
  intro v _hv x hx
  cases x <;> simp_all

private theorem objectKind_holds (w : World) : sig.ObjectKind .objectKind w := by
  refine ⟨⟨by simp, ?_⟩, by simp⟩
  intro v _hv x hx
  cases x <;> simp_all

/-- Each endurant possibly instantiates its category-specific kind. -/
theorem ax46_sig : ax_a46 sig := by
  intro x w hx
  cases x <;> simp_all
  · refine ⟨w, by trivial, .relatorKind, ?_, by simp⟩
    right; right; left
    exact relatorKind_holds w
  · refine ⟨w, by trivial, .modeKind, ?_, by simp⟩
    right; right; right
    exact modeKind_holds w
  · refine ⟨w, by trivial, .modeKind, ?_, by simp⟩
    right; right; right
    exact modeKind_holds w
  · refine ⟨w, by trivial, .objectKind, ?_, by simp⟩
    left
    exact objectKind_holds w
  · refine ⟨w, by trivial, .objectKind, ?_, by simp⟩
    left
    exact objectKind_holds w
  · refine ⟨w, by trivial, .objectKind, ?_, by simp⟩
    left
    exact objectKind_holds w

/-- Consistency witness for §3.4 of the analysis model chain. -/
instance : UFOAxioms3_4 sig where
  toUFOAxioms3_3 := by
    change UFOAxioms3_3 Model3_3.sig
    infer_instance
  ax44 := ax44_sig
  ax45 := ax45_sig
  ax46 := ax46_sig

end RelatorRepair.Model3_4
