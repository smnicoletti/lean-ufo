import LeanUfo.UFO.Core.Section3_1

/-!
# Analysis model for the relator repair: section 3.1

This module fixes the domain used throughout the model chain. It contains a
relator, two qua individuals, three substantials, one perdurant foundation,
and four types. Later modules extend the signature without changing this
domain.
-/

namespace RelatorRepair.Model3_1

inductive World
  | actual | bearerA | bearerB | external
  deriving DecidableEq, Repr

inductive Thing
  | relator | quaA | quaB | bearerA | bearerB | external | foundation
  | relatorKind | modeKind | objectKind | perdurantKind
  deriving DecidableEq, Repr

def frame : S5Frame where
  World := World
  R := fun _ _ => True
  refl := by simp
  symm := by simp
  trans := by simp

def isType : Thing -> Prop
  | .relatorKind | .modeKind | .objectKind | .perdurantKind => True
  | _ => False

def inst : Thing -> Thing -> Prop
  | .relator, .relatorKind => True
  | .quaA, .modeKind | .quaB, .modeKind => True
  | .bearerA, .objectKind | .bearerB, .objectKind | .external, .objectKind => True
  | .foundation, .perdurantKind => True
  | _, _ => False

def endurant : Thing -> Prop
  | .relator | .quaA | .quaB | .bearerA | .bearerB | .external => True
  | _ => False

def perdurant : Thing -> Prop
  | .foundation => True
  | _ => False

def endurantType : Thing -> Prop
  | .relatorKind | .modeKind | .objectKind => True
  | _ => False

def perdurantType : Thing -> Prop
  | .perdurantKind => True
  | _ => False

def sig : UFOSignature3_1 where
  F := frame
  Thing := Thing
  thing_nonempty := ⟨.relator⟩
  Type_ := fun x _ => isType x
  Individual := fun x _ => ¬ isType x
  Inst := fun x t _ => inst x t
  Sub := fun x y w =>
    isType x ∧ isType y ∧
      Frame.Box (F := frame) (fun _ => ∀ z, inst z x → inst z y) w
  ConcreteIndividual := fun x _ => ¬ isType x
  AbstractIndividual := fun _ _ => False
  Endurant := fun x _ => endurant x
  Perdurant := fun x _ => perdurant x
  EndurantType := fun x _ => endurantType x
  PerdurantType := fun x _ => perdurantType x

attribute [simp] frame isType inst endurant perdurant endurantType perdurantType sig

theorem ax1_sig : ax_a1 sig := by
  intro x w
  cases x <;> cases w <;> simp [Frame.Dia, frame]
  all_goals
    first
    | exact ⟨World.actual, Thing.relator, trivial⟩
    | exact ⟨World.actual, Thing.quaA, trivial⟩
    | exact ⟨World.actual, Thing.bearerA, trivial⟩
    | exact ⟨World.actual, Thing.foundation, trivial⟩

theorem ax2_sig : ax_a2 sig := by
  intro x w
  cases x <;> cases w <;> simp [Frame.Box, frame]
  all_goals
    first
    | exact ⟨World.actual, Thing.relator, trivial⟩
    | exact ⟨World.actual, Thing.quaA, trivial⟩
    | exact ⟨World.actual, Thing.bearerA, trivial⟩
    | exact ⟨World.actual, Thing.foundation, trivial⟩

theorem ax3_sig : ax_a3 sig := by
  intro x y w h
  cases x <;> cases y <;> cases w <;> simp_all

theorem ax4_sig : ax_a4 sig := by
  intro w h
  rcases h with ⟨x, y, z, hType, hxy, hyz⟩
  cases x <;> cases y <;> simp_all

theorem ax5_sig : ax_a5 sig := by
  intro x y w
  rfl

/-- Every entity in the witness has at most one instantiation target. -/
theorem inst_target_unique {x t₁ t₂ : Thing} :
    inst x t₁ -> inst x t₂ -> t₁ = t₂ := by
  intro h₁ h₂
  cases x <;> cases t₁ <;> cases t₂ <;> simp_all

/-- Every target of the model's instantiation relation is a type. -/
theorem inst_target_isType {x t : Thing} : inst x t -> isType t := by
  intro h
  cases x <;> cases t <;> simp_all

/-- Every type in the analysis model has a fixed actual instance. -/
theorem type_has_instance {t : Thing} : isType t -> ∃ x, inst x t := by
  intro ht
  cases t <;> simp_all
  · exact ⟨.relator, trivial⟩
  · exact ⟨.quaA, trivial⟩
  · exact ⟨.bearerA, trivial⟩
  · exact ⟨.foundation, trivial⟩

theorem ax6_sig : ax_a6 sig := by
  intro t₁ t₂ x w h
  have ht : t₁ = t₂ := inst_target_unique h.1 h.2.1
  subst t₂
  have hSelf : sig.Sub t₁ t₁ w := (ax5_sig t₁ t₁ w).2
    ⟨inst_target_isType h.1, inst_target_isType h.1,
      fun _ _ _ hInst => hInst⟩
  exact False.elim (h.2.2.1 hSelf)

theorem ax7_sig : ax_a7 sig := by
  intro x w h
  cases x <;> cases w <;> simp_all

theorem ax8_sig : ax_a8 sig := by
  intro x w h
  cases x <;> cases w <;> simp_all

theorem ax9_sig : ax_a9 sig := by
  intro x w h
  cases x <;> cases w <;> simp_all

theorem ax10_sig : ax_a10 sig := by
  intro x w
  cases x <;> cases w <;> simp

theorem ax11_sig : ax_a11 sig := by
  intro x w h
  cases x <;> cases w <;> simp_all

theorem ax12_sig : ax_a12 sig := by
  intro x w h
  cases x <;> cases w <;> simp_all

theorem ax13_sig : ax_a13 sig := by
  intro x w h
  cases x <;> cases w <;> simp_all

theorem ax14_sig : ax_a14 sig := by
  intro x w
  cases x <;> cases w <;> simp

theorem ax15_sig : ax_a15 sig := by
  intro x w h
  cases x <;> cases w <;> simp_all

theorem ax16_sig : ax_a16 sig := by
  intro x w h
  cases x <;> cases w <;> simp_all

theorem ax17_sig : ax_a17 sig := by
  intro x w h
  cases x <;> cases w <;> simp_all

instance : UFOAxioms3_1 sig where
  ax1 := ax1_sig
  ax2 := ax2_sig
  ax3 := ax3_sig
  ax4 := ax4_sig
  ax5 := ax5_sig
  ax6 := ax6_sig
  ax7 := ax7_sig
  ax8 := ax8_sig
  ax9 := ax9_sig
  ax10 := ax10_sig
  ax11 := ax11_sig
  ax12 := ax12_sig
  ax13 := ax13_sig
  ax14 := ax14_sig
  ax15 := ax15_sig
  ax16 := ax16_sig
  ax17 := ax17_sig

end RelatorRepair.Model3_1
