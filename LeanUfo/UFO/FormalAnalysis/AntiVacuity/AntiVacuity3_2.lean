import LeanUfo.UFO.FormalAnalysis.AntiVacuity.AntiVacuity3_1
import LeanUfo.UFO.Core.Section3_2

/-!
# Taxonomy model through section 3.2

This one-world extension supplies the rigid-kind branch used by the cumulative
section 3.3 and 3.4 taxonomy model. A separate multi-world anti-vacuity model
is required to inhabit every section 3.2 rigidity and sortality category.
-/

namespace AntiVacuity.Taxonomy

def sig2 : UFOSignature3_2 where
  toUFOSignature3_1 := sig1
  Rigid := fun x _ => endurantType x
  AntiRigid := fun _ _ => False
  SemiRigid := fun _ _ => False
  Kind := fun x _ => endurantType x
  Sortal := fun x _ => endurantType x
  NonSortal := fun _ _ => False
  SubKind := fun _ _ => False
  Phase := fun _ _ => False
  Role := fun _ _ => False
  SemiRigidSortal := fun _ _ => False
  Category := fun _ _ => False
  Mixin := fun _ _ => False
  PhaseMixin := fun _ _ => False
  RoleMixin := fun _ _ => False

attribute [simp] sig2

theorem ax18_sig : ax_a18 sig2 := by
  intro t w; cases t <;> cases w <;> simp [Frame.Box, Frame.Dia]

theorem ax19_sig : ax_a19 sig2 := by
  intro t w
  cases t with
  | individual leaf => cases leaf <;> cases w <;> simp [Frame.Dia]
  | kind leaf =>
      cases leaf <;> cases w <;> simp [Frame.Dia]
      all_goals exact ⟨.individual _, rfl⟩

theorem ax20_sig : ax_a20 sig2 := by intro t w; cases t <;> cases w <;> simp

theorem ax21_sig : ax_a21 sig2 := by
  intro x w hx
  cases x with
  | kind leaf => simp_all
  | individual leaf =>
      cases leaf with
      | object => exact ⟨.kind .object, by simp [Frame.Box]⟩
      | collective => exact ⟨.kind .collective, by simp [Frame.Box]⟩
      | quantity => exact ⟨.kind .quantity, by simp [Frame.Box]⟩
      | relator => exact ⟨.kind .relator, by simp [Frame.Box]⟩
      | mode => exact ⟨.kind .mode, by simp [Frame.Box]⟩
      | quality => exact ⟨.kind .quality, by simp [Frame.Box]⟩
      | abstract => simp_all
      | perdurant => simp_all

theorem ax22_sig : ax_a22 sig2 := by
  intro k x w h hdia
  rcases hdia with ⟨v, _hv, z, hzKind, hzInst, hzNe⟩
  exact hzNe (inst_target_unique h.2 hzInst).symm

theorem ax23_sig : ax_a23 sig2 := by
  intro t w
  constructor
  · intro h; exact ⟨h, t, h, fun _ _ _ hx => hx⟩
  · intro h; exact h.1

theorem ax24_sig : ax_a24 sig2 := by intro t w; cases t <;> cases w <;> simp
theorem ax25_sig : ax_a25 sig2 := by intro w; simp
theorem ax26_sig : ax_a26 sig2 := by intro t w; cases t <;> cases w <;> simp
theorem ax27_sig : ax_a27 sig2 := by intro w; simp
theorem ax28_sig : ax_a28 sig2 := by intro t w; cases t <;> cases w <;> simp
theorem ax29_sig : ax_a29 sig2 := by intro t w; cases t <;> cases w <;> simp
theorem ax30_sig : ax_a30 sig2 := by intro t w; cases t <;> cases w <;> simp
theorem ax31_sig : ax_a31 sig2 := by intro t w; cases t <;> cases w <;> simp
theorem ax32_sig : ax_a32 sig2 := by intro w; simp
theorem ax33_sig : ax_a33 sig2 := by intro t w; cases t <;> cases w <;> simp

theorem ax_instEndurant_sig : ax_instEndurant_of_EndurantType (Sig := sig2) := by
  intro t x w hType hInst
  cases t <;> rename_i tl <;> cases tl <;>
    cases x <;> rename_i xl <;> cases xl <;> cases w <;> simp_all

theorem ax_sub_kind_sortal_sig : ax_sub_of_kind_is_sortal (Sig := sig2) := by
  intro a k w hSub hKind
  rcases type_has_instance hSub.1 with ⟨x, hxa⟩
  have hxk := hSub.2.2 () trivial x hxa
  have hak : a = k := inst_target_unique hxa hxk
  subst k
  simpa using hKind

theorem ax_nonSortal_up_sig : ax_nonSortal_upward (Sig := sig2) := by
  intro a b w h; exact False.elim h

theorem ax_kindStable_sig : ax_kindStable sig2 := by
  intro k w v hk _; exact hk

instance axioms2 : UFOAxioms3_2 sig2 where
  toUFOAxioms3_1 := axioms1
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

end AntiVacuity.Taxonomy

/-!
## Complete section 3.2 anti-vacuity model

The common taxonomy model above is intentionally rigid because later files use
it to classify the six endurant leaves. The following independent model checks
all section 3.2 categories simultaneously. It still satisfies the complete
cumulative package through section 3.2.
-/

namespace AntiVacuity.Section3_2

inductive World
  | actual | alternative
  deriving DecidableEq, Repr

/- The first twelve constructors are types. The five remaining constructors
are individuals. `i1` and `j1` instantiate the first kind; `i2` instantiates
the second kind. -/
inductive Thing
  | k1 | k2 | subkind | phase | role | semiSortal
  | category | mixin | phaseMixin | roleMixin
  | abstractType | perdurantType
  | i1 | j1 | i2 | abstractIndividual | perdurantIndividual
  deriving DecidableEq, Repr

def frame : S5Frame where
  World := World
  R := fun _ _ => True
  refl := by simp
  symm := by simp
  trans := by simp

def isType : Thing -> Prop
  | .k1 | .k2 | .subkind | .phase | .role | .semiSortal
  | .category | .mixin | .phaseMixin | .roleMixin
  | .abstractType | .perdurantType => True
  | _ => False

/- Instantiation profiles determine the modal categories.

Rigid extensions are constant. Anti-rigid extensions occur only at `actual`.
The semi-rigid sortal has one constant and one contingent instance. The mixin
has a first-kind instance constantly and a second-kind instance contingently.
The category contains both complete kind extensions at both worlds. -/
def inst : Thing -> Thing -> World -> Prop
  | .i1, .k1, _ | .j1, .k1, _ | .i2, .k2, _ => True
  | .i1, .subkind, _ => True
  | .i2, .phase, .actual | .i1, .role, .actual => True
  | .i1, .semiSortal, _ | .j1, .semiSortal, .actual => True
  | .i1, .category, _ | .j1, .category, _ | .i2, .category, _ => True
  | .i1, .mixin, _ | .i2, .mixin, .actual => True
  | .i1, .phaseMixin, .actual | .i2, .phaseMixin, .actual => True
  | .i1, .roleMixin, .actual | .i2, .roleMixin, .actual => True
  | .abstractIndividual, .abstractType, _ => True
  | .perdurantIndividual, .perdurantType, _ => True
  | _, _, _ => False

def endurant : Thing -> Prop
  | .i1 | .j1 | .i2 => True
  | _ => False

def endurantType : Thing -> Prop
  | .k1 | .k2 | .subkind | .phase | .role | .semiSortal
  | .category | .mixin | .phaseMixin | .roleMixin => True
  | _ => False

def kind : Thing -> Prop
  | .k1 | .k2 => True
  | _ => False

def rigid (t : Thing) (w : World) : Prop :=
  endurantType t ∧ ∀ x,
    Frame.Dia (F := frame) (fun w' => inst x t w') w ->
    Frame.Box (F := frame) (fun w' => inst x t w') w

def antiRigid (t : Thing) (w : World) : Prop :=
  endurantType t ∧ ∀ x,
    Frame.Dia (F := frame) (fun w' => inst x t w') w ->
    Frame.Dia (F := frame) (fun w' => ¬ inst x t w') w

def sortal (t : Thing) (w : World) : Prop :=
  endurantType t ∧ ∃ k, kind k ∧
    Frame.Box (F := frame) (fun w' => ∀ x, inst x t w' -> inst x k w') w

def sig : UFOSignature3_2 where
  F := frame
  Thing := Thing
  thing_nonempty := ⟨.i1⟩
  Type_ := fun x _ => isType x
  Individual := fun x _ => ¬ isType x
  Inst := inst
  Sub := fun x y w => isType x ∧ isType y ∧
    Frame.Box (F := frame) (fun w' => ∀ z, inst z x w' -> inst z y w') w
  ConcreteIndividual := fun x _ => endurant x ∨ x = .perdurantIndividual
  AbstractIndividual := fun x _ => x = .abstractIndividual
  Endurant := fun x _ => endurant x
  Perdurant := fun x _ => x = .perdurantIndividual
  EndurantType := fun x _ => endurantType x
  PerdurantType := fun x _ => x = .perdurantType
  Rigid := rigid
  AntiRigid := antiRigid
  SemiRigid := fun t w => endurantType t ∧ ¬ rigid t w ∧ ¬ antiRigid t w
  Kind := fun t _ => kind t
  Sortal := sortal
  NonSortal := fun t w => endurantType t ∧ ¬ sortal t w
  SubKind := fun t _ => t = .subkind
  Phase := fun t _ => t = .phase
  Role := fun t _ => t = .role
  SemiRigidSortal := fun t _ => t = .semiSortal
  Category := fun t _ => t = .category
  Mixin := fun t _ => t = .mixin
  PhaseMixin := fun t _ => t = .phaseMixin
  RoleMixin := fun t _ => t = .roleMixin

attribute [simp] frame isType inst endurant endurantType kind sig

theorem rigid_iff (t : Thing) (w : World) :
    rigid t w ↔ t = .k1 ∨ t = .k2 ∨ t = .subkind ∨ t = .category := by
  cases t <;> cases w <;> simp [rigid, Frame.Box, Frame.Dia]
  all_goals try (intro x u hx v; cases x <;> cases u <;> cases v <;> simp_all)
  case phase.actual => exact ⟨.i2, ⟨.actual, trivial⟩, .alternative, fun h => h⟩
  case phase.alternative => exact ⟨.i2, ⟨.actual, trivial⟩, .alternative, fun h => h⟩
  case role.actual => exact ⟨.i1, ⟨.actual, trivial⟩, .alternative, fun h => h⟩
  case role.alternative => exact ⟨.i1, ⟨.actual, trivial⟩, .alternative, fun h => h⟩
  case semiSortal.actual => exact ⟨.j1, ⟨.actual, trivial⟩, .alternative, fun h => h⟩
  case semiSortal.alternative => exact ⟨.j1, ⟨.actual, trivial⟩, .alternative, fun h => h⟩
  case mixin.actual => exact ⟨.i2, ⟨.actual, trivial⟩, .alternative, fun h => h⟩
  case mixin.alternative => exact ⟨.i2, ⟨.actual, trivial⟩, .alternative, fun h => h⟩
  case phaseMixin.actual => exact ⟨.i1, ⟨.actual, trivial⟩, .alternative, fun h => h⟩
  case phaseMixin.alternative => exact ⟨.i1, ⟨.actual, trivial⟩, .alternative, fun h => h⟩
  case roleMixin.actual => exact ⟨.i1, ⟨.actual, trivial⟩, .alternative, fun h => h⟩
  case roleMixin.alternative => exact ⟨.i1, ⟨.actual, trivial⟩, .alternative, fun h => h⟩

theorem antiRigid_iff (t : Thing) (w : World) :
    antiRigid t w ↔ t = .phase ∨ t = .role ∨
      t = .phaseMixin ∨ t = .roleMixin := by
  cases t <;> cases w <;> simp [antiRigid, Frame.Dia]
  all_goals try (
    intro x u hu
    cases x <;> cases u <;> simp_all
    all_goals exact ⟨.alternative, fun h => h⟩)
  case k1.actual => exact ⟨.i1, ⟨.actual, trivial⟩, by intro v; cases v <;> trivial⟩
  case k1.alternative => exact ⟨.i1, ⟨.actual, trivial⟩, by intro v; cases v <;> trivial⟩
  case k2.actual => exact ⟨.i2, ⟨.actual, trivial⟩, by intro v; cases v <;> trivial⟩
  case k2.alternative => exact ⟨.i2, ⟨.actual, trivial⟩, by intro v; cases v <;> trivial⟩
  case subkind.actual => exact ⟨.i1, ⟨.actual, trivial⟩, by intro v; cases v <;> trivial⟩
  case subkind.alternative => exact ⟨.i1, ⟨.actual, trivial⟩, by intro v; cases v <;> trivial⟩
  case semiSortal.actual => exact ⟨.i1, ⟨.actual, trivial⟩, by intro v; cases v <;> trivial⟩
  case semiSortal.alternative => exact ⟨.i1, ⟨.actual, trivial⟩, by intro v; cases v <;> trivial⟩
  case category.actual => exact ⟨.i1, ⟨.actual, trivial⟩, by intro v; cases v <;> trivial⟩
  case category.alternative => exact ⟨.i1, ⟨.actual, trivial⟩, by intro v; cases v <;> trivial⟩
  case mixin.actual => exact ⟨.i1, ⟨.actual, trivial⟩, by intro v; cases v <;> trivial⟩
  case mixin.alternative => exact ⟨.i1, ⟨.actual, trivial⟩, by intro v; cases v <;> trivial⟩

theorem sortal_iff (t : Thing) (w : World) :
    sortal t w ↔ t = .k1 ∨ t = .k2 ∨ t = .subkind ∨
      t = .phase ∨ t = .role ∨ t = .semiSortal := by
  cases t <;> cases w <;> simp [sortal, Frame.Box]
  case k1.actual => exact ⟨.k1, by simp, by intro v x hx; cases v <;> cases x <;> simp_all⟩
  case k1.alternative => exact ⟨.k1, by simp, by intro v x hx; cases v <;> cases x <;> simp_all⟩
  case k2.actual => exact ⟨.k2, by simp, by intro v x hx; cases v <;> cases x <;> simp_all⟩
  case k2.alternative => exact ⟨.k2, by simp, by intro v x hx; cases v <;> cases x <;> simp_all⟩
  case subkind.actual => exact ⟨.k1, by simp, by intro v x hx; cases v <;> cases x <;> simp_all⟩
  case subkind.alternative => exact ⟨.k1, by simp, by intro v x hx; cases v <;> cases x <;> simp_all⟩
  case phase.actual => exact ⟨.k2, by simp, by intro v x hx; cases v <;> cases x <;> simp_all⟩
  case phase.alternative => exact ⟨.k2, by simp, by intro v x hx; cases v <;> cases x <;> simp_all⟩
  case role.actual => exact ⟨.k1, by simp, by intro v x hx; cases v <;> cases x <;> simp_all⟩
  case role.alternative => exact ⟨.k1, by simp, by intro v x hx; cases v <;> cases x <;> simp_all⟩
  case semiSortal.actual => exact ⟨.k1, by simp, by intro v x hx; cases v <;> cases x <;> simp_all⟩
  case semiSortal.alternative => exact ⟨.k1, by simp, by intro v x hx; cases v <;> cases x <;> simp_all⟩
  all_goals
    intro k
    intro hk
    cases k <;> simp_all
    · exact ⟨.actual, .i2, trivial, fun h => h⟩
    · exact ⟨.actual, .i1, trivial, fun h => h⟩

attribute [simp] rigid_iff antiRigid_iff sortal_iff

theorem ax1_sig : ax_a1 sig.toUFOSignature3_1 := by
  intro t w
  constructor
  · intro ht
    cases t <;> cases w <;> simp_all [Frame.Dia]
    all_goals
      first
      | exact ⟨.actual, .i1, trivial⟩
      | exact ⟨.actual, .i2, trivial⟩
      | exact ⟨.actual, .j1, trivial⟩
      | exact ⟨.actual, .abstractIndividual, trivial⟩
      | exact ⟨.actual, .perdurantIndividual, trivial⟩
  · rintro ⟨v, _, x, hx⟩
    cases t <;> cases v <;> cases x <;> simp_all

theorem ax2_sig : ax_a2 sig.toUFOSignature3_1 := by
  intro x w
  change (¬ isType x) ↔
    Frame.Box (F := frame) (fun w' => ¬ ∃ y, inst y x w') w
  calc
    (¬ isType x) ↔
        ¬ Frame.Dia (F := frame) (fun w' => ∃ y, inst y x w') w :=
      not_congr (ax1_sig x w)
    _ ↔ Frame.Box (F := frame) (fun w' => ¬ ∃ y, inst y x w') w :=
      not_dia_iff_box_not (F := frame) _ w

theorem ax3_sig : ax_a3 sig.toUFOSignature3_1 := by
  intro x t w h; cases x <;> cases t <;> cases w <;> simp_all

theorem ax4_sig : ax_a4 sig.toUFOSignature3_1 := by
  intro w h
  rcases h with ⟨x, y, z, h⟩
  cases x <;> cases w <;> simp_all

theorem ax5_sig : ax_a5 sig.toUFOSignature3_1 := by intro x y w; rfl

private theorem sub_category_of_endurant_instance
    {x t : Thing} {w : World}
    (hx : endurant x) (hxt : inst x t w) :
    sig.Sub t .category w := by
  have ht : t = .k1 ∨ t = .k2 ∨ t = .subkind ∨ t = .phase ∨
      t = .role ∨ t = .semiSortal ∨ t = .category ∨ t = .mixin ∨
      t = .phaseMixin ∨ t = .roleMixin := by
    cases x <;> cases t <;> cases w <;> simp_all
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Frame.Box]
  all_goals intro v z hz; cases v <;> cases z <;> simp_all

theorem ax6_sig : ax_a6 sig.toUFOSignature3_1 := by
  intro t1 t2 x w h
  rcases h with ⟨hx1, hx2, hNot12, hNot21⟩
  by_cases hxEnd : endurant x
  · left
    exact ⟨.category,
      sub_category_of_endurant_instance hxEnd hx1,
      sub_category_of_endurant_instance hxEnd hx2,
      by cases x <;> cases w <;> simp_all⟩
  · cases x <;> simp_all
    all_goals cases t1 <;> cases t2 <;> cases w <;> simp_all [Frame.Box]

theorem ax7_sig : ax_a7 sig.toUFOSignature3_1 := by
  intro x w h; cases x <;> cases w <;> simp_all
theorem ax8_sig : ax_a8 sig.toUFOSignature3_1 := by
  intro x w h; cases x <;> cases w <;> simp_all
theorem ax9_sig : ax_a9 sig.toUFOSignature3_1 := by
  intro x w h; cases x <;> cases w <;> simp_all
theorem ax10_sig : ax_a10 sig.toUFOSignature3_1 := by
  intro x w; cases x <;> cases w <;> simp
theorem ax11_sig : ax_a11 sig.toUFOSignature3_1 := by
  intro x w h; cases x <;> cases w <;> simp_all
theorem ax12_sig : ax_a12 sig.toUFOSignature3_1 := by
  intro x w h; cases x <;> cases w <;> simp_all
theorem ax13_sig : ax_a13 sig.toUFOSignature3_1 := by
  intro x w h; cases x <;> cases w <;> simp_all
theorem ax14_sig : ax_a14 sig.toUFOSignature3_1 := by
  intro x w; cases x <;> cases w <;> simp
theorem ax15_sig : ax_a15 sig.toUFOSignature3_1 := by
  intro x w h; cases x <;> cases w <;> simp_all
theorem ax16_sig : ax_a16 sig.toUFOSignature3_1 := by
  intro x w h; cases x <;> cases w <;> simp_all
theorem ax17_sig : ax_a17 sig.toUFOSignature3_1 := by
  intro x w h; cases x <;> cases w <;> simp_all

theorem ax18_sig : ax_a18 sig := by intro t w; rfl
theorem ax19_sig : ax_a19 sig := by intro t w; rfl
theorem ax20_sig : ax_a20 sig := by intro t w; rfl

theorem ax21_sig : ax_a21 sig := by
  intro x w h
  cases x <;> cases w <;> simp_all [Frame.Box]
  · exact ⟨.k1, by simp⟩
  · exact ⟨.k1, by simp⟩
  · exact ⟨.k1, by simp⟩
  · exact ⟨.k1, by simp⟩
  · exact ⟨.k2, by simp⟩
  · exact ⟨.k2, by simp⟩

theorem ax22_sig : ax_a22 sig := by
  intro k x w h hdia
  rcases hdia with ⟨v, _hv, z, hzKind, hzInst, hzNe⟩
  have hk : k = .k1 ∨ k = .k2 := by cases k <;> simp_all
  have hz : z = .k1 ∨ z = .k2 := by cases z <;> simp_all
  rcases hk with rfl | rfl <;> rcases hz with rfl | rfl
  · exact hzNe rfl
  · cases x <;> cases w <;> cases v <;> simp_all
  · cases x <;> cases w <;> cases v <;> simp_all
  · exact hzNe rfl

theorem ax23_sig : ax_a23 sig := by intro t w; rfl
theorem ax24_sig : ax_a24 sig := by intro t w; rfl
theorem ax25_sig : ax_a25 sig := by intro w; cases w <;> simp
theorem ax26_sig : ax_a26 sig := by
  intro t w; cases t <;> cases w <;> simp [rigid_iff, sortal_iff]
theorem ax27_sig : ax_a27 sig := by intro w; cases w <;> simp
theorem ax28_sig : ax_a28 sig := by
  intro t w; cases t <;> cases w <;> simp [antiRigid_iff, sortal_iff]
theorem ax29_sig : ax_a29 sig := by
  intro t w; cases t <;> cases w <;>
    simp [rigid_iff, antiRigid_iff, sortal_iff]
theorem ax30_sig : ax_a30 sig := by
  intro t w; cases t <;> cases w <;> simp [rigid_iff, sortal_iff]
theorem ax31_sig : ax_a31 sig := by
  intro t w; cases t <;> cases w <;>
    simp [rigid_iff, antiRigid_iff, sortal_iff]
theorem ax32_sig : ax_a32 sig := by intro w; cases w <;> simp
theorem ax33_sig : ax_a33 sig := by
  intro t w; cases t <;> cases w <;> simp [antiRigid_iff, sortal_iff]

theorem ax_instEndurant_sig : ax_instEndurant_of_EndurantType (Sig := sig) := by
  intro t x w ht hx
  cases t <;> cases x <;> cases w <;> simp_all

theorem ax_sub_kind_sortal_sig : ax_sub_of_kind_is_sortal (Sig := sig) := by
  intro a k w hSub hKind
  have hEnd : endurantType a := by
    have hIncl := hSub.2.2
    cases a <;> try trivial
    · have hTarget := hIncl .actual trivial .abstractIndividual (by simp)
      cases k <;> simp_all
    · have hTarget := hIncl .actual trivial .perdurantIndividual (by simp)
      cases k <;> simp_all
    all_goals simp_all
  exact ⟨hEnd, k, hKind, hSub.2.2⟩

theorem ax_nonSortal_up_sig : ax_nonSortal_upward (Sig := sig) := by
  intro a b w hNon hSub
  have ha : a = .category ∨ a = .mixin ∨
      a = .phaseMixin ∨ a = .roleMixin := by
    cases a <;> cases w <;> simp_all [sortal_iff]
  have hi1a : inst .i1 a .actual := by
    rcases ha with rfl | rfl | rfl | rfl <;> simp
  have hi2a : inst .i2 a .actual := by
    rcases ha with rfl | rfl | rfl | rfl <;> simp
  have hi1b := hSub.2.2 .actual trivial .i1 hi1a
  have hi2b := hSub.2.2 .actual trivial .i2 hi2a
  cases b <;> cases w <;> simp_all [sortal_iff]

theorem ax_kindStable_sig : ax_kindStable sig := by
  intro k w v hk _
  cases k <;> cases w <;> cases v <;> simp_all

instance axioms : UFOAxioms3_2 sig where
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

theorem predicates_nonempty :
    (∃ x, sig.Rigid x .actual) ∧
    (∃ x, sig.AntiRigid x .actual) ∧
    (∃ x, sig.SemiRigid x .actual) ∧
    (∃ x, sig.Kind x .actual) ∧
    (∃ x, sig.Sortal x .actual) ∧
    (∃ x, sig.NonSortal x .actual) ∧
    (∃ x, sig.SubKind x .actual) ∧
    (∃ x, sig.Phase x .actual) ∧
    (∃ x, sig.Role x .actual) ∧
    (∃ x, sig.SemiRigidSortal x .actual) ∧
    (∃ x, sig.Category x .actual) ∧
    (∃ x, sig.Mixin x .actual) ∧
    (∃ x, sig.PhaseMixin x .actual) ∧
    (∃ x, sig.RoleMixin x .actual) := by
  refine ⟨⟨.k1, (rigid_iff .k1 .actual).2 (by simp)⟩,
    ⟨.phase, (antiRigid_iff .phase .actual).2 (by simp)⟩,
    ⟨.semiSortal, by simp [rigid_iff, antiRigid_iff]⟩,
    ⟨.k1, by simp⟩, ⟨.k1, (sortal_iff .k1 .actual).2 (by simp)⟩,
    ⟨.category, by simp [sortal_iff]⟩, ⟨.subkind, by simp⟩,
    ⟨.phase, by simp⟩, ⟨.role, by simp⟩, ⟨.semiSortal, by simp⟩,
    ⟨.category, by simp⟩, ⟨.mixin, by simp⟩,
    ⟨.phaseMixin, by simp⟩, ⟨.roleMixin, by simp⟩⟩

/- The same multi-world model covers every predicate of section 3.1.
`subkind` has the constant instance `i1`, while `k1` additionally has `j1`;
therefore `subkind` is a proper specialization of `k1`. -/
theorem section3_1_predicates_nonempty :
    (∃ x w, sig.Type_ x w) ∧
    (∃ x w, sig.Individual x w) ∧
    (∃ x t w, sig.Inst x t w) ∧
    (∃ t u w, sig.Sub t u w) ∧
    (∃ t u w, ProperSub sig.toUFOSignature3_1 t u w) ∧
    (∃ x w, sig.ConcreteIndividual x w) ∧
    (∃ x w, sig.AbstractIndividual x w) ∧
    (∃ x w, sig.Endurant x w) ∧
    (∃ x w, sig.Perdurant x w) ∧
    (∃ t w, sig.EndurantType t w) ∧
    (∃ t w, sig.PerdurantType t w) := by
  refine ⟨⟨.k1, .actual, trivial⟩,
    ⟨.i1, .actual, by simp⟩,
    ⟨.i1, .k1, .actual, trivial⟩,
    ⟨.subkind, .k1, .actual, ?_⟩,
    ⟨.subkind, .k1, .actual, ?_⟩,
    ⟨.i1, .actual, Or.inl trivial⟩,
    ⟨.abstractIndividual, .actual, by simp⟩,
    ⟨.i1, .actual, trivial⟩,
    ⟨.perdurantIndividual, .actual, by simp⟩,
    ⟨.k1, .actual, trivial⟩,
    ⟨.perdurantType, .actual, by simp⟩⟩
  · refine ⟨trivial, trivial, ?_⟩
    intro v _ x hx
    cases x <;> cases v <;> simp_all [inst]
  · constructor
    · refine ⟨trivial, trivial, ?_⟩
      intro v _ x hx
      cases x <;> cases v <;> simp_all [inst]
    · rintro ⟨_, _, hbox⟩
      have hbad := hbox .actual trivial .j1 trivial
      cases hbad

end AntiVacuity.Section3_2
