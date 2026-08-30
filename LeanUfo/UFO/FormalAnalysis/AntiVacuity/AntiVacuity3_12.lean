import LeanUfo.UFO.Core.Section3_12
import Mathlib.Data.Set.Insert

/-!
# Quality-structure anti-vacuity analysis through section 3.12

The section 3.12 axioms require more than a nonempty quality predicate. A quale
must belong to a unique quality structure, quality structures are nonempty
set-like abstract individuals, and quales and sets are disjoint. The model
therefore uses distinct entities for two quales, a quality dimension, and a
quality domain.

The concrete part contains one bearer, one simple quality, and one complex
quality. The simple quality inheres in the complex quality, which in turn
inheres in the bearer. Their separate kinds support both simple and complex
quality types. The complex quale belongs to the domain; its sole tuple
projection is the simple quale in the dimension. One distance value serves all
pairs of quales and is also the zero, sum, and order witness.

The carrier also includes `metaKind`, whose only instance is
`simpleQualityKind`. It has no section 3.12 classification and does not alter
the quality witnesses. It supplies the type-level instantiation needed when
this cumulative model is extended with `Categorizes` in section 4.
-/

namespace AntiVacuity.Section3_12

set_option maxHeartbeats 300000

inductive Thing
  | metaKind | objectKind | simpleQualityKind | complexQualityKind | perdurantKind
  | bearer | simpleQuality | complexQuality | life
  | simpleQuale | complexQuale | dimension | domain | superSet | distanceValue
  deriving DecidableEq, Repr

abbrev World := Unit

def frame : S5Frame where
  World := World
  R := fun _ _ => True
  refl := by simp
  symm := by simp
  trans := by simp

def isType : Thing -> Prop
  | .metaKind | .objectKind | .simpleQualityKind | .complexQualityKind | .perdurantKind => True
  | _ => False

def inst : Thing -> Thing -> Prop
  | .simpleQualityKind, .metaKind
  | .bearer, .objectKind
  | .simpleQuality, .simpleQualityKind
  | .complexQuality, .complexQualityKind
  | .life, .perdurantKind => True
  | _, _ => False

def endurant : Thing -> Prop
  | .bearer | .simpleQuality | .complexQuality => True
  | _ => False

def perdurant : Thing -> Prop
  | .life => True
  | _ => False

def endurantType : Thing -> Prop
  | .objectKind | .simpleQualityKind | .complexQualityKind => True
  | _ => False

def perdurantType : Thing -> Prop
  | .perdurantKind => True
  | _ => False

def quality : Thing -> Prop
  | .simpleQuality | .complexQuality => True
  | _ => False

def sig1 : UFOSignature3_1 where
  F := frame
  Thing := Thing
  thing_nonempty := ⟨.bearer⟩
  Type_ := fun x _ => isType x
  Individual := fun x _ => ¬ isType x
  Inst := fun x t _ => inst x t
  Sub := fun x y w => isType x ∧ isType y ∧
    Frame.Box (F := frame) (fun _ => ∀ z, inst z x -> inst z y) w
  ConcreteIndividual := fun x _ => endurant x ∨ perdurant x
  AbstractIndividual := fun x _ => ¬ isType x ∧ ¬ endurant x ∧ ¬ perdurant x
  Endurant := fun x _ => endurant x
  Perdurant := fun x _ => perdurant x
  EndurantType := fun x _ => endurantType x
  PerdurantType := fun x _ => perdurantType x

attribute [simp] frame isType inst endurant perdurant endurantType perdurantType quality sig1

private theorem type_has_instance {t : Thing} (ht : isType t) :
    ∃ x, inst x t := by
  cases t <;> simp_all
  · exact ⟨.simpleQualityKind, trivial⟩
  · exact ⟨.bearer, trivial⟩
  · exact ⟨.simpleQuality, trivial⟩
  · exact ⟨.complexQuality, trivial⟩
  · exact ⟨.life, trivial⟩

private theorem inst_target_unique {x t u : Thing}
    (ht : inst x t) (hu : inst x u) : t = u := by
  cases x <;> cases t <;> cases u <;> simp_all

theorem ax1_sig : ax_a1 sig1 := by
  intro t w; constructor
  · intro ht
    rcases type_has_instance ht with ⟨x, hx⟩
    exact ⟨(), trivial, x, hx⟩
  · rintro ⟨_, _, x, hx⟩
    cases x <;> cases t <;> simp_all

theorem ax2_sig : ax_a2 sig1 := by
  intro x w
  change (¬ isType x) ↔ Frame.Box (F := frame) (fun _ => ¬ ∃ y, inst y x) w
  constructor
  · intro hx _ _ h; rcases h with ⟨y, hy⟩
    cases y <;> cases x <;> simp_all
  · intro h hx
    rcases type_has_instance hx with ⟨y, hy⟩
    exact h () trivial ⟨y, hy⟩

theorem ax3_sig : ax_a3 sig1 := by
  intro x t w h; cases x <;> cases t <;> simp_all

theorem ax4_sig : ax_a4 sig1 := by
  intro w h; rcases h with ⟨x, y, z, hx, hxy, hyz⟩
  cases x <;> cases y <;> simp_all

theorem ax5_sig : ax_a5 sig1 := by intro x y w; rfl

theorem ax6_sig : ax_a6 sig1 := by
  intro t u x w h
  have htu := inst_target_unique h.1 h.2.1
  subst u
  have ht : isType t := by cases x <;> cases t <;> simp_all
  exact False.elim (h.2.2.1 ⟨ht, ht, by intro _ _ z hz; exact hz⟩)

theorem ax7_sig : ax_a7 sig1 := by
  intro x w h; cases x <;> simp_all
theorem ax8_sig : ax_a8 sig1 := by
  intro x w h; cases x <;> simp_all
theorem ax9_sig : ax_a9 sig1 := by
  intro x w h; cases x <;> simp_all
theorem ax10_sig : ax_a10 sig1 := by
  intro x w; cases x <;> simp
theorem ax11_sig : ax_a11 sig1 := by
  intro x w h; cases x <;> simp_all
theorem ax12_sig : ax_a12 sig1 := by
  intro x w h; cases x <;> simp_all
theorem ax13_sig : ax_a13 sig1 := by
  intro x w h; cases x <;> simp_all
theorem ax14_sig : ax_a14 sig1 := by
  intro x w; cases x <;> simp
theorem ax15_sig : ax_a15 sig1 := by
  intro x w h; cases x <;> simp_all
theorem ax16_sig : ax_a16 sig1 := by
  intro x w h; cases x <;> simp_all
theorem ax17_sig : ax_a17 sig1 := by
  intro x w h; cases x <;> simp_all

instance axioms1 : UFOAxioms3_1 sig1 where
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

instance axioms2 : UFOAxioms3_2 sig2 where
  toUFOAxioms3_1 := axioms1
  ax18 := by intro t w; cases t <;> simp [Frame.Box, Frame.Dia]
  ax19 := by
    intro t w; cases t <;> simp [Frame.Dia]
    · exact ⟨.bearer, trivial⟩
    · exact ⟨.simpleQuality, trivial⟩
    · exact ⟨.complexQuality, trivial⟩
  ax20 := by intro t w; cases t <;> simp
  ax21 := by
    intro x w hx; cases x <;> simp_all [Frame.Box]
    · exact ⟨.objectKind, ⟨trivial, trivial⟩⟩
    · exact ⟨.simpleQualityKind, ⟨trivial, trivial⟩⟩
    · exact ⟨.complexQualityKind, ⟨trivial, trivial⟩⟩
  ax22 := by
    intro k x w h hdia
    rcases hdia with ⟨_, _, z, hz, hzx, hne⟩
    exact hne (inst_target_unique h.2 hzx).symm
  ax23 := by
    intro t w; constructor
    · intro h; exact ⟨h, t, h, by intro _ _ _ hx; exact hx⟩
    · intro h; exact h.1
  ax24 := by intro t w; cases t <;> simp
  ax25 := by intro w; simp
  ax26 := by intro t w; cases t <;> simp
  ax27 := by intro w; simp
  ax28 := by intro t w; cases t <;> simp
  ax29 := by intro t w; cases t <;> simp
  ax30 := by intro t w; cases t <;> simp
  ax31 := by intro t w; cases t <;> simp
  ax32 := by intro w; simp
  ax33 := by intro t w; cases t <;> simp
  ax_instEndurant := by
    intro t x w ht hx; cases t <;> cases x <;> simp_all
  ax_sub_kind_sortal := by
    intro a k w hSub hKind
    rcases type_has_instance hSub.1 with ⟨x, hxa⟩
    have hxk := hSub.2.2 () trivial x hxa
    have hak := inst_target_unique hxa hxk
    subst k
    exact hKind
  ax_nonSortal_up := by intro a b w h; cases h
  ax_kindStable := by intro k w v hk _; exact hk

/- The two qualities are intrinsic moments; the bearer is the sole
substantial. `Quality` is derived from the explicit quality-kind table, so the
proofs below also check that no unrelated entity acquires that classification.
-/
def sig3 : UFOSignature3_3 where
  toUFOSignature3_2 := sig2
  Substantial := fun x _ => x = .bearer
  Moment := fun x _ => quality x
  Object := fun x _ => x = .bearer
  Collective := fun _ _ => False
  Quantity := fun _ _ => False
  Relator := fun _ _ => False
  IntrinsicMoment := fun x _ => quality x
  Mode := fun _ _ => False
  QualityKind := fun t _ => t = .simpleQualityKind ∨ t = .complexQualityKind

attribute [simp] sig3

@[simp] theorem quality_iff (x : Thing) (w : World) :
    Quality sig3 x w ↔ quality x := by
  cases x <;> simp only [quality]
  all_goals unfold Quality
  all_goals constructor
  all_goals try { rintro ⟨t, ht, _⟩ <;> cases t <;> simp_all }
  · intro _
    refine ⟨.simpleQualityKind, ⟨Or.inl rfl, trivial⟩, ?_⟩
    intro y hy; cases y <;> simp_all
  · intro _
    refine ⟨.complexQualityKind, ⟨Or.inr rfl, trivial⟩, ?_⟩
    intro y hy; cases y <;> simp_all

instance axioms3 : UFOAxioms3_3 sig3 where
  toUFOAxioms3_2 := axioms2
  ax34 := by intro x w; cases x <;> simp [quality, endurant]
  ax35 := by intro w h; rcases h with ⟨x, h⟩; cases x <;> simp_all [quality]
  ax36 := by intro x w; cases x <;> simp
  ax37 := by intro w; simp
  ax38 := by intro w; simp
  ax39 := by intro w; simp
  ax40 := by intro x w; cases x <;> simp [quality]
  ax41 := by intro w; simp
  ax42 := by
    intro x w
    change (False ∨ Quality sig3 x w) ↔ quality x
    simp only [false_or]
    exact quality_iff x w
  ax43 := by intro w; simp

/- Each type-level category is defined by the modal profile in (a44). This
avoids maintaining a second classification table alongside instantiation. -/
def allInstances (P : Thing -> World -> Prop) (t : Thing) (w : World) : Prop :=
  isType t ∧ Frame.Box (F := frame)
    (fun w' => ∀ x, inst x t -> P x w') w

def sig4 : UFOSignature3_4 where
  toUFOSignature3_3 := sig3
  SubstantialType := allInstances (fun x _ => x = .bearer)
  MomentType := allInstances (fun x _ => quality x)
  ObjectType := allInstances (fun x _ => x = .bearer)
  CollectiveType := allInstances (fun _ _ => False)
  QuantityType := allInstances (fun _ _ => False)
  RelatorType := allInstances (fun _ _ => False)
  ModeType := allInstances (fun _ _ => False)
  QualityType := fun t _ =>
    t = .simpleQualityKind ∨ t = .complexQualityKind
  ObjectKind := fun t w => allInstances (fun x _ => x = .bearer) t w ∧ sig2.Kind t w
  CollectiveKind := fun t w => allInstances (fun _ _ => False) t w ∧ sig2.Kind t w
  QuantityKind := fun t w => allInstances (fun _ _ => False) t w ∧ sig2.Kind t w
  RelatorKind := fun t w => allInstances (fun _ _ => False) t w ∧ sig2.Kind t w
  ModeKind := fun t w => allInstances (fun _ _ => False) t w ∧ sig2.Kind t w

attribute [simp] allInstances sig4

private theorem no_all_false (t : Thing) (w : World) :
    ¬ allInstances (fun _ _ => False) t w := by
  rintro ⟨ht, hbox⟩
  rcases type_has_instance ht with ⟨x, hx⟩
  exact hbox () trivial x hx

instance axioms4 : UFOAxioms3_4 sig4 where
  toUFOAxioms3_3 := axioms3
  ax44 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals intro t w
    · cases t <;> simp [allInstances, Frame.Box, endurantType, endurant]
      all_goals first
        | exact ⟨.simpleQualityKind, trivial, by simp⟩
        | exact ⟨.life, trivial, by simp⟩
        | (intro x hx; cases x <;> simp_all)
    · cases t <;> simp [allInstances, Frame.Box, perdurantType, perdurant]
      all_goals first
        | exact ⟨.simpleQualityKind, trivial, by simp⟩
        | exact ⟨.bearer, trivial, by simp⟩
        | exact ⟨.simpleQuality, trivial, by simp⟩
        | exact ⟨.complexQuality, trivial, by simp⟩
        | (intro x hx; cases x <;> simp_all)
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · constructor
      · rintro (rfl | rfl)
        · refine ⟨trivial, ?_⟩
          intro v _ x hx
          apply (quality_iff x v).2
          cases x <;> simp_all [quality]
        · refine ⟨trivial, ?_⟩
          intro v _ x hx
          apply (quality_iff x v).2
          cases x <;> simp_all [quality]
      · rintro ⟨ht, hbox⟩
        cases t <;> simp_all
        · exact False.elim ((quality_iff .simpleQualityKind ()).1
            (hbox () trivial .simpleQualityKind trivial))
        · exact False.elim ((quality_iff .bearer ()).1
            (hbox () trivial .bearer trivial))
        · exact False.elim ((quality_iff .life ()).1
            (hbox () trivial .life trivial))
  ax45 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro t w
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · cases t <;> simp [allInstances, Frame.Box, quality, endurantType]
  ax46 := by
    intro x w hx
    cases x <;> simp [endurant] at hx
    · refine ⟨(), trivial, .objectKind, Or.inl ?_, trivial⟩
      refine ⟨⟨trivial, ?_⟩, trivial⟩
      intro _ _ y hy; cases y <;> simp_all
    · refine ⟨(), trivial, .simpleQualityKind, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_)))), trivial⟩
      exact Or.inl rfl
    · refine ⟨(), trivial, .complexQualityKind, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_)))), trivial⟩
      exact Or.inr rfl

/- Identity parthood is a full extensional mereology. It is sufficient here:
quality composition in §3.12 is expressed through inherence and set
extensions, not through proper parthood. -/
def sig5 : UFOSignature3_5 where
  toUFOSignature3_4 := sig4
  Part := fun x y _ => x = y
  Overlap := fun x y _ => x = y
  ProperPart := fun _ _ _ => False

attribute [simp] sig5

instance axioms5 : UFOAxioms3_5 sig5 where
  toUFOAxioms3_4 := axioms4
  ax47 := by intro x w; rfl
  ax48 := by intro x y w h; exact h.1
  ax49 := by intro x y z w h; exact h.1.trans h.2
  ax50 := by
    intro x y w; constructor
    · intro h; exact ⟨x, rfl, h⟩
    · rintro ⟨z, rfl, h⟩; exact h
  ax51 := by intro x y w h; exact ⟨y, rfl, h⟩
  ax52 := by
    intro x y w; constructor
    · intro h; cases h
    · intro h; exact False.elim (h.2 h.1.symm)

def gfd (x' y' : Thing) (_w : World) : Prop :=
  ∀ x, (inst x x' ∧ False) -> ∃ y, y ≠ x ∧ inst y y' ∧ False

def ifd (x x' y y' : Thing) (w : World) : Prop :=
  gfd x' y' w ∧ inst x x' ∧ inst y y' ∧ (False -> False)

def sig6 : UFOSignature3_6 where
  toUFOSignature3_5 := sig5
  FunctionsAs := fun _ _ _ => False
  GenericFunctionalDependence := gfd
  IndividualFunctionalDependence := ifd
  ComponentOf := fun x x' y y' w => False ∧ ifd x x' y y' w

attribute [simp] gfd ifd sig6

instance axioms6 : UFOAxioms3_6 sig6 where
  toUFOAxioms3_5 := axioms5
  ax53 := by intro x y w; rfl
  ax54 := by intro x x' y y' w; rfl
  ax55 := by intro x x' y y' w; rfl

def gcd (x' y' : Thing) (_w : World) : Prop :=
  ∀ x, inst x x' -> ∃ y, inst y y' ∧ False

def constitution (x x' y y' : Thing) (w : World) : Prop :=
  inst x x' ∧ inst y y' ∧ gcd x' y' w ∧ False

def sig7 : UFOSignature3_7 where
  toUFOSignature3_6 := sig6
  Ex := fun _ _ => True
  ConstitutedBy := fun _ _ _ => False
  GenericConstitutionalDependence := gcd
  Constitution := constitution

attribute [simp] gcd constitution sig7

instance axioms7 : UFOAxioms3_7 sig7 where
  toUFOAxioms3_6 := axioms6
  ax56 := by intro x y w h; cases h
  ax57 := by intro x y x' y' w h; exact False.elim h.1
  ax58 := by intro x y w; rfl
  ax59 := by intro x x' y y' w; rfl
  ax60 := by intro x y w h; exact False.elim h.2
  ax61 := by intro x y w h; cases h

def sig8 : UFOSignature3_8 where
  toUFOSignature3_7 := sig7
  ExistentialDependence := fun x y w =>
    Frame.Box (F := sig7.F) (fun w' => sig7.Ex x w' -> sig7.Ex y w') w
  ExistentialIndependence := fun x y w =>
    ¬ Frame.Box (F := sig7.F) (fun w' => sig7.Ex x w' -> sig7.Ex y w') w ∧
    ¬ Frame.Box (F := sig7.F) (fun w' => sig7.Ex y w' -> sig7.Ex x w') w

attribute [simp] sig8

instance axioms8 : UFOAxioms3_8 sig8 where
  toUFOAxioms3_7 := axioms7
  ax62 := by intro x w _; trivial
  ax63 := by intro x y w; rfl
  ax64 := by intro x y w; rfl

/- Inherence distinguishes the two quality forms. The simple quality is a
constituent of the complex quality, and the complex quality inheres in the
ordinary bearer. Hence both moments have the same ultimate non-moment bearer.
-/
def inheresIn : Thing -> Thing -> Prop
  | .simpleQuality, .complexQuality
  | .complexQuality, .bearer => True
  | _, _ => False

def sig9 : UFOSignature3_9 where
  toUFOSignature3_8 := sig8
  InheresIn := fun x y _ => inheresIn x y

attribute [simp] inheresIn sig9

private theorem bearer_terminal (w : World) :
    ∀ y, ¬ sig9.InheresIn .bearer y w := by
  intro y; cases y <;> simp

private theorem momentOf_targets {w : World} :
    ∀ {m x : Thing}, MomentOf sig9 m x w ->
      ((m = .simpleQuality -> x = .complexQuality ∨ x = .bearer) ∧
       (m = .complexQuality -> x = .bearer))
  | m, x, MomentOf.direct hi => by
      constructor <;> intro hm <;> subst m <;> cases x <;> simp_all [inheresIn]
  | m, x, @MomentOf.step _ _ y _ _ hi ht => by
      have ih := momentOf_targets ht
      constructor
      · intro hm; subst m
        have hy : y = Thing.complexQuality := by cases y <;> simp_all [inheresIn]
        subst y
        exact Or.inr (ih.2 rfl)
      · intro hm; subst m
        have hy : y = Thing.bearer := by cases y <;> simp_all [inheresIn]
        subst y
        exact False.elim ((not_momentOf_of_no_inheres (Sig := sig9) (bearer_terminal w)) ht)

private theorem complex_momentOf_target {x : Thing} {w : World}
    (h : MomentOf sig9 .complexQuality x w) : x = .bearer :=
  (momentOf_targets h).2 rfl

private theorem simple_ultimate_unique {b : Thing} {w : World}
    (h : UltimateBearerOf sig9 b .simpleQuality w) : b = .bearer := by
  rcases h with ⟨hb, hm⟩
  rcases (momentOf_targets hm).1 rfl with rfl | rfl
  · exact False.elim (hb (by simp [quality]))
  · rfl

set_option maxHeartbeats 5000000 in
instance axioms9 : UFOAxioms3_9 sig9 where
  toUFOAxioms3_8 := axioms8
  ax65 := by intro x y w h v _ _; trivial
  ax66 := by
    intro x y w h; cases x <;> cases y <;> simp_all [inheresIn, quality, isType]
  ax67 := by
    intro x y z w h; cases x <;> cases y <;> cases z <;> simp_all [inheresIn]
  ax68 := by
    intro m w hm
    cases m <;> simp [quality] at hm
    · refine ⟨.bearer, ⟨by simp [quality],
        MomentOf.step (Sig := sig9) (m := Thing.simpleQuality)
          (y := Thing.complexQuality) (x := Thing.bearer)
          (by simp [inheresIn])
          (MomentOf.direct (Sig := sig9) (m := Thing.complexQuality)
            (x := Thing.bearer) (by simp [inheresIn]))⟩, ?_⟩
      intro b hb; exact simple_ultimate_unique hb
    · refine ⟨.bearer, ⟨by simp [quality],
        MomentOf.direct (Sig := sig9) (m := Thing.complexQuality)
          (x := Thing.bearer) (by simp [inheresIn])⟩, ?_⟩
      intro b hb; exact complex_momentOf_target hb.2

def externallyDependent (x y : Thing) (w : World) : Prop :=
  sig9.ExistentialDependence x y w ∧
    ∀ z, sig9.InheresIn x z w -> sig9.ExistentialIndependence y z w

def sig10 : UFOSignature3_10 where
  toUFOSignature3_9 := sig9
  ExternallyDependent := externallyDependent
  ExternallyDependentMode := fun x w =>
    sig9.Mode x w ∧ ∃ y, externallyDependent x y w
  FoundedBy := fun _ _ _ => False
  QuaIndividualOf := fun _ _ _ => False
  QuaIndividual := fun _ _ => False
  Mediates := fun _ _ _ => False

attribute [simp] externallyDependent sig10

instance axioms10 : UFOAxioms3_10 sig10 where
  toUFOAxioms3_9 := axioms9
  ax69 := by intro x y w; rfl
  ax70 := by intro x w; rfl
  ax71 := by intro x y w h; cases h
  ax72 := by intro x w h; exact False.elim h.1
  ax73 := by
    intro x y w; constructor
    · intro h; cases h
    · intro h
      have hx := (h x).1 rfl
      exact False.elim hx.1.1
  ax74 := by intro x w; simp
  ax75 := by intro x w h; cases h
  ax76 := by intro x y z w h; cases h.1
  ax77 := by intro x w h; cases h
  ax78 := by intro x y w h; cases h.1
  ax79 := by
    intro x w; constructor
    · intro h; cases h
    · rintro ⟨⟨y, hy⟩, _⟩; cases hy
  ax80 := by
    intro x y w; constructor
    · intro h; cases h
    · intro h; cases h.1
  axQuaIndividualOfEndurant := by intro x y w h; cases h

/- The complex quality kind is characterized by the simple quality kind. Its
only instance contains exactly one inhering instance of the characterizing
type, and that simple quality has the complex quality as its unique bearer.
-/
def sig11 : UFOSignature3_11 where
  toUFOSignature3_10 := sig10
  Characterization := fun t q _ =>
    t = Thing.complexQualityKind ∧ q = Thing.simpleQualityKind

attribute [simp] sig11

instance axioms11 : UFOAxioms3_11 sig11 where
  toUFOAxioms3_10 := axioms10
  ax81 := by
    intro t m w h
    rcases h with ⟨rfl, rfl⟩
    refine ⟨by simp [allInstances, Frame.Box, quality], ?_, ?_, ?_⟩
    · refine ⟨trivial, ?_⟩
      intro _ _ x hx; cases x <;> simp_all [quality]
    · intro x hx; cases x <;> simp_all
      exact ⟨.simpleQuality, trivial, by simp⟩
    · intro z hz; cases z <;> simp_all
      refine ⟨.complexQuality, ⟨trivial, by simp⟩, ?_⟩
      intro b hb; cases b <;> simp_all
  ax82 := by
    intro t q w h
    rcases h.1 with ⟨rfl, rfl⟩
    intro x hx; cases x <;> simp_all
    refine ⟨.complexQuality, ⟨trivial, by simp⟩, ?_⟩
    intro y hy; cases y <;> simp_all

def quale : Thing -> Prop
  | .simpleQuale | .complexQuale => True
  | _ => False

def setLike : Thing -> Prop
  | .dimension | .domain | .superSet => True
  | _ => False

def setExtension : Thing -> Set Thing
  | .dimension => {.simpleQuale}
  | .domain => {.complexQuale}
  | .superSet => {.simpleQuale, .complexQuale}
  | _ => ∅

def associatedWith : Thing -> Thing -> Prop
  | .dimension, .simpleQualityKind
  | .domain, .complexQualityKind => True
  | _, _ => False

def hasValue : Thing -> Thing -> Prop
  | .simpleQuality, .simpleQuale
  | .complexQuality, .complexQuale => True
  | _, _ => False

def distance : Thing -> Thing -> Thing -> Prop
  | .simpleQuale, .simpleQuale, .distanceValue
  | .simpleQuale, .complexQuale, .distanceValue
  | .complexQuale, .simpleQuale, .distanceValue
  | .complexQuale, .complexQuale, .distanceValue => True
  | _, _, _ => False

/- The quality layer has two genuine quality structures and one auxiliary
set. The auxiliary set witnesses proper inclusion and supplies a common set
for distances between quales from different quality structures. -/
def sig : UFOSignature3_12 where
  toUFOSignature3_11 := sig11
  Quale := fun x _ => quale x
  Set_ := fun x _ => setLike x
  SetExtension := fun x _ => setExtension x
  QualityDomain := fun x _ => x = .domain
  QualityDimension := fun x _ => x = .dimension
  AssociatedWith := fun x t _ => associatedWith x t
  IntrinsicMomentType := fun t _ =>
    t = .simpleQualityKind ∨ t = .complexQualityKind
  HasValue := fun x q _ => hasValue x q
  TupleProjection := fun {_} _ _ _ => .simpleQuale
  Distance := fun x y r _ => distance x y r
  DistanceZero := fun r _ => r = .distanceValue
  DistanceSum := fun r₀ r₁ s _ =>
    r₀ = .distanceValue ∧ r₁ = .distanceValue ∧ s = .distanceValue
  DistanceGreaterEq := fun s r _ =>
    s = .distanceValue ∧ r = .distanceValue

attribute [simp] quale setLike setExtension associatedWith hasValue distance sig

@[simp] theorem qualityStructure_iff (x : Thing) (w : World) :
    QualityStructure sig x w ↔ x = .dimension ∨ x = .domain := by
  constructor
  · rintro ⟨t, ht, _⟩
    cases x <;> cases t <;> simp_all [associatedWith]
  · rintro (rfl | rfl)
    · refine ⟨.simpleQualityKind, ⟨?_, trivial⟩, ?_⟩
      · exact Or.inl rfl
      · intro y hy; cases y <;> simp_all [associatedWith]
    · refine ⟨.complexQualityKind, ⟨?_, trivial⟩, ?_⟩
      · exact Or.inr rfl
      · intro y hy; cases y <;> simp_all [associatedWith]

@[simp] theorem simpleQuality_iff (x : Thing) (w : World) :
    SimpleQuality sig x w ↔ x = .simpleQuality := by
  unfold SimpleQuality
  change (Quality sig3 x w ∧ ¬ ∃ y, inheresIn y x) ↔ _
  rw [quality_iff]
  cases x <;> simp [quality, inheresIn]
  exact ⟨.simpleQuality, trivial⟩

@[simp] theorem complexQuality_iff (x : Thing) (w : World) :
    ComplexQuality sig x w ↔ x = .complexQuality := by
  unfold ComplexQuality
  change (Quality sig3 x w ∧ ¬ SimpleQuality sig x w) ↔ _
  rw [quality_iff, simpleQuality_iff]
  cases x <;> simp [quality]

@[simp] theorem simpleQualityType_iff (t : Thing) (w : World) :
    SimpleQualityType sig t w ↔ t = .simpleQualityKind := by
  unfold SimpleQualityType
  change ((t = .simpleQualityKind ∨ t = .complexQualityKind) ∧
    ∀ x, inst x t -> SimpleQuality sig x w) ↔ _
  constructor
  · intro h
    rcases h.1 with rfl | rfl
    · rfl
    · have hs := h.2 .complexQuality trivial
      have heq := (simpleQuality_iff .complexQuality w).1 hs
      cases heq
  · intro ht; subst t
    constructor
    · exact Or.inl rfl
    · intro x hx; cases x <;> simp_all
      exact (simpleQuality_iff .simpleQuality w).2 rfl

@[simp] theorem complexQualityType_iff (t : Thing) (w : World) :
    ComplexQualityType sig t w ↔ t = .complexQualityKind := by
  unfold ComplexQualityType
  change ((t = .simpleQualityKind ∨ t = .complexQualityKind) ∧
    ∀ x, inst x t -> ComplexQuality sig x w) ↔ _
  constructor
  · intro h
    rcases h.1 with rfl | rfl
    · have hc := h.2 .simpleQuality trivial
      have heq := (complexQuality_iff .simpleQuality w).1 hc
      cases heq
    · rfl
  · intro ht; subst t
    constructor
    · exact Or.inr rfl
    · intro x hx; cases x <;> simp_all
      exact (complexQuality_iff .complexQuality w).2 rfl

private theorem associated_cases {s t : Thing} {w : World}
    (h : sig.AssociatedWith s t w) :
    (s = .dimension ∧ t = .simpleQualityKind) ∨
    (s = .domain ∧ t = .complexQualityKind) := by
  cases s <;> cases t <;> simp_all [associatedWith]

private theorem inheres_in_complex {x : Thing} {w : World}
    (h : sig.InheresIn x .complexQuality w) : x = .simpleQuality := by
  cases x <;> simp_all [inheresIn]

private theorem distance_result {x y r : Thing} {w : World}
    (h : sig.Distance x y r w) : r = .distanceValue := by
  cases r <;> simp_all [distance]

private theorem distance_endpoints {x y r : Thing} {w : World}
    (h : sig.Distance x y r w) :
    (x = .simpleQuale ∨ x = .complexQuale) ∧
    (y = .simpleQuale ∨ y = .complexQuale) := by
  cases x <;> cases y <;> simp_all [distance]

set_option maxHeartbeats 200000 in
instance axioms : UFOAxioms3_12 sig where
  toUFOAxioms3_11 := axioms11
  ax83 := by intro x w h; cases x <;> simp_all [quale, isType, endurant, perdurant]
  ax84 := by intro x w h; cases x <;> simp_all [setLike, isType, endurant, perdurant]
  ax85 := by intro w h; rcases h with ⟨x, hx⟩; cases x <;> simp_all [quale, setLike]
  ax86 := by
    intro x w h
    rcases (qualityStructure_iff x w).1 h with rfl | rfl
    · exact ⟨trivial, ⟨Thing.simpleQuale, Set.mem_singleton Thing.simpleQuale⟩⟩
    · exact ⟨trivial, ⟨Thing.complexQuale, Set.mem_singleton Thing.complexQuale⟩⟩
  ax87 := by
    intro x w
    constructor
    · intro hx
      cases x <;> simp_all [quale]
      case simpleQuale =>
        refine ⟨.dimension, ⟨(qualityStructure_iff .dimension w).2 (Or.inl rfl),
          by exact Set.mem_singleton Thing.simpleQuale⟩, ?_⟩
        intro y hy
        rcases (qualityStructure_iff y w).1 hy.1 with hyD | hyO
        · exact hyD
        · subst y
          have heq := Set.mem_singleton_iff.mp hy.2
          cases heq
      case complexQuale =>
        refine ⟨.domain, ⟨(qualityStructure_iff .domain w).2 (Or.inr rfl),
          by exact Set.mem_singleton Thing.complexQuale⟩, ?_⟩
        intro y hy
        rcases (qualityStructure_iff y w).1 hy.1 with hyD | hyO
        · subst y
          have heq := Set.mem_singleton_iff.mp hy.2
          cases heq
        · exact hyO
    · rintro ⟨y, hy, _⟩
      rcases (qualityStructure_iff y w).1 hy.1 with hyD | hyO
      · subst y
        have hx := Set.mem_singleton_iff.mp hy.2
        subst x
        trivial
      · subst y
        have hx := Set.mem_singleton_iff.mp hy.2
        subst x
        trivial
  ax88 := by
    intro x w
    constructor
    · intro hx
      rcases (qualityStructure_iff x w).1 hx with rfl | rfl
      · exact Or.inr rfl
      · exact Or.inl rfl
    · rintro (rfl | rfl)
      · exact (qualityStructure_iff .domain w).2 (Or.inr rfl)
      · exact (qualityStructure_iff .dimension w).2 (Or.inl rfl)
  ax89 := by intro x w h; cases x <;> simp_all
  ax90 := by
    intro s t s' t' w h
    rcases h with ⟨hs, hs', hp⟩
    rcases associated_cases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases associated_cases hs' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact False.elim (hp.2 hp.1)
      · have hbad := hp.1.2.2 () trivial Thing.complexQuality trivial
        cases hbad
    · rcases associated_cases hs' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have hbad := hp.1.2.2 () trivial Thing.simpleQuality trivial
        cases hbad
      · exact False.elim (hp.2 hp.1)
  ax91 := by
    intro t w
    constructor
    · intro ht
      refine ⟨ht, ?_⟩
      rcases ht with rfl | rfl
      · refine ⟨.dimension,
          ⟨(qualityStructure_iff .dimension w).2 (Or.inl rfl), trivial⟩, ?_⟩
        intro x hx; exact (associated_cases hx.2).elim (fun h => h.1) (fun h => by cases h.2)
      · refine ⟨.domain,
          ⟨(qualityStructure_iff .domain w).2 (Or.inr rfl), trivial⟩, ?_⟩
        intro x hx; exact (associated_cases hx.2).elim (fun h => by cases h.2) (fun h => h.1)
    · intro h; exact h.1
  ax92 := by
    intro x y w h
    cases x <;> cases y <;> simp only [sig, hasValue] at h
    · exact ⟨(quality_iff .simpleQuality w).2 trivial, trivial⟩
    · exact ⟨(quality_iff .complexQuality w).2 trivial, trivial⟩
  ax93 := by
    intro x w hx
    have hxq : quality x := (quality_iff x w).1 hx
    cases x <;> simp_all [quality]
    · refine ⟨.simpleQuale, trivial, ?_⟩
      intro y hy; cases y <;> simp_all
    · refine ⟨.complexQuale, trivial, ?_⟩
      intro y hy; cases y <;> simp_all
  ax94 := by
    intro x y w h
    cases x <;> cases y <;> simp only [sig, hasValue] at h
    · refine ⟨Thing.simpleQualityKind, Thing.dimension, trivial, trivial, ?_⟩
      exact Set.mem_singleton Thing.simpleQuale
    · refine ⟨Thing.complexQualityKind, Thing.domain, trivial, trivial, ?_⟩
      exact Set.mem_singleton Thing.complexQuale
  ax95 := by
    intro x y w h
    rcases associated_cases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · constructor
      · intro _; exact (simpleQualityType_iff .simpleQualityKind w).2 rfl
      · intro _; rfl
    · constructor
      · intro h; cases h
      · intro h; cases (simpleQualityType_iff .complexQualityKind w).1 h
  ax96 := by
    intro x y w h
    rcases associated_cases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · constructor
      · intro h; cases h
      · intro h; cases (complexQualityType_iff .simpleQualityKind w).1 h
    · constructor
      · intro _; exact (complexQualityType_iff .complexQualityKind w).2 rfl
      · intro _; rfl
  ax97 := by
    intro x y z Y Z w h
    have hx := (complexQuality_iff x w).1 h.1
    subst x
    exact (inheres_in_complex h.2.2.2.1).trans
      (inheres_in_complex h.2.2.2.2.1).symm
  ax98 := by
    intro x w hx y hy
    have hx' := (complexQuality_iff x w).1 hx
    subst x
    exact (simpleQuality_iff y w).2 (inheres_in_complex hy)
  ax99 := by
    intro x t w h
    rcases h with ⟨hx, ha⟩
    subst x
    rcases associated_cases ha with hbad | ⟨_, ht⟩
    · cases hbad.1
    subst t
    refine ⟨1, fun _ => .dimension, fun _ => .simpleQualityKind, ?_, ?_, ?_⟩
    · intro p hp i
      exact Set.mem_singleton Thing.simpleQuale
    · intro i; exact ⟨trivial, ⟨rfl, rfl⟩⟩
    · intro u hu
      exact ⟨0, hu.2⟩
  ax100 := by
    intro x y r w h
    rcases distance_endpoints h with ⟨hx, hy⟩
    refine ⟨?_, ?_, .superSet, ?_, ?_⟩
    · rcases hx with rfl | rfl <;> trivial
    · rcases hy with rfl | rfl <;> trivial
    · rcases hx with rfl | rfl
      · exact Set.mem_insert Thing.simpleQuale {Thing.complexQuale}
      · exact Set.mem_insert_of_mem Thing.simpleQuale
          (Set.mem_singleton Thing.complexQuale)
    · rcases hy with rfl | rfl
      · exact Set.mem_insert Thing.simpleQuale {Thing.complexQuale}
      · exact Set.mem_insert_of_mem Thing.simpleQuale
          (Set.mem_singleton Thing.complexQuale)
  ax101 := by
    intro x y w h
    have hx : x = .simpleQuale ∨ x = .complexQuale := by
      cases x <;> simp_all [quale]
    have hy : y = .simpleQuale ∨ y = .complexQuale := by
      cases y <;> simp_all [quale]
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    all_goals
      refine ⟨.distanceValue, trivial, ?_⟩
      intro r hr
      exact distance_result hr
  axDistanceIdentity := by
    intro x y r w h
    exact distance_result h.2
  axDistanceSymmetry := by
    intro x y r w h
    have hr := distance_result h
    rcases distance_endpoints h with ⟨hx, hy⟩
    subst r
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> trivial
  axDistanceTriangle := by
    intro x y z r₀ r₁ r₂ s w h
    rcases h with ⟨_, _, hxz, hsum⟩
    exact ⟨hsum.2.2, distance_result hxz⟩

/- Every primitive relation introduced in §3.12, and every named derived
predicate in that section, has an inhabitant in this single cumulative model.
The function-valued set-extension and tuple-projection fields are exercised by
membership, proper inclusion, and product-subset witnesses. -/
theorem predicates_nonempty :
    (∃ x w, sig.Quale x w) ∧
    (∃ x w, sig.Set_ x w) ∧
    (∃ x w, sig.QualityDomain x w) ∧
    (∃ x w, sig.QualityDimension x w) ∧
    (∃ x t w, sig.AssociatedWith x t w) ∧
    (∃ t w, sig.IntrinsicMomentType t w) ∧
    (∃ x q w, sig.HasValue x q w) ∧
    (∃ x y r w, sig.Distance x y r w) ∧
    (∃ r w, sig.DistanceZero r w) ∧
    (∃ r₀ r₁ s w, sig.DistanceSum r₀ r₁ s w) ∧
    (∃ s r w, sig.DistanceGreaterEq s r w) ∧
    (∃ x s w, MemberOf sig x s w) ∧
    (∃ s t w, SubsetOf sig s t w) ∧
    (∃ s t w, ProperSubsetOf sig s t w) ∧
    (∃ s w, NonEmptySet sig s w) ∧
    (∃ (n : Nat) (x : Thing) (ys : Fin n -> Thing) (w : World),
      ProductSubsetOf sig x ys w) ∧
    (∃ x w, QualityStructure sig x w) ∧
    (∃ x w, SimpleQuality sig x w) ∧
    (∃ x w, ComplexQuality sig x w) ∧
    (∃ t w, SimpleQualityType sig t w) ∧
    (∃ t w, ComplexQualityType sig t w) := by
  refine ⟨⟨.simpleQuale, (), trivial⟩,
    ⟨.dimension, (), trivial⟩,
    ⟨.domain, (), rfl⟩,
    ⟨.dimension, (), rfl⟩,
    ⟨.dimension, .simpleQualityKind, (), trivial⟩,
    ⟨.simpleQualityKind, (), Or.inl rfl⟩,
    ⟨.simpleQuality, .simpleQuale, (), trivial⟩,
    ⟨.simpleQuale, .complexQuale, .distanceValue, (), trivial⟩,
    ⟨.distanceValue, (), rfl⟩,
    ⟨.distanceValue, .distanceValue, .distanceValue, (), rfl, rfl, rfl⟩,
    ⟨.distanceValue, .distanceValue, (), rfl, rfl⟩,
    ⟨.simpleQuale, .dimension, (), Set.mem_singleton Thing.simpleQuale⟩,
    ⟨.dimension, .superSet, (), by
      intro z hz
      have hz' := (Set.mem_singleton_iff.mp hz)
      subst z
      exact Set.mem_insert Thing.simpleQuale {Thing.complexQuale}⟩,
    ⟨.dimension, .superSet, (), by
      constructor
      · intro z hz
        have hz' := Set.mem_singleton_iff.mp hz
        subst z
        exact Set.mem_insert Thing.simpleQuale {Thing.complexQuale}
      · intro h
        have hc : Thing.complexQuale ∈ setExtension .superSet :=
          Set.mem_insert_of_mem Thing.simpleQuale (Set.mem_singleton Thing.complexQuale)
        have := h hc
        have heq := Set.mem_singleton_iff.mp this
        cases heq⟩,
    ⟨.dimension, (), ⟨Thing.simpleQuale, Set.mem_singleton Thing.simpleQuale⟩⟩,
    ⟨1, .domain, fun _ => .dimension, (), by
      intro p hp i
      exact Set.mem_singleton Thing.simpleQuale⟩,
    ⟨.dimension, (), (qualityStructure_iff .dimension ()).2 (Or.inl rfl)⟩,
    ⟨.simpleQuality, (), (simpleQuality_iff .simpleQuality ()).2 rfl⟩,
    ⟨.complexQuality, (), (complexQuality_iff .complexQuality ()).2 rfl⟩,
    ⟨.simpleQualityKind, (), (simpleQualityType_iff .simpleQualityKind ()).2 rfl⟩,
    ⟨.complexQualityKind, (), (complexQualityType_iff .complexQualityKind ()).2 rfl⟩⟩

end AntiVacuity.Section3_12
