import LeanUfo.UFO.Core.Section3_11
import LeanUfo.UFO.FormalAnalysis.AntiVacuity.AntiVacuity3_2

/-!
# Characterization anti-vacuity analysis through section 3.11

This model extends the two-world taxonomy interpretation from
`AntiVacuity3_2`. Its three endurants are divided into two modes (`i1`, `j1`)
and one object (`i2`). Consequently, `role` is a mode type and `phase` is an
object type: their only instances occur at `actual`.

The characterization fact relates `phase` and `role` at `actual`. Their
instances are `i2` and `i1`, respectively, and the inherence table makes `i1`
inhere in `i2`. Thus both coverage directions in (a81), including uniqueness
of the bearer, are exercised by the witness.
-/

namespace AntiVacuity.Section3_11

open AntiVacuity.Section3_2

def substantial : Thing -> Prop
  | .i2 => True
  | _ => False

def moment : Thing -> Prop
  | .i1 | .j1 => True
  | _ => False

def sig3 : UFOSignature3_3 where
  toUFOSignature3_2 := AntiVacuity.Section3_2.sig
  Substantial := fun x _ => substantial x
  Moment := fun x _ => moment x
  Object := fun x _ => substantial x
  Collective := fun _ _ => False
  Quantity := fun _ _ => False
  Relator := fun _ _ => False
  IntrinsicMoment := fun x _ => moment x
  Mode := fun x _ => moment x
  QualityKind := fun _ _ => False

attribute [simp] substantial moment sig3

theorem ax34_sig : ax_a34 sig3 := by
  intro x w; cases x <;> cases w <;> simp [AntiVacuity.Section3_2.endurant]
theorem ax35_sig : ax_a35 sig3 := by
  intro w h; rcases h with ⟨x, h⟩; cases x <;> simp_all
theorem ax36_sig : ax_a36 sig3 := by intro x w; cases x <;> cases w <;> simp
theorem ax37_sig : ax_a37 sig3 := by intro w; cases w <;> simp
theorem ax38_sig : ax_a38 sig3 := by intro w; cases w <;> simp
theorem ax39_sig : ax_a39 sig3 := by intro w; cases w <;> simp
theorem ax40_sig : ax_a40 sig3 := by intro x w; cases x <;> cases w <;> simp
theorem ax41_sig : ax_a41 sig3 := by intro w; cases w <;> simp
theorem ax42_sig : ax_a42 sig3 := by
  intro x w; cases x <;> cases w <;> simp [Quality]
theorem ax43_sig : ax_a43 sig3 := by intro w; cases w <;> simp [Quality]

instance axioms3 : UFOAxioms3_3 sig3 where
  toUFOAxioms3_2 := by
    change UFOAxioms3_2 AntiVacuity.Section3_2.sig
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

/- Type-level predicates are interpreted by the right-hand sides of (a44).
This keeps the classification tied to the instance profiles rather than to a
second hand-written table. -/
def allInstances (P : Thing -> World -> Prop) (t : Thing) (w : World) : Prop :=
  isType t ∧ Frame.Box (F := frame)
    (fun w' => ∀ x, inst x t w' -> P x w') w

def sig4 : UFOSignature3_4 where
  toUFOSignature3_3 := sig3
  SubstantialType := allInstances (fun x _ => substantial x)
  MomentType := allInstances (fun x _ => moment x)
  ObjectType := allInstances (fun x _ => substantial x)
  CollectiveType := allInstances (fun _ _ => False)
  QuantityType := allInstances (fun _ _ => False)
  RelatorType := allInstances (fun _ _ => False)
  ModeType := allInstances (fun x _ => moment x)
  QualityType := allInstances (fun _ _ => False)
  ObjectKind := fun t w => allInstances (fun x _ => substantial x) t w ∧ kind t
  CollectiveKind := fun t w => allInstances (fun _ _ => False) t w ∧ kind t
  QuantityKind := fun t w => allInstances (fun _ _ => False) t w ∧ kind t
  RelatorKind := fun t w => allInstances (fun _ _ => False) t w ∧ kind t
  ModeKind := fun t w => allInstances (fun x _ => moment x) t w ∧ kind t

attribute [simp] allInstances sig4

@[simp] theorem quality_false (x : Thing) (w : World) :
    ¬ Quality sig3 x w := by
  cases x <;> cases w <;> simp [Quality]

private theorem no_all_false (t : Thing) (w : World) :
    ¬ allInstances (fun _ _ => False) t w := by
  rintro ⟨ht, hbox⟩
  rcases (ax1_sig t w).1 ht with ⟨v, hv, x, hx⟩
  exact hbox v hv x hx

theorem ax44_sig : ax_a44 sig4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t w; cases t <;> cases w <;>
      simp [allInstances, Frame.Box, AntiVacuity.Section3_2.endurantType]
    all_goals first
      | exact ⟨.actual, .abstractIndividual, trivial, by simp⟩
      | exact ⟨.actual, .perdurantIndividual, trivial, by simp⟩
      | (intro v x hx; cases v <;> cases x <;> simp_all)
  · intro t w; cases t <;> cases w <;> simp [allInstances, Frame.Box]
    all_goals first
      | exact ⟨.actual, .i1, trivial, by simp⟩
      | exact ⟨.actual, .i2, trivial, by simp⟩
      | exact ⟨.actual, .abstractIndividual, trivial, by simp⟩
      | (intro v x hx; cases v <;> cases x <;> simp_all)
  · intro t w; rfl
  · intro t w; rfl
  · intro t w; rfl
  · intro t w; rfl
  · intro t w; rfl
  · intro t w; rfl
  · intro t w; rfl
  · intro t w; constructor
    · intro h; exact False.elim (no_all_false t w h)
    · rintro ⟨ht, hbox⟩
      rcases (ax1_sig t w).1 ht with ⟨v, hv, x, hx⟩
      exact False.elim (quality_false x v (hbox v hv x hx))

theorem ax45_sig : ax_a45 sig4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro t w
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · constructor
    · intro h; cases h
    · intro h; exact False.elim (no_all_false t w h.1)

theorem ax46_sig : ax_a46 sig4 := by
  intro x w hx
  change endurant x at hx
  cases x <;> simp [endurant] at hx
  · refine ⟨.actual, trivial, .k1, ?_, trivial⟩
    right; right; right; right; left; refine ⟨⟨trivial, ?_⟩, trivial⟩
    intro v _ z hz; cases v <;> cases z <;> simp_all [moment]
  · refine ⟨.actual, trivial, .k1, ?_, trivial⟩
    right; right; right; right; left; refine ⟨⟨trivial, ?_⟩, trivial⟩
    intro v _ z hz; cases v <;> cases z <;> simp_all [moment]
  · refine ⟨.actual, trivial, .k2, ?_, trivial⟩
    left; refine ⟨⟨trivial, ?_⟩, trivial⟩
    intro v _ z hz; cases v <;> cases z <;> simp_all [substantial]

instance axioms4 : UFOAxioms3_4 sig4 where
  toUFOAxioms3_3 := axioms3
  ax44 := ax44_sig
  ax45 := ax45_sig
  ax46 := ax46_sig

/- The intermediate sections use conservative interpretations. Identity
parthood supplies the full extensional mereology; composition and constitution
are interpreted by the formulas that define them. -/
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

def gfd (x' y' : Thing) (w : World) : Prop :=
  ∀ x, (inst x x' w ∧ False) ->
    ∃ y, y ≠ x ∧ inst y y' w ∧ False

def ifd (x x' y y' : Thing) (w : World) : Prop :=
  gfd x' y' w ∧ inst x x' w ∧ inst y y' w ∧ (False -> False)

def sig6 : UFOSignature3_6 where
  toUFOSignature3_5 := sig5
  FunctionsAs := fun _ _ _ => False
  GenericFunctionalDependence := gfd
  IndividualFunctionalDependence := ifd
  ComponentOf := fun x x' y y' w => False ∧ ifd x x' y y' w

attribute [simp] sig6

instance axioms6 : UFOAxioms3_6 sig6 where
  toUFOAxioms3_5 := by change UFOAxioms3_5 sig5; exact axioms5
  ax53 := by intro x y w; rfl
  ax54 := by intro x x' y y' w; rfl
  ax55 := by intro x x' y y' w; rfl

def gcd (x' y' : Thing) (w : World) : Prop :=
  ∀ x, inst x x' w -> ∃ y, inst y y' w ∧ False

def constitution (x x' y y' : Thing) (w : World) : Prop :=
  inst x x' w ∧ inst y y' w ∧ gcd x' y' w ∧ False

def sig7 : UFOSignature3_7 where
  toUFOSignature3_6 := sig6
  Ex := fun _ _ => True
  ConstitutedBy := fun _ _ _ => False
  GenericConstitutionalDependence := gcd
  Constitution := constitution

attribute [simp] sig7

instance axioms7 : UFOAxioms3_7 sig7 where
  toUFOAxioms3_6 := by change UFOAxioms3_6 sig6; exact axioms6
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
  toUFOAxioms3_7 := by change UFOAxioms3_7 sig7; exact axioms7
  ax62 := by
    intro x w _; trivial
  ax63 := by intro x y w; rfl
  ax64 := by intro x y w; rfl

def inheresIn : Thing -> Thing -> Prop
  | .i1, .i2 | .j1, .i2 => True
  | _, _ => False

def sig9 : UFOSignature3_9 where
  toUFOSignature3_8 := sig8
  InheresIn := fun (x y : Thing) (_ : World) => inheresIn x y

attribute [simp] inheresIn sig9

private theorem i2_terminal (w : World) : ∀ y, ¬ sig9.InheresIn .i2 y w := by
  intro y; cases y <;> simp [inheresIn]

set_option maxHeartbeats 5000000 in
instance axioms9 : UFOAxioms3_9 sig9 where
  toUFOAxioms3_8 := by change UFOAxioms3_8 sig8; exact axioms8
  ax65 := by intro x y w h v _ _; trivial
  ax66 := by
    intro x y w h; cases x <;> cases y <;> simp_all [inheresIn, moment, isType]
  ax67 := by
    intro x y z w h; cases x <;> cases y <;> cases z <;> simp_all [inheresIn]
  ax68 := by
    intro m w hm
    cases m <;> simp [moment] at hm
    · refine ⟨.i2, ⟨by simp [moment], .direct (by simp [inheresIn])⟩, ?_⟩
      intro b hb
      exact momentOf_eq_of_unique_direct_bearer (Sig := sig9)
        (b := .i2) (x := b)
        (by intro y h; cases y <;> simp_all [inheresIn])
        (i2_terminal w) hb.2
    · refine ⟨.i2, ⟨by simp [moment], .direct (by simp [inheresIn])⟩, ?_⟩
      intro b hb
      exact momentOf_eq_of_unique_direct_bearer (Sig := sig9)
        (b := .i2) (x := b)
        (by intro y h; cases y <;> simp_all [inheresIn])
        (i2_terminal w) hb.2

def sig10 : UFOSignature3_10 where
  toUFOSignature3_9 := sig9
  ExternallyDependent := fun x y w =>
    sig9.ExistentialDependence x y w ∧
      ∀ z, sig9.InheresIn x z w -> sig9.ExistentialIndependence y z w
  ExternallyDependentMode := fun x w =>
    sig9.Mode x w ∧ ∃ y, sig9.ExistentialDependence x y w ∧
      ∀ z, sig9.InheresIn x z w -> sig9.ExistentialIndependence y z w
  FoundedBy := fun (_ _ : Thing) (_ : World) => False
  QuaIndividualOf := fun _ _ _ => False
  QuaIndividual := fun _ _ => False
  Mediates := fun _ _ _ => False

attribute [simp] sig10

/- With total existence, external dependence is empty: existential
independence is empty, while each mode has an inherence bearer. The remaining
relator-specific predicates can therefore also be empty. -/
private theorem no_externally_dependent_mode (x : Thing) (w : World) :
    ¬ sig10.ExternallyDependentMode x w := by
  intro h
  change moment x ∧ ∃ y, _ at h
  rcases h.2 with ⟨y, _, hy⟩
  cases x <;> simp [moment] at h
  · have hInd := hy .i2 (by simp [inheresIn])
    exact hInd.1 (by intro v _ _; trivial)
  · have hInd := hy .i2 (by simp [inheresIn])
    exact hInd.1 (by intro v _ _; trivial)

instance axioms10 : UFOAxioms3_10 sig10 where
  toUFOAxioms3_9 := by change UFOAxioms3_9 sig9; exact axioms9
  ax69 := by intro x y w; rfl
  ax70 := by intro x w; rfl
  ax71 := by intro x y w h; cases h
  ax72 := by intro x w h; exact False.elim (no_externally_dependent_mode x w h)
  ax73 := by
    intro x y w; constructor
    · intro h; cases h
    · intro h
      have hx := (h x).1 rfl
      exact False.elim (no_externally_dependent_mode x w hx.1)
  ax74 := by intro x w; simp
  ax75 := by intro x w h; cases h
  ax76 := by intro x y z w h; exact False.elim h.1
  ax77 := by intro x w h; change False at h; cases h
  ax78 := by
    intro x y w h
    have hFalse := h.1
    change False at hFalse
    cases hFalse
  ax79 := by
    intro x w; constructor
    · intro h; change False at h; cases h
    · rintro ⟨⟨y, hy⟩, _⟩; cases hy
  ax80 := by
    intro x y w; constructor
    · intro h; cases h
    · intro h
      have hFalse := h.1
      change False at hFalse
      cases hFalse
  axQuaIndividualOfEndurant := by intro x y w h; cases h

def sig : UFOSignature3_11 where
  toUFOSignature3_10 := sig10
  Characterization := fun (t m : Thing) (w : World) =>
    t = Thing.phase ∧ m = Thing.role ∧ w = World.actual

attribute [simp] sig

theorem ax81_sig : ax_a81 sig := by
  intro t m w h
  rcases h with ⟨rfl, rfl, rfl⟩
  refine ⟨by trivial, ?_, ?_, ?_⟩
  · refine ⟨trivial, ?_⟩
    intro v _ x hx
    cases v <;> cases x <;> simp_all [moment]
  · intro x hx
    cases x <;> simp_all
    exact ⟨.i1, trivial, by simp⟩
  · intro z hz
    cases z <;> simp_all
    refine ⟨.i2, ⟨trivial, by simp⟩, ?_⟩
    intro bearer hb; cases bearer <;> simp_all

theorem ax82_sig : ax_a82 sig := by
  intro t q w h
  rcases h.1 with ⟨rfl, rfl, rfl⟩
  exact False.elim (no_all_false .role .actual h.2)

instance axioms : UFOAxioms3_11 sig where
  toUFOAxioms3_10 := by change UFOAxioms3_10 sig10; exact axioms10
  ax81 := ax81_sig
  ax82 := ax82_sig

/-- Characterization has a concrete inhabitant in a model of the complete
cumulative package through section 3.11. -/
theorem predicates_nonempty : ∃ t m w, sig.Characterization t m w :=
  ⟨Thing.phase, Thing.role, World.actual, rfl, rfl, rfl⟩

end AntiVacuity.Section3_11
