import LeanUfo.UFO.FormalAnalysis.AntiVacuity.AntiVacuity3_2
import LeanUfo.UFO.Core.Section3_3

/-!
# Taxonomy anti-vacuity analysis through section 3.3

Section 3.3 adds the endurant-individual taxonomy to the common interpretation.
-/

namespace AntiVacuity.Taxonomy

/-- Interpretation of the section 3.3 individual taxonomy.

The six representatives are partitioned as follows:
- object, collective, and quantity are substantial individuals;
- relator, mode, and quality are moments;
- relator is the relator branch of moments;
- mode and quality are the two intrinsic-moment leaves.

The derived `Quality` predicate holds through one unique `QualityKind`. -/
def sig3 : UFOSignature3_3 where
  toUFOSignature3_2 := sig2
  Substantial := fun x _ => ∃ leaf, x = .individual leaf ∧ isSubstantial leaf = true
  Moment := fun x _ => ∃ leaf, x = .individual leaf ∧ isMoment leaf = true
  Object := fun x _ => x = .individual .object
  Collective := fun x _ => x = .individual .collective
  Quantity := fun x _ => x = .individual .quantity
  Relator := fun x _ => x = .individual .relator
  IntrinsicMoment := fun x _ => x = .individual .mode ∨ x = .individual .quality
  Mode := fun x _ => x = .individual .mode
  QualityKind := fun x _ => x = .kind .quality

attribute [simp] sig3

/-- The derived `Quality` predicate denotes exactly the quality representative.

The reverse direction supplies `kind quality` as the unique quality kind. The
forward direction uses the interpretation of `QualityKind` and `Inst` to show
that no other domain element can satisfy the derived definition. -/
theorem quality_iff (x : Thing) (w : Unit) :
    Quality sig3 x w ↔ x = .individual .quality := by
  cases w
  constructor
  · rintro ⟨t, ⟨ht, hInst⟩, _hUnique⟩
    have ht' : t = .kind .quality := by simpa using ht
    subst t
    cases x <;> simp_all
  · intro hx
    subst x
    refine ⟨.kind .quality, ⟨by simp, rfl⟩, ?_⟩
    intro y hy
    simpa using hy.1

attribute [simp] quality_iff

/-- Axiom (a34): the substantial and moment extensions partition all endurant
individuals. -/
theorem ax34_sig : ax_a34 sig3 := by
  intro x w
  cases x with
  | individual leaf => cases leaf <;> cases w <;> simp
  | kind leaf => cases leaf <;> cases w <;> simp

/-- Axiom (a35): the Boolean complement used by `isMoment` makes the two upper
branches disjoint. -/
theorem ax35_sig : ax_a35 sig3 := by
  intro w h
  rcases h with ⟨x, hx⟩
  cases x with
  | individual leaf => cases leaf <;> cases w <;> simp_all
  | kind leaf => cases leaf <;> cases w <;> simp_all

/-- Axioms (a36)-(a39): object, collective, and quantity form a disjoint
partition of substantial individuals. -/
theorem ax36_sig : ax_a36 sig3 := by
  intro x w
  cases x with
  | individual leaf => cases leaf <;> cases w <;> simp
  | kind leaf => cases leaf <;> cases w <;> simp
theorem ax37_sig : ax_a37 sig3 := by intro w; simp
theorem ax38_sig : ax_a38 sig3 := by intro w; simp
theorem ax39_sig : ax_a39 sig3 := by intro w; simp
/-- Axiom (a40): relators and intrinsic moments partition moments. -/
theorem ax40_sig : ax_a40 sig3 := by
  intro x w
  cases x with
  | individual leaf => cases leaf <;> cases w <;> simp
  | kind leaf => cases leaf <;> cases w <;> simp
theorem ax41_sig : ax_a41 sig3 := by intro w; simp
/-- Axiom (a42): modes and derived qualities partition intrinsic moments. The
explicit proof avoids hiding the derived `Quality` definition behind `simp`. -/
theorem ax42_sig : ax_a42 sig3 := by
  intro x w
  constructor
  · rintro (hxMode | hxQuality)
    · exact Or.inl hxMode
    · have hxQuality' : Quality sig3 x w := hxQuality
      exact Or.inr ((quality_iff x w).1 hxQuality')
  · rintro (hxMode | hxQuality)
    · exact Or.inl hxMode
    · apply Or.inr
      exact (quality_iff x w).2 hxQuality
/-- Axiom (a43): the mode and quality representatives are distinct. -/
theorem ax43_sig : ax_a43 sig3 := by
  intro w
  rintro ⟨x, hxMode, hxQuality⟩
  have hxQuality' : Quality sig3 x w := hxQuality
  have hxq := (quality_iff x w).1 hxQuality'
  cases x with
  | individual leaf => cases leaf <;> simp_all
  | kind leaf => simp_all

/-- The complete section 3.3 package extending the common section 3.2 model. -/
instance axioms3 : UFOAxioms3_3 sig3 where
  toUFOAxioms3_2 := axioms2
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

/- Every primitive category introduced in section 3.3 is inhabited in this
single model. The derived `Quality` predicate is included because it completes
the intrinsic-moment partition used by (a42), although it is not a signature
field. -/
theorem section3_3_predicates_nonempty :
    (∃ x w, sig3.Substantial x w) ∧
    (∃ x w, sig3.Moment x w) ∧
    (∃ x w, sig3.Object x w) ∧
    (∃ x w, sig3.Collective x w) ∧
    (∃ x w, sig3.Quantity x w) ∧
    (∃ x w, sig3.Relator x w) ∧
    (∃ x w, sig3.IntrinsicMoment x w) ∧
    (∃ x w, sig3.Mode x w) ∧
    (∃ x w, Quality sig3 x w) ∧
    (∃ t w, sig3.QualityKind t w) := by
  exact ⟨⟨.individual .object, (), ⟨.object, rfl, rfl⟩⟩,
    ⟨.individual .relator, (), ⟨.relator, rfl, rfl⟩⟩,
    ⟨.individual .object, (), rfl⟩,
    ⟨.individual .collective, (), rfl⟩,
    ⟨.individual .quantity, (), rfl⟩,
    ⟨.individual .relator, (), rfl⟩,
    ⟨.individual .mode, (), Or.inl rfl⟩,
    ⟨.individual .mode, (), rfl⟩,
    ⟨.individual .quality, (), (quality_iff (.individual .quality) ()).2 rfl⟩,
    ⟨.kind .quality, (), rfl⟩⟩


end AntiVacuity.Taxonomy
