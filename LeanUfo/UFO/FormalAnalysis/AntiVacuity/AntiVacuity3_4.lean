import LeanUfo.UFO.FormalAnalysis.AntiVacuity.AntiVacuity3_3
import LeanUfo.UFO.Core.Section3_4

/-!
# Taxonomy anti-vacuity analysis through section 3.4

Section 3.4 adds the endurant type and kind taxonomy to the common interpretation.
-/

namespace AntiVacuity.Taxonomy

/-- A type belongs to a leaf exactly when all its instances necessarily belong
to that leaf. This mirrors the characterizations in axiom (a44). -/
def typedBy (P : Thing -> Unit -> Prop) (t : Thing) (w : Unit) : Prop :=
  sig3.Type_ t w ∧ Frame.Box (F := frame)
    (fun w' => ∀ x, sig3.Inst x t w' -> P x w') w

/-- Interpretation of the section 3.4 signature.

The upper type predicates use `typedBy` directly. Each specific kind is its
corresponding specific type conjoined with the section 3.2 `Kind` predicate.
`QualityKind` remains the primitive field inherited from section 3.3, while
`QualityType` is characterized from the derived individual predicate. -/
def sig : UFOSignature3_4 where
  toUFOSignature3_3 := sig3
  SubstantialType := typedBy sig3.Substantial
  MomentType := typedBy sig3.Moment
  ObjectType := typedBy sig3.Object
  CollectiveType := typedBy sig3.Collective
  QuantityType := typedBy sig3.Quantity
  RelatorType := typedBy sig3.Relator
  ModeType := typedBy sig3.Mode
  QualityType := typedBy (Quality sig3)
  ObjectKind := fun t w => typedBy sig3.Object t w ∧ sig3.Kind t w
  CollectiveKind := fun t w => typedBy sig3.Collective t w ∧ sig3.Kind t w
  QuantityKind := fun t w => typedBy sig3.Quantity t w ∧ sig3.Kind t w
  RelatorKind := fun t w => typedBy sig3.Relator t w ∧ sig3.Kind t w
  ModeKind := fun t w => typedBy sig3.Mode t w ∧ sig3.Kind t w

attribute [simp] typedBy sig

/-- A leaf kind classifies its matching leaf individual at every accessible
world. This lemma supplies the repeated boxed clause in (a44)-(a46). -/
private theorem typedBy_self (leaf : Leaf) :
    typedBy (fun x _ => x = .individual leaf) (.kind leaf) () := by
  constructor
  · simp
  · intro v _hv x hx
    cases v
    cases x <;> simp_all [inst]

private theorem endurantType_characterization (t : Thing) (w : Unit) :
    typedBy sig3.Endurant t w ↔ sig3.EndurantType t w := by
  constructor
  · rintro ⟨ht, hBox⟩
    rcases type_has_instance ht with ⟨x, hx⟩
    have hxEndurant := hBox w (frame.refl w) x hx
    cases t <;> rename_i tLeaf <;> cases tLeaf <;>
      cases x <;> rename_i xLeaf <;> cases xLeaf <;> simp_all [inst]
  · intro ht
    refine ⟨ax15_sig t w ht, ?_⟩
    intro v _hv x hx
    exact ax_instEndurant_sig t x v ht hx

private theorem perdurantType_characterization (t : Thing) (w : Unit) :
    typedBy sig3.Perdurant t w ↔ sig3.PerdurantType t w := by
  constructor
  · rintro ⟨ht, hBox⟩
    rcases type_has_instance ht with ⟨x, hx⟩
    have hxPerdurant := hBox w (frame.refl w) x hx
    cases t <;> rename_i tLeaf <;> cases tLeaf <;>
      cases x <;> rename_i xLeaf <;> cases xLeaf <;> simp_all [inst]
  · intro ht
    refine ⟨ax16_sig t w ht, ?_⟩
    intro v _hv x hx
    cases t <;> rename_i tLeaf <;> cases tLeaf <;>
      cases x <;> rename_i xLeaf <;> cases xLeaf <;> simp_all [inst]

/-- Axiom (a44): each section 3.4 type predicate is equivalent to being a type
whose instances necessarily lie in the corresponding individual category.
Most clauses hold by definition; the two upper branches are discharged by a
finite partition check. -/
theorem ax44_sig : ax_a44 sig := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t w
    exact (endurantType_characterization t w).symm
  · intro t w
    exact (perdurantType_characterization t w).symm
  all_goals intro t w; rfl

/-- In this interpretation the quality type is exactly the type whose matching
individual is the quality leaf. The forward direction uses the mandatory
instance supplied by section 3.1, preventing empty types from satisfying the
leaf characterization vacuously. -/
private theorem qualityType_iff (t : Thing) (w : Unit) :
    sig.QualityType t w ↔ t = .kind .quality := by
  constructor
  · rintro ⟨ht, hBox⟩
    rcases type_has_instance ht with ⟨x, hx⟩
    have hxQuality : Quality sig3 x w := hBox w (frame.refl w) x hx
    have hxLeaf := (quality_iff x w).1 hxQuality
    cases t <;> cases x <;> simp_all [inst]
  · intro ht
    subst t
    constructor
    · simp
    · intro v _hv x hx
      apply (quality_iff x v).2
      cases x <;> simp_all [inst]

/-- Axiom (a45): each specific kind is its corresponding specific type together
with `Kind`. The quality clause uses `qualityType_iff` because quality is a
derived predicate. -/
theorem ax45_sig : ax_a45 sig := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t w; rfl
  · intro t w; rfl
  · intro t w; rfl
  · intro t w; rfl
  · intro t w; rfl
  · intro t w
    constructor
    · intro hQualityKind
      have ht : t = .kind .quality := hQualityKind
      exact ⟨(qualityType_iff t w).2 ht, by subst t; simp⟩
    · rintro ⟨hQualityType, _hKind⟩
      exact (qualityType_iff t w).1 hQualityType

/-- For each individual leaf, identifies the disjunct of (a46) satisfied by its
matching kind. -/
private theorem specificKind_holds (leaf : Leaf)
    (hEndurant : endurant (.individual leaf)) :
    sig.ObjectKind (.kind leaf) () ∨
    sig.CollectiveKind (.kind leaf) () ∨
    sig.QuantityKind (.kind leaf) () ∨
    sig.RelatorKind (.kind leaf) () ∨
    sig.ModeKind (.kind leaf) () ∨
    sig.QualityKind (.kind leaf) () := by
  cases leaf with
  | object => exact Or.inl ⟨typedBy_self .object, by simp⟩
  | collective => exact Or.inr (Or.inl ⟨typedBy_self .collective, by simp⟩)
  | quantity => exact Or.inr (Or.inr (Or.inl ⟨typedBy_self .quantity, by simp⟩))
  | relator => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨typedBy_self .relator, by simp⟩)))
  | mode => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨typedBy_self .mode, by simp⟩))))
  | quality =>
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      simp
  | abstract => simp_all
  | perdurant => simp_all

/-- Axiom (a46): every endurant possibly instantiates a specific endurant kind.
The witness is its matching kind at the unique world. -/
theorem ax46_sig : ax_a46 sig := by
  intro x w hx
  cases x with
  | kind leaf => simp_all
  | individual leaf =>
      cases w
      exact ⟨(), trivial, .kind leaf, specificKind_holds leaf hx, rfl⟩

/-- The complete section 3.4 package for the simultaneous leaf witness. -/
instance axioms : UFOAxioms3_4 sig where
  toUFOAxioms3_3 := axioms3
  ax44 := ax44_sig
  ax45 := ax45_sig
  ax46 := ax46_sig

/-- All six section 3.3 individual leaves are inhabited in one interpretation
at one world. -/
theorem individual_taxonomy_nonempty :
    sig.Object (.individual .object) () ∧
    sig.Collective (.individual .collective) () ∧
    sig.Quantity (.individual .quantity) () ∧
    sig.Relator (.individual .relator) () ∧
    sig.Mode (.individual .mode) () ∧
    Quality sig.toUFOSignature3_3 (.individual .quality) () := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  exact (quality_iff (.individual .quality) ()).2 rfl

/-- All six section 3.4 type and kind leaves are inhabited simultaneously. The
quality representative witnesses both the derived `QualityType` and the
primitive `QualityKind`. -/
theorem type_taxonomy_nonempty :
    sig.ObjectKind (.kind .object) () ∧
    sig.CollectiveKind (.kind .collective) () ∧
    sig.QuantityKind (.kind .quantity) () ∧
    sig.RelatorKind (.kind .relator) () ∧
    sig.ModeKind (.kind .mode) () ∧
    sig.QualityType (.kind .quality) () ∧
    sig.QualityKind (.kind .quality) () := by
  refine ⟨⟨typedBy_self .object, by simp⟩,
    ⟨typedBy_self .collective, by simp⟩,
    ⟨typedBy_self .quantity, by simp⟩,
    ⟨typedBy_self .relator, by simp⟩,
    ⟨typedBy_self .mode, by simp⟩, ?_, by simp⟩
  constructor
  · simp
  · intro v _hv x hx
    exact (quality_iff x v).2 (by cases x <;> simp_all [inst])

/- This checkpoint lists every field added by `UFOSignature3_4`. Upper type
categories and their six leaves are witnessed together; the five kind fields
added in section 3.4 are accompanied by the inherited `QualityKind`, which
completes the six-way kind taxonomy. -/
theorem predicates_nonempty :
    (∃ t w, sig.SubstantialType t w) ∧
    (∃ t w, sig.MomentType t w) ∧
    (∃ t w, sig.ObjectType t w) ∧
    (∃ t w, sig.CollectiveType t w) ∧
    (∃ t w, sig.QuantityType t w) ∧
    (∃ t w, sig.RelatorType t w) ∧
    (∃ t w, sig.ModeType t w) ∧
    (∃ t w, sig.QualityType t w) ∧
    (∃ t w, sig.ObjectKind t w) ∧
    (∃ t w, sig.CollectiveKind t w) ∧
    (∃ t w, sig.QuantityKind t w) ∧
    (∃ t w, sig.RelatorKind t w) ∧
    (∃ t w, sig.ModeKind t w) ∧
    (∃ t w, sig.QualityKind t w) := by
  refine ⟨⟨.kind .object, (), ?_⟩,
    ⟨.kind .relator, (), ?_⟩,
    ⟨.kind .object, (), typedBy_self .object⟩,
    ⟨.kind .collective, (), typedBy_self .collective⟩,
    ⟨.kind .quantity, (), typedBy_self .quantity⟩,
    ⟨.kind .relator, (), typedBy_self .relator⟩,
    ⟨.kind .mode, (), typedBy_self .mode⟩,
    ⟨.kind .quality, (), (qualityType_iff (.kind .quality) ()).2 rfl⟩,
    ⟨.kind .object, (), ⟨typedBy_self .object, by simp⟩⟩,
    ⟨.kind .collective, (), ⟨typedBy_self .collective, by simp⟩⟩,
    ⟨.kind .quantity, (), ⟨typedBy_self .quantity, by simp⟩⟩,
    ⟨.kind .relator, (), ⟨typedBy_self .relator, by simp⟩⟩,
    ⟨.kind .mode, (), ⟨typedBy_self .mode, by simp⟩⟩,
    ⟨.kind .quality, (), rfl⟩⟩
  · constructor
    · simp
    · intro v _ x hx
      cases x <;> simp_all [inst]
  · constructor
    · simp
    · intro v _ x hx
      cases x <;> simp_all [inst]

end AntiVacuity.Taxonomy
