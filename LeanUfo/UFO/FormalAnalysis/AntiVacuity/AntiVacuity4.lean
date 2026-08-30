import LeanUfo.UFO.Core.Section4
import LeanUfo.UFO.FormalAnalysis.AntiVacuity.AntiVacuity3_13

/-!
# Type-structure anti-vacuity analysis through section 4

The four section 4 predicates are constrained by biconditionals, so their
interpretations below are exactly the corresponding right-hand sides of
(a105)-(a108). Anti-vacuity still requires suitable inhabitants of those
right-hand sides.

The cumulative carrier distinguishes the simple- and complex-quality kinds.
They have disjoint instance extensions, and the simple-quality kind is covered
by itself together with the complex-quality kind. This supplies witnesses for
disjointness, complete coverage, and partitioning.

Categorization needs one additional level in the instantiation hierarchy. The
`metaKind` introduced in `AntiVacuity3_12` has `simpleQualityKind` as its only
instance. Since `simpleQualityKind` specializes itself, `metaKind` categorizes
`simpleQualityKind`. This witness exercises the higher-order shape of (a108):
an instance of the categorizing type is itself a type.
-/

namespace AntiVacuity.Section4

open AntiVacuity.Section3_12

private abbrev base := AntiVacuity.Section3_13.sig

def isDisjointWith (t t' : Thing) (w : World) : Prop :=
  base.Type_ t w ∧ base.Type_ t' w ∧
    ¬ ∃ x, base.Inst x t w ∧ base.Inst x t' w

def isCompletelyCoveredBy (t t' t'' : Thing) (w : World) : Prop :=
  ∀ x, base.Inst x t w -> base.Inst x t' w ∨ base.Inst x t'' w

def isPartitionedInto (t t' t'' : Thing) (w : World) : Prop :=
  isCompletelyCoveredBy t t' t'' w ∧ isDisjointWith t' t'' w

def categorizes (t₁ t₂ : Thing) (w : World) : Prop :=
  base.Type_ t₁ w ∧ ∀ t₃, base.Inst t₃ t₁ w -> base.Sub t₃ t₂ w

def sig : UFOSignature4 where
  toUFOSignature3_13 := base
  IsDisjointWith := isDisjointWith
  IsCompletelyCoveredBy := isCompletelyCoveredBy
  IsPartitionedInto := isPartitionedInto
  Categorizes := categorizes

attribute [simp] base isDisjointWith isCompletelyCoveredBy isPartitionedInto
  categorizes sig

instance axioms : UFOAxioms4 sig where
  toUFOAxioms3_13 := AntiVacuity.Section3_13.axioms
  ax105 := by intro t t' w; rfl
  ax106 := by intro t t' t'' w; rfl
  ax107 := by intro t t' t'' w; rfl
  ax108 := by intro t₁ t₂ w; rfl

private theorem quality_kinds_disjoint :
    sig.IsDisjointWith .simpleQualityKind .complexQualityKind () := by
  refine ⟨trivial, trivial, ?_⟩
  rintro ⟨x, hx, hx'⟩
  cases x <;> simp_all [inst]

private theorem simple_kind_covered :
    sig.IsCompletelyCoveredBy .simpleQualityKind
      .simpleQualityKind .complexQualityKind () := by
  intro x hx
  exact Or.inl hx

private theorem metakind_categorizes_simple_kind :
    sig.Categorizes .metaKind .simpleQualityKind () := by
  refine ⟨trivial, ?_⟩
  intro t ht
  cases t <;> simp_all [inst, isType, Frame.Box]

/- All four section 4 relations are inhabited in this one cumulative model.
The partition witness reuses the same coverage and disjointness facts proved
above, making its two required components explicit. -/
theorem predicates_nonempty :
    (∃ t t' w, sig.IsDisjointWith t t' w) ∧
    (∃ t t' t'' w, sig.IsCompletelyCoveredBy t t' t'' w) ∧
    (∃ t t' t'' w, sig.IsPartitionedInto t t' t'' w) ∧
    (∃ t₁ t₂ w, sig.Categorizes t₁ t₂ w) := by
  exact ⟨⟨.simpleQualityKind, .complexQualityKind, (), quality_kinds_disjoint⟩,
    ⟨.simpleQualityKind, .simpleQualityKind, .complexQualityKind, (),
      simple_kind_covered⟩,
    ⟨.simpleQualityKind, .simpleQualityKind, .complexQualityKind, (),
      simple_kind_covered, quality_kinds_disjoint⟩,
    ⟨.metaKind, .simpleQualityKind, (), metakind_categorizes_simple_kind⟩⟩

end AntiVacuity.Section4
