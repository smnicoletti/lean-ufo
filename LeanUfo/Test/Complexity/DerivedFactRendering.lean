import LeanUfo.UFO.DSL.Compiler

/-!
# Derived proposition text and operation counts

Each fixture checks the exact certificate text and its construction cost.
The general renderer theorem covers all coordinates and field names. These
tests check each signature-selection branch and the direct-field fallback.
String-character processing is outside the unit-cost model.
-/

namespace LeanUfo.Test.Complexity.DerivedFactRendering

open LeanUfo.UFO.DSL

example : renderDerivedFactCosted (.unary "Quality" 7) 2 =
    ⟨"Quality sig.toUFOSignature3_3 (⟨7, by decide⟩ : Fin data.thingCount) (⟨2, by decide⟩ : Fin data.worldCount)", 16⟩ := by
  native_decide

example : renderDerivedFactCosted (.unary "NonEmptySet" 7) 2 =
    ⟨"NonEmptySet sig.toUFOSignature3_12 (⟨7, by decide⟩ : Fin data.thingCount) (⟨2, by decide⟩ : Fin data.worldCount)", 18⟩ := by
  native_decide

example : renderDerivedFactCosted (.unary "QualityStructure" 7) 2 =
    ⟨"QualityStructure sig.toUFOSignature3_12 (⟨7, by decide⟩ : Fin data.thingCount) (⟨2, by decide⟩ : Fin data.worldCount)", 20⟩ := by
  native_decide

example : renderDerivedFactCosted (.unary "SimpleQuality" 7) 2 =
    ⟨"SimpleQuality sig.toUFOSignature3_12 (⟨7, by decide⟩ : Fin data.thingCount) (⟨2, by decide⟩ : Fin data.worldCount)", 22⟩ := by
  native_decide

example : renderDerivedFactCosted (.unary "ComplexQuality" 7) 2 =
    ⟨"ComplexQuality sig.toUFOSignature3_12 (⟨7, by decide⟩ : Fin data.thingCount) (⟨2, by decide⟩ : Fin data.worldCount)", 24⟩ := by
  native_decide

example : renderDerivedFactCosted (.unary "SimpleQualityType" 7) 2 =
    ⟨"SimpleQualityType sig.toUFOSignature3_12 (⟨7, by decide⟩ : Fin data.thingCount) (⟨2, by decide⟩ : Fin data.worldCount)", 26⟩ := by
  native_decide

example : renderDerivedFactCosted (.unary "ComplexQualityType" 7) 2 =
    ⟨"ComplexQualityType sig.toUFOSignature3_12 (⟨7, by decide⟩ : Fin data.thingCount) (⟨2, by decide⟩ : Fin data.worldCount)", 28⟩ := by
  native_decide

example : renderDerivedFactCosted (.unary "customUnary" 7) 2 =
    ⟨"sig.customUnary (⟨7, by decide⟩ : Fin data.thingCount) (⟨2, by decide⟩ : Fin data.worldCount)", 27⟩ := by
  native_decide

example : renderDerivedFactCosted (.binary "ProperSub" 7 9) 2 =
    ⟨"ProperSub sig.toUFOSignature3_1 (⟨7, by decide⟩ : Fin data.thingCount) (⟨9, by decide⟩ : Fin data.thingCount) (⟨2, by decide⟩ : Fin data.worldCount)", 21⟩ := by
  native_decide

example : renderDerivedFactCosted (.binary "UltimateBearerOf" 7 9) 2 =
    ⟨"UltimateBearerOf sig.toUFOSignature3_9 (⟨7, by decide⟩ : Fin data.thingCount) (⟨9, by decide⟩ : Fin data.thingCount) (⟨2, by decide⟩ : Fin data.worldCount)", 23⟩ := by
  native_decide

example : renderDerivedFactCosted (.binary "SubsetOf" 7 9) 2 =
    ⟨"SubsetOf sig.toUFOSignature3_12 (⟨7, by decide⟩ : Fin data.thingCount) (⟨9, by decide⟩ : Fin data.thingCount) (⟨2, by decide⟩ : Fin data.worldCount)", 25⟩ := by
  native_decide

example : renderDerivedFactCosted (.binary "ProperSubsetOf" 7 9) 2 =
    ⟨"ProperSubsetOf sig.toUFOSignature3_12 (⟨7, by decide⟩ : Fin data.thingCount) (⟨9, by decide⟩ : Fin data.thingCount) (⟨2, by decide⟩ : Fin data.worldCount)", 27⟩ := by
  native_decide

example : renderDerivedFactCosted (.binary "customBinary" 7 9) 2 =
    ⟨"sig.customBinary (⟨7, by decide⟩ : Fin data.thingCount) (⟨9, by decide⟩ : Fin data.thingCount) (⟨2, by decide⟩ : Fin data.worldCount)", 26⟩ := by
  native_decide

example : renderDerivedFactCosted (.ternary "customTernary" 7 9 11) 2 =
    ⟨"sig.customTernary (⟨7, by decide⟩ : Fin data.thingCount) (⟨9, by decide⟩ : Fin data.thingCount) (⟨11, by decide⟩ : Fin data.thingCount) (⟨2, by decide⟩ : Fin data.worldCount)", 22⟩ := by
  native_decide

example : renderDerivedFactCosted (.quaternary "customQuaternary" 7 9 11 13) 2 =
    ⟨"sig.customQuaternary (⟨7, by decide⟩ : Fin data.thingCount) (⟨9, by decide⟩ : Fin data.thingCount) (⟨11, by decide⟩ : Fin data.thingCount) (⟨13, by decide⟩ : Fin data.thingCount) (⟨2, by decide⟩ : Fin data.worldCount)", 27⟩ := by
  native_decide

/-- Large coordinates affect character work, but not the counted calls. -/
example : (renderDerivedFactCosted
    (.quaternary "customQuaternary" 1000000000000 9 11 13) 1000000000000).cost = 27 := by
  native_decide

/-- An empty everywhere scope does not call the renderer. An explicit scope
still emits its given world; source resolution is responsible for validation. -/
example :
    let result := expandScopedFactsCosted 0 #[.derived (.unary "Quality" 0) .everywhere]
    result.value.isEmpty = true ∧ result.cost = 4 := by native_decide

example :
    let result := expandScopedFactsCosted 0 #[.derived (.unary "Quality" 0) (.at 7)]
    (match result.value.toList with
    | [.derived text] => text == renderDerivedFactSpecification (.unary "Quality" 0) 7
    | _ => false) = true ∧ result.cost = 23 := by native_decide

/-- The largest rendering branch contributes 28 units to each expanded fact.
Scope traversal and output storage contribute three more per output and four
per input, attaining the scope bound for this one-fact fixture. -/
example :
    let result := expandScopedFactsCosted 2 #[
      .derived (.unary "ComplexQualityType" 0) .everywhere]
    result.value.size = 2 ∧ result.cost = 66 := by native_decide

end LeanUfo.Test.Complexity.DerivedFactRendering
