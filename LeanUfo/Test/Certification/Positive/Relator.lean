import LeanUfo.UFO.DSL.ConcreteExamples.RelatorProbe

/-!
End-to-end regression for the repaired relator fragment.

The canonical DSL model lives in `ConcreteExamples/RelatorProbe.lean` and is
imported here instead of being duplicated. A fresh certification of that model
takes about 22 minutes, so defining a second `ufo_model` in this test would pay
the same cost twice and allow the two witnesses to drift apart.

The indices below follow the declaration order in `RelatorProbe`. Generated DSL
models do not currently export named constants for their worlds and things, so
downstream semantic assertions must identify them as elements of the compiled
finite domains. Keeping these assertions outside the example makes changes to
the compiled tables or checker contract visible to the test suite.
-/

open LeanUfo.UFO
open LeanUfo.UFO.DSL

namespace TestRelatorProbe

private def actual : Fin RelatorProbe.data.worldCount := ⟨0, by decide⟩
private def relator : Fin RelatorProbe.data.thingCount := ⟨4, by decide⟩
private def quaA : Fin RelatorProbe.data.thingCount := ⟨5, by decide⟩
private def quaB : Fin RelatorProbe.data.thingCount := ⟨6, by decide⟩
private def bearerA : Fin RelatorProbe.data.thingCount := ⟨7, by decide⟩
private def bearerB : Fin RelatorProbe.data.thingCount := ⟨8, by decide⟩

example : FiniteModel4.Certified RelatorProbe.data :=
  RelatorProbe.certifiedModel

example : RelatorProbe.data.relator relator actual = true := by native_decide
example : RelatorProbe.data.properPart quaA relator actual = true := by native_decide
example : RelatorProbe.data.properPart quaB relator actual = true := by native_decide
example : RelatorProbe.data.quaIndividualOf quaA bearerA actual = true := by native_decide
example : RelatorProbe.data.quaIndividualOf quaB bearerB actual = true := by native_decide
example : RelatorProbe.data.mediates relator bearerA actual = true := by native_decide
example : RelatorProbe.data.mediates relator bearerB actual = true := by native_decide

example : Checker.checkAx73 RelatorProbe.data = true := RelatorProbe.checked_ax73
example : Checker.checkAx79 RelatorProbe.data = true := RelatorProbe.checked_ax79
example : Checker.checkAx80 RelatorProbe.data = true := RelatorProbe.checked_ax80

example : ax_a73 RelatorProbe.sig.toUFOSignature3_10 :=
  RelatorProbe.certified_ax73

example : ¬ ax_a73_printed RelatorProbe.sig.toUFOSignature3_10 := by
  intro hPrinted
  have hQua : RelatorProbe.sig.QuaIndividualOf quaA bearerA actual := by
    have h : RelatorProbe.data.quaIndividualOf quaA bearerA actual = true := by
      native_decide
    change RelatorProbe.data.quaIndividualOf quaA bearerA actual = true
    exact h
  have hOverlap : RelatorProbe.sig.Overlap relator quaA actual := by
    have h : RelatorProbe.data.overlap relator quaA actual = true := by
      native_decide
    change RelatorProbe.data.overlap relator quaA actual = true
    exact h
  have hRelatorEDM : RelatorProbe.sig.ExternallyDependentMode relator actual :=
    (((hPrinted quaA bearerA actual).1 hQua relator).1 hOverlap).1
  have hRelatorMode : RelatorProbe.sig.Mode relator actual :=
    ((RelatorProbe.certified_ax70 relator actual).1 hRelatorEDM).1
  have hModeFalse : RelatorProbe.data.mode relator actual = false := by
    native_decide
  have hModeTrue : RelatorProbe.data.mode relator actual = true := by
    change RelatorProbe.data.mode relator actual = true at hRelatorMode
    exact hRelatorMode
  simp [hModeFalse] at hModeTrue

end TestRelatorProbe
