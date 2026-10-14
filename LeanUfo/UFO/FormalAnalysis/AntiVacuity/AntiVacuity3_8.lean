import LeanUfo.UFO.Core.Section3_8
import LeanUfo.UFO.FormalAnalysis.AntiVacuity.AntiVacuity3_7

/-!
# Anti-vacuity analysis for section 3.8

Existential dependence and independence are interpreted directly from the
world-dependent existence profiles. Reflexive dependence is inhabited by
every entity. `external` and `bearerA` each occur at a world where the other
does not, which witnesses independence in both directions.
-/

namespace AntiVacuity.Section3_8

open Relator.Model3_1

def sig : UFOSignature3_8 where
  toUFOSignature3_7 := AntiVacuity.Section3_7.sig
  ExistentialDependence := fun x y w =>
    Frame.Box (F := AntiVacuity.Section3_7.sig.F)
      (fun w' => AntiVacuity.Section3_7.sig.Ex x w' ->
        AntiVacuity.Section3_7.sig.Ex y w') w
  ExistentialIndependence := fun x y w =>
    (¬ Frame.Box (F := AntiVacuity.Section3_7.sig.F)
      (fun w' => AntiVacuity.Section3_7.sig.Ex x w' ->
        AntiVacuity.Section3_7.sig.Ex y w') w) ∧
    (¬ Frame.Box (F := AntiVacuity.Section3_7.sig.F)
      (fun w' => AntiVacuity.Section3_7.sig.Ex y w' ->
        AntiVacuity.Section3_7.sig.Ex x w') w)

instance : UFOAxioms3_8 sig where
  toUFOAxioms3_7 := by
    change UFOAxioms3_7 AntiVacuity.Section3_7.sig
    infer_instance
  ax62 := by intro x w h; trivial
  ax63 := by intro x y w; rfl
  ax64 := by intro x y w; rfl

private theorem independent_fact (w : World) :
    sig.ExistentialIndependence .external .bearerA w := by
  constructor
  · intro h
    exact h .external trivial (by simp [Relator.Model3_7.ex])
  · intro h
    exact h .bearerA trivial (by simp [Relator.Model3_7.ex])

theorem predicates_nonempty :
    (∃ x y w, sig.ExistentialDependence x y w) ∧
    (∃ x y w, sig.ExistentialIndependence x y w) := by
  refine ⟨⟨.relator, .relator, .actual, ?_⟩,
    ⟨.external, .bearerA, .actual, independent_fact .actual⟩⟩
  intro w _ h
  exact h

end AntiVacuity.Section3_8
