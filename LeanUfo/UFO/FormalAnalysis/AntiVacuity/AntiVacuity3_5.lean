import LeanUfo.UFO.FormalAnalysis.Satisfiability.Relator.Model3_5

/-!
# Anti-vacuity analysis for section 3.5

The positive relator mereology contains reflexive parts, overlap, and two
proper parts of one relator. Thus all three primitive mereological predicates
are inhabited in one model of the cumulative section 3.5 package.
-/

namespace AntiVacuity.Section3_5

theorem predicates_nonempty :
    (∃ x y w, Relator.Model3_5.sig.Part x y w) ∧
    (∃ x y w, Relator.Model3_5.sig.Overlap x y w) ∧
    (∃ x y w, Relator.Model3_5.sig.ProperPart x y w) := by
  refine ⟨⟨.quaA, .relator, .actual, by simp⟩,
    ⟨.quaA, .relator, .actual, by simp⟩,
    ⟨.quaA, .relator, .actual, by simp [Relator.Model3_5.part]⟩⟩

end AntiVacuity.Section3_5
