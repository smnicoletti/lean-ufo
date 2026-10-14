import LeanUfo.UFO.FormalAnalysis.Satisfiability.Relator.Model3_10

/-!
# Relator anti-vacuity analysis through section 3.10

The ordinary `Model3_10` interpretation proves joint satisfiability with an
empty relator extension. The `FormalAnalysis.Satisfiability.Relator` chain gives
a direct interpretation of the corrected section 3.10 package with a nonempty
relator extension. The theorem below records its anti-vacuity consequence.

The witness contains, at the same world:
- one relator;
- two distinct qua individuals that are proper parts of the relator;
- two distinct mediated bearers;
- one shared perdurant foundation.

The theorem below uses the active `UFOAxioms3_10` instance. The printed
overlap-based (a73) is not an assumption; `Relator.Model3_10.not_ax73_printed`
proves that the same interpretation refutes it.
-/

namespace AntiVacuity.Relators

open Relator.Model3_1

/-- The corrected section 3.10 package has a model in which the relator,
qua-individual, mediation, and foundation predicates are nonempty
simultaneously. -/
theorem relator_fragment_nonempty :
    let Sig := Relator.Model3_10.sig
    Sig.Relator .relator .actual ∧
    Sig.QuaIndividual .quaA .actual ∧
    Sig.QuaIndividual .quaB .actual ∧
    Sig.ProperPart .quaA .relator .actual ∧
    Sig.ProperPart .quaB .relator .actual ∧
    Sig.QuaIndividualOf .quaA .bearerA .actual ∧
    Sig.QuaIndividualOf .quaB .bearerB .actual ∧
    Sig.Mediates .relator .bearerA .actual ∧
    Sig.Mediates .relator .bearerB .actual ∧
    FoundationOf Sig .quaA .actual = FoundationOf Sig .quaB .actual := by
  let h := Relator.Model3_10.positive_relator_witness
  refine ⟨h.1, ?_, ?_, h.2.1, h.2.2.1, h.2.2.2.1,
    h.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2,
    h.2.2.2.2.2.2.1⟩
  · change Relator.Model3_10.quaIndividual .quaA
    trivial
  · change Relator.Model3_10.quaIndividual .quaB
    trivial

/-- Every primitive predicate introduced in section 3.10 is inhabited in the
same interpretation. The externally-dependent witness is obtained from (a70),
so this statement checks the connection between that relation and the
externally-dependent-mode classification as well as the relation table. -/
theorem predicates_nonempty :
    let Sig := Relator.Model3_10.sig
    (∃ x y w, Sig.ExternallyDependent x y w) ∧
    (∃ x w, Sig.ExternallyDependentMode x w) ∧
    (∃ x y w, Sig.FoundedBy x y w) ∧
    (∃ x y w, Sig.QuaIndividualOf x y w) ∧
    (∃ x w, Sig.QuaIndividual x w) ∧
    (∃ x y w, Sig.Mediates x y w) := by
  have hEDM : Relator.Model3_10.sig.ExternallyDependentMode
      .quaA .actual := by
    change Relator.Model3_10.externallyDependentMode .quaA
    trivial
  rcases (Relator.Model3_10.ax70_sig .quaA .actual).1 hEDM with
    ⟨_, y, hExternal⟩
  refine ⟨⟨.quaA, y, .actual, hExternal⟩, ⟨.quaA, .actual, hEDM⟩,
    ⟨.quaA, .foundation, .actual, ?_⟩,
    ⟨.quaA, .bearerA, .actual, ?_⟩,
    ⟨.quaA, .actual, ?_⟩,
    ⟨.relator, .bearerA, .actual, ?_⟩⟩
  · change Relator.Model3_10.foundedBy .quaA .foundation
    trivial
  · change Relator.Model3_10.quaIndividualOf .quaA .bearerA
    trivial
  · change Relator.Model3_10.quaIndividual .quaA
    trivial
  · exact (relator_fragment_nonempty).2.2.2.2.2.2.2.1

/-- The witness satisfies the active `UFOAxioms3_10` package. -/
example : UFOAxioms3_10 Relator.Model3_10.sig := by infer_instance

end AntiVacuity.Relators
