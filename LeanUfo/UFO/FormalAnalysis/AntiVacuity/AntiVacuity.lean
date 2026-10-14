import LeanUfo.UFO.FormalAnalysis.AntiVacuity.AntiVacuity3_1
import LeanUfo.UFO.FormalAnalysis.AntiVacuity.AntiVacuity3_2
import LeanUfo.UFO.FormalAnalysis.AntiVacuity.AntiVacuity3_3
import LeanUfo.UFO.FormalAnalysis.AntiVacuity.AntiVacuity3_4
import LeanUfo.UFO.FormalAnalysis.AntiVacuity.AntiVacuity3_5
import LeanUfo.UFO.FormalAnalysis.AntiVacuity.AntiVacuity3_6
import LeanUfo.UFO.FormalAnalysis.AntiVacuity.AntiVacuity3_7
import LeanUfo.UFO.FormalAnalysis.AntiVacuity.AntiVacuity3_8
import LeanUfo.UFO.FormalAnalysis.AntiVacuity.AntiVacuity3_9
import LeanUfo.UFO.FormalAnalysis.AntiVacuity.AntiVacuity3_10
import LeanUfo.UFO.FormalAnalysis.AntiVacuity.AntiVacuity3_11
import LeanUfo.UFO.FormalAnalysis.AntiVacuity.AntiVacuity3_12
import LeanUfo.UFO.FormalAnalysis.AntiVacuity.AntiVacuity3_13
import LeanUfo.UFO.FormalAnalysis.AntiVacuity.AntiVacuity4

/-!
# Anti-vacuity checkpoints

`Satisfiability.Consistency` proves that each axiom package has a model.
The checkpoints in this file add explicit inhabitants for taxonomy predicates
whose empty extensions could hide contradictions.

Each theorem supplies one signature, one axiom-package instance, and all listed
inhabitants in that same interpretation. The section-specific modules for
sections 3.5-3.9 additionally expose non-emptiness theorems for mereology,
composition, constitution, dependence, and inherence. The section 3.10
checkpoint uses the positive relator interpretation. Sections 3.12, 3.13, and
4 add cumulative quality, endurant/perdurant, and type-structure models.

Every section module exports a local non-emptiness theorem:
- §3.1 uses `Taxonomy.section3_1_predicates_nonempty`; proper specialization is
  added by `Section3_2.section3_1_predicates_nonempty`;
- §3.2 uses `Section3_2.predicates_nonempty`;
- §§3.3-3.4 use the taxonomy namespace checkpoints;
- §§3.5-3.9 use `Section3_X.predicates_nonempty`;
- §3.10 uses `Relators.predicates_nonempty` and
  `Relators.relator_fragment_nonempty`;
- §§3.11-3.13 and §4 use their section namespace `predicates_nonempty` theorem.
-/

/-- Section 3.1 has one model with every primitive predicate inhabited. The
same model also contains a genuine proper specialization. -/
theorem anti_vacuity_3_1 :
    ∃ (Sig : UFOSignature3_1.{0}),
      UFOAxioms3_1 Sig ∧
      (∃ x w, Sig.Type_ x w) ∧
      (∃ x w, Sig.Individual x w) ∧
      (∃ x t w, Sig.Inst x t w) ∧
      (∃ t u w, Sig.Sub t u w) ∧
      (∃ t u w, ProperSub Sig t u w) ∧
      (∃ x w, Sig.ConcreteIndividual x w) ∧
      (∃ x w, Sig.AbstractIndividual x w) ∧
      (∃ x w, Sig.Endurant x w) ∧
      (∃ x w, Sig.Perdurant x w) ∧
      (∃ t w, Sig.EndurantType t w) ∧
      (∃ t w, Sig.PerdurantType t w) := by
  refine ⟨AntiVacuity.Section3_2.sig.toUFOSignature3_1, ?_, ?_⟩
  · exact AntiVacuity.Section3_2.axioms.toUFOAxioms3_1
  · exact AntiVacuity.Section3_2.section3_1_predicates_nonempty

/-- Section 3.2 has one two-world model in which all rigidity and sortality
categories are inhabited simultaneously. The interpretation includes both
stable and contingent instantiation profiles, which are needed to distinguish
rigid, anti-rigid, semi-rigid, sortal, and non-sortal types. -/
theorem anti_vacuity_3_2 :
    ∃ (Sig : UFOSignature3_2.{0}),
      UFOAxioms3_2 Sig ∧
      (∃ (w : Sig.F.World),
        (∃ x, Sig.Rigid x w) ∧
        (∃ x, Sig.AntiRigid x w) ∧
        (∃ x, Sig.SemiRigid x w) ∧
        (∃ x, Sig.Kind x w) ∧
        (∃ x, Sig.Sortal x w) ∧
        (∃ x, Sig.NonSortal x w) ∧
        (∃ x, Sig.SubKind x w) ∧
        (∃ x, Sig.Phase x w) ∧
        (∃ x, Sig.Role x w) ∧
        (∃ x, Sig.SemiRigidSortal x w) ∧
        (∃ x, Sig.Category x w) ∧
        (∃ x, Sig.Mixin x w) ∧
        (∃ x, Sig.PhaseMixin x w) ∧
        (∃ x, Sig.RoleMixin x w)) := by
  refine ⟨AntiVacuity.Section3_2.sig, inferInstance, .actual, ?_⟩
  exact AntiVacuity.Section3_2.predicates_nonempty

/-- Section 3.4 has one model with all six endurant-individual leaves and their
corresponding type and kind leaves inhabited at the same world. -/
theorem anti_vacuity_3_4 :
    ∃ (Sig : UFOSignature3_4.{0}),
      UFOAxioms3_4 Sig ∧
      (∃ (w : Sig.F.World),
        (∃ x, Sig.Object x w) ∧
        (∃ x, Sig.Collective x w) ∧
        (∃ x, Sig.Quantity x w) ∧
        (∃ x, Sig.Relator x w) ∧
        (∃ x, Sig.Mode x w) ∧
        (∃ x, Quality Sig.toUFOSignature3_3 x w) ∧
        (∃ t, Sig.ObjectType t w) ∧
        (∃ t, Sig.CollectiveType t w) ∧
        (∃ t, Sig.QuantityType t w) ∧
        (∃ t, Sig.RelatorType t w) ∧
        (∃ t, Sig.ModeType t w) ∧
        (∃ t, Sig.QualityType t w) ∧
        (∃ t, Sig.ObjectKind t w) ∧
        (∃ t, Sig.CollectiveKind t w) ∧
        (∃ t, Sig.QuantityKind t w) ∧
        (∃ t, Sig.RelatorKind t w) ∧
        (∃ t, Sig.ModeKind t w) ∧
        (∃ t, Sig.QualityKind t w)) := by
  let Sig := AntiVacuity.Taxonomy.sig
  let hTypes := AntiVacuity.Taxonomy.type_taxonomy_nonempty
  refine ⟨Sig, inferInstance, (),
    ⟨.individual .object, rfl⟩,
    ⟨.individual .collective, rfl⟩,
    ⟨.individual .quantity, rfl⟩,
    ⟨.individual .relator, rfl⟩,
    ⟨.individual .mode, rfl⟩,
    ⟨.individual .quality,
      (AntiVacuity.Taxonomy.quality_iff (.individual .quality) ()).2 rfl⟩,
    ⟨.kind .object, hTypes.1.1⟩,
    ⟨.kind .collective, hTypes.2.1.1⟩,
    ⟨.kind .quantity, hTypes.2.2.1.1⟩,
    ⟨.kind .relator, hTypes.2.2.2.1.1⟩,
    ⟨.kind .mode, hTypes.2.2.2.2.1.1⟩,
    ⟨.kind .quality, hTypes.2.2.2.2.2.1⟩,
    ⟨.kind .object, hTypes.1⟩,
    ⟨.kind .collective, hTypes.2.1⟩,
    ⟨.kind .quantity, hTypes.2.2.1⟩,
    ⟨.kind .relator, hTypes.2.2.2.1⟩,
    ⟨.kind .mode, hTypes.2.2.2.2.1⟩,
    ⟨.kind .quality, hTypes.2.2.2.2.2.2⟩⟩

/-- The corrected section 3.10 package has one model with a relator, two qua
individuals, their two mediated bearers, and their shared foundation. -/
theorem anti_vacuity_3_10 :
    ∃ (Sig : UFOSignature3_10.{0}),
      UFOAxioms3_10 Sig ∧
      (∃ (w : Sig.F.World) (r q₁ q₂ b₁ b₂ : Sig.Thing),
        Sig.Relator r w ∧
        Sig.QuaIndividual q₁ w ∧ Sig.QuaIndividual q₂ w ∧
        Sig.ProperPart q₁ r w ∧ Sig.ProperPart q₂ r w ∧
        Sig.QuaIndividualOf q₁ b₁ w ∧ Sig.QuaIndividualOf q₂ b₂ w ∧
        Sig.Mediates r b₁ w ∧ Sig.Mediates r b₂ w ∧
        FoundationOf Sig q₁ w = FoundationOf Sig q₂ w) := by
  let h := AntiVacuity.Relators.relator_fragment_nonempty
  refine ⟨Relator.Model3_10.sig, inferInstance, .actual,
    .relator, .quaA, .quaB, .bearerA, .bearerB, ?_⟩
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
    h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2⟩

/-- Section 3.11 has a cumulative model with an inhabited characterization
relation. Its characterizing moment has a unique inherence bearer among the
instances of the characterized endurant type. -/
theorem anti_vacuity_3_11 :
    ∃ (Sig : UFOSignature3_11.{0}),
      UFOAxioms3_11 Sig ∧
      ∃ (t m : Sig.Thing) (w : Sig.F.World),
        Sig.Characterization t m w := by
  refine ⟨AntiVacuity.Section3_11.sig, inferInstance, ?_⟩
  exact AntiVacuity.Section3_11.predicates_nonempty

/- The imported section modules expose their exhaustive local checkpoints as
`predicates_nonempty` (with the taxonomy and relator namespace qualifiers used
where necessary). Keeping those proofs in their section files makes this
module an aggregate entry point, parallel to `Satisfiability.Consistency`. -/
