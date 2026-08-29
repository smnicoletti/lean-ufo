import LeanUfo.UFO.Core.AxiomaticAnalysis
import LeanUfo.UFO.Models.RelatorRepair.Model3_9

/-!
# Analysis model for the relator repair: section 3.10

The model satisfies every §3.10 assumption except the current overlap-based
(a73). It satisfies the selected part-based repair and the guarded-overlap
formula retained for comparison. Its relator has exactly two qua-individual
proper parts. They inhere in distinct bearers and share one perdurant foundation.
-/

namespace RelatorRepair.Model3_10

open Model3_1

def foundedBy : Thing -> Thing -> Prop
  | .relator, .foundation | .quaA, .foundation | .quaB, .foundation => True
  | _, _ => False

def quaIndividualOf : Thing -> Thing -> Prop
  | .quaA, .bearerA | .quaB, .bearerB => True
  | _, _ => False

def quaIndividual : Thing -> Prop
  | .quaA | .quaB => True
  | _ => False

def externallyDependentMode : Thing -> Prop
  | .quaA | .quaB => True
  | _ => False

def sig : UFOSignature3_10 where
  toUFOSignature3_9 := Model3_9.sig
  ExternallyDependent := fun x y w =>
    Model3_9.sig.ExistentialDependence x y w ∧
      forall z, Model3_9.sig.InheresIn x z w ->
        Model3_9.sig.ExistentialIndependence y z w
  ExternallyDependentMode := fun x _ => externallyDependentMode x
  FoundedBy := fun x y _ => foundedBy x y
  QuaIndividualOf := fun x y _ => quaIndividualOf x y
  QuaIndividual := fun x _ => quaIndividual x
  Mediates := fun x y w =>
    Model3_9.sig.Relator x w ∧
      Model3_9.sig.Endurant y w ∧
      exists z, quaIndividualOf z y ∧ Model3_9.sig.Part z x w

attribute [simp] foundedBy quaIndividualOf quaIndividual externallyDependentMode

/-- External dependence is interpreted exactly by (a69). -/
theorem ax69_sig : ax_a69 sig := by intro x y w; rfl

private theorem external_independent_bearerA (w : World) :
    sig.ExistentialIndependence .external .bearerA w := by
  change
    (¬ Frame.Box (F := Model3_1.frame)
      (fun w' => Model3_7.ex .external w' -> Model3_7.ex .bearerA w') w) ∧
    (¬ Frame.Box (F := Model3_1.frame)
      (fun w' => Model3_7.ex .bearerA w' -> Model3_7.ex .external w') w)
  constructor
  · intro h
    exact h .external trivial (by simp [Model3_7.ex])
  · intro h
    exact h .bearerA trivial (by simp [Model3_7.ex])

private theorem external_independent_bearerB (w : World) :
    sig.ExistentialIndependence .external .bearerB w := by
  change
    (¬ Frame.Box (F := Model3_1.frame)
      (fun w' => Model3_7.ex .external w' -> Model3_7.ex .bearerB w') w) ∧
    (¬ Frame.Box (F := Model3_1.frame)
      (fun w' => Model3_7.ex .bearerB w' -> Model3_7.ex .external w') w)
  constructor
  · intro h
    exact h .external trivial (by simp [Model3_7.ex])
  · intro h
    exact h .bearerB trivial (by simp [Model3_7.ex])

private theorem quaA_externallyDependent_external (w : World) :
    sig.ExternallyDependent .quaA .external w := by
  constructor
  · intro w' _ hEx
    cases w' <;> simp_all [Model3_7.ex]
  · intro z hInheres
    change Model3_9.inheresIn .quaA z at hInheres
    cases z <;> simp_all [Model3_9.inheresIn]
    exact external_independent_bearerA w

private theorem quaB_externallyDependent_external (w : World) :
    sig.ExternallyDependent .quaB .external w := by
  constructor
  · intro w' _ hEx
    cases w' <;> simp_all [Model3_7.ex]
  · intro z hInheres
    change Model3_9.inheresIn .quaB z at hInheres
    cases z <;> simp_all [Model3_9.inheresIn]
    exact external_independent_bearerB w

/-- Externally dependent modes are interpreted exactly by (a70). -/
theorem ax70_sig : ax_a70 sig := by
  intro x w
  cases x <;> simp [sig, externallyDependentMode, Model3_3.mode]
  · exact ⟨.external, quaA_externallyDependent_external w⟩
  · exact ⟨.external, quaB_externallyDependent_external w⟩

/-- In the witness, exactly `quaA` and `quaB` are externally dependent modes. -/
theorem externallyDependentMode_iff (x : Thing) (w : World) :
    sig.ExternallyDependentMode x w ↔ x = .quaA ∨ x = .quaB := by
  cases x <;> simp [sig, externallyDependentMode]

/-- The proper parts of the relator are exactly the two qua individuals. -/
theorem properPart_relator_iff (x : Thing) (w : World) :
    sig.ProperPart x .relator w ↔ x = .quaA ∨ x = .quaB := by
  change (Model3_5.part x .relator ∧ ¬ Model3_5.part .relator x) ↔ _
  cases x <;> simp [Model3_5.part]

/-- The qua-individual predicate holds exactly for `quaA` and `quaB`. -/
theorem quaIndividual_iff (x : Thing) (w : World) :
    sig.QuaIndividual x w ↔ x = .quaA ∨ x = .quaB := by
  change quaIndividual x ↔ _
  cases x <;> simp [quaIndividual]

/-- The two qua individuals have identical existence profiles. -/
private theorem qua_dependence
    {x y : Thing} (hx : x = .quaA ∨ x = .quaB)
    (hy : y = .quaA ∨ y = .quaB) (w : World) :
    sig.ExistentialDependence x y w := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  all_goals
    intro w' _ hEx
    cases w' <;> simp_all [Model3_7.ex]

/-- Founded entities have the category and perdurant foundation required by (a71). -/
theorem ax71_sig : ax_a71 sig := by
  intro x y w h
  change foundedBy x y at h
  change (externallyDependentMode x ∨ Model3_3.relator x) ∧
    Model3_1.perdurant y
  cases x <;> cases y <;> simp_all [foundedBy, externallyDependentMode,
    Model3_3.relator, Model3_1.perdurant]

private theorem unique_foundation_quaA (w : World) :
    ∃! y, sig.FoundedBy .quaA y w := by
  refine ⟨.foundation, ?_, ?_⟩
  · change foundedBy .quaA .foundation
    trivial
  · intro y h
    change foundedBy .quaA y at h
    cases y <;> simp_all [foundedBy]
    rfl

private theorem unique_foundation_quaB (w : World) :
    ∃! y, sig.FoundedBy .quaB y w := by
  refine ⟨.foundation, ?_, ?_⟩
  · change foundedBy .quaB .foundation
    trivial
  · intro y h
    change foundedBy .quaB y at h
    cases y <;> simp_all [foundedBy]
    rfl

private theorem unique_foundation_relator (w : World) :
    ∃! y, sig.FoundedBy .relator y w := by
  refine ⟨.foundation, ?_, ?_⟩
  · change foundedBy .relator .foundation
    trivial
  · intro y h
    change foundedBy .relator y at h
    cases y <;> simp_all [foundedBy]
    rfl

/-- Both externally dependent modes have the same unique foundation. -/
theorem ax72_sig : ax_a72 sig := by
  intro x w h
  have hx := (externallyDependentMode_iff x w).1 h
  rcases hx with rfl | rfl
  · exact unique_foundation_quaA w
  · exact unique_foundation_quaB w

@[simp] theorem foundationOf_quaA (w : World) :
    FoundationOf sig .quaA w = .foundation :=
  (foundationOf_eq_iff (Sig := sig) (unique_foundation_quaA w)).2 (by
    change foundedBy .quaA .foundation
    trivial)

@[simp] theorem foundationOf_quaB (w : World) :
    FoundationOf sig .quaB w = .foundation :=
  (foundationOf_eq_iff (Sig := sig) (unique_foundation_quaB w)).2 (by
    change foundedBy .quaB .foundation
    trivial)

@[simp] theorem foundationOf_relator (w : World) :
    FoundationOf sig .relator w = .foundation :=
  (foundationOf_eq_iff (Sig := sig) (unique_foundation_relator w)).2 (by
    change foundedBy .relator .foundation
    trivial)

/-- Qua-individual membership is the existential closure of the bearer table. -/
theorem ax74_sig : ax_a74 sig := by
  intro x w
  cases x <;> simp [sig, quaIndividual, quaIndividualOf]
  · exact ⟨.bearerA, trivial⟩
  · exact ⟨.bearerB, trivial⟩

/-- Every qua individual is one of the two externally dependent modes. -/
theorem ax75_sig : ax_a75 sig := by
  intro x w h
  change quaIndividual x at h
  change externallyDependentMode x
  cases x <;> simp_all [quaIndividual, externallyDependentMode]

/-- Each qua individual has one bearer in the relation table. -/
theorem ax76_sig : ax_a76 sig := by
  intro x y y' w h
  change quaIndividualOf x y ∧ quaIndividualOf x y' at h
  cases x <;> cases y <;> cases y' <;> simp_all [quaIndividualOf]
  all_goals rfl

/-- The single relator has the shared unique foundation. -/
theorem ax77_sig : ax_a77 sig := by
  intro x w h
  change Model3_3.relator x at h
  cases x <;> simp_all [Model3_3.relator]
  exact unique_foundation_relator w

/-- Every part of the relator has the shared foundation. -/
theorem ax78_sig : ax_a78 sig := by
  intro x y w h
  rcases h with ⟨hRel, hPart⟩
  change Model3_3.relator x at hRel
  cases x <;> simp [Model3_3.relator] at hRel
  change Model3_5.part y .relator at hPart
  cases y <;> simp [Model3_5.part] at hPart
  · rfl
  · exact (foundationOf_relator w).trans (foundationOf_quaA w).symm
  · exact (foundationOf_relator w).trans (foundationOf_quaB w).symm

/-- The original ax79 is satisfied by the two-qua-individual relator. -/
theorem ax79_sig : ax_a79 sig := by
  intro x w
  constructor
  · intro hRel
    change Model3_3.relator x at hRel
    cases x <;> simp [Model3_3.relator] at hRel
    refine ⟨⟨.quaA, ?_⟩, ?_, ?_⟩
    · change Model3_5.part .quaA .relator ∧
        ¬ Model3_5.part .relator .quaA
      simp [Model3_5.part]
    · intro y z h
      rcases h with ⟨hy, hz⟩
      have hyCases := (properPart_relator_iff y w).1 hy
      have hzCases := (properPart_relator_iff z w).1 hz
      refine ⟨(quaIndividual_iff y w).2 hyCases,
        (quaIndividual_iff z w).2 hzCases, ?_,
        qua_dependence hyCases hzCases w, qua_dependence hzCases hyCases w⟩
      rcases hyCases with rfl | rfl <;> rcases hzCases with rfl | rfl
      all_goals
        first
        | rfl
        | exact (foundationOf_quaA w).trans (foundationOf_quaB w).symm
        | exact (foundationOf_quaB w).trans (foundationOf_quaA w).symm
    · intro y z h
      rcases h with ⟨hy, hzQua, _hFoundation, _hYZ, _hZY⟩
      have hzCases := (quaIndividual_iff z w).1 hzQua
      exact (properPart_relator_iff z w).2 hzCases
  · rintro ⟨⟨y, hy⟩, _hPairwise, _hClosure⟩
    change Model3_5.part y x ∧ ¬ Model3_5.part x y at hy
    change Model3_3.relator x
    cases x <;> cases y <;> simp_all [Model3_5.part]

/-- Mediation is interpreted exactly by (a80). -/
theorem ax80_sig : ax_a80 sig := by intro x y w; rfl

/-- A qua individual's bearer is an endurant in the direct model. -/
theorem quaIndividualOf_endurant_sig : ax_quaIndividualOf_endurant (Sig := sig) := by
  intro x y w h
  change quaIndividualOf x y at h
  change Model3_1.endurant y
  cases x <;> cases y <;> simp_all [quaIndividualOf]

/-- The selected part-based ax73 repair holds in the positive relator model. -/
theorem ax73_part_sig : ax_a73_part_characterization sig := by
  intro x y w
  constructor
  · intro h
    change quaIndividualOf x y at h
    cases x <;> cases y <;> simp [quaIndividualOf] at h
    · intro z
      change Model3_5.part z .quaA ↔
        (externallyDependentMode z ∧ Model3_9.inheresIn z .bearerA ∧
          FoundationOf sig z w = FoundationOf sig .quaA w)
      cases z <;> simp [Model3_5.part, externallyDependentMode,
        Model3_9.inheresIn]
    · intro z
      change Model3_5.part z .quaB ↔
        (externallyDependentMode z ∧ Model3_9.inheresIn z .bearerB ∧
          FoundationOf sig z w = FoundationOf sig .quaB w)
      cases z <;> simp [Model3_5.part, externallyDependentMode,
        Model3_9.inheresIn]
  · intro h
    have hSelfPart : sig.Part x x w := Model3_5.ax47_sig x w
    have hSelf := (h x).1 hSelfPart
    have hEDM := hSelf.1
    have hInheres := hSelf.2.1
    change externallyDependentMode x at hEDM
    change Model3_9.inheresIn x y at hInheres
    change quaIndividualOf x y
    cases x <;> cases y <;> simp_all [externallyDependentMode,
      Model3_9.inheresIn, quaIndividualOf]

/-- The guarded-overlap comparison formula also holds in the same model. -/
theorem ax73_guarded_overlap_sig : ax_a73_guarded_overlap sig := by
  intro x y w
  constructor
  · intro h
    change quaIndividualOf x y at h
    cases x <;> cases y <;> simp [quaIndividualOf] at h
    · refine ⟨by change externallyDependentMode .quaA; trivial,
        by change Model3_9.inheresIn .quaA .bearerA; trivial, ?_⟩
      intro z hz
      change externallyDependentMode z at hz
      change Model3_5.overlap z .quaA ↔
        (Model3_9.inheresIn z .bearerA ∧
          FoundationOf sig z w = FoundationOf sig .quaA w)
      cases z <;> simp_all [externallyDependentMode, Model3_5.overlap,
        Model3_9.inheresIn]
    · refine ⟨by change externallyDependentMode .quaB; trivial,
        by change Model3_9.inheresIn .quaB .bearerB; trivial, ?_⟩
      intro z hz
      change externallyDependentMode z at hz
      change Model3_5.overlap z .quaB ↔
        (Model3_9.inheresIn z .bearerB ∧
          FoundationOf sig z w = FoundationOf sig .quaB w)
      cases z <;> simp_all [externallyDependentMode, Model3_5.overlap,
        Model3_9.inheresIn]
  · rintro ⟨hEDM, hInheres, _hOverlap⟩
    change externallyDependentMode x at hEDM
    change Model3_9.inheresIn x y at hInheres
    change quaIndividualOf x y
    cases x <;> cases y <;> simp_all [externallyDependentMode,
      Model3_9.inheresIn, quaIndividualOf]

/-- All unchanged section 3.10 assumptions, explicitly excluding ax73. -/
instance baseAxioms : UFOAxioms3_10WithoutA73 sig where
  toUFOAxioms3_9 := by
    change UFOAxioms3_9 Model3_9.sig
    infer_instance
  ax69 := ax69_sig
  ax70 := ax70_sig
  ax71 := ax71_sig
  ax72 := ax72_sig
  ax74 := ax74_sig
  ax75 := ax75_sig
  ax76 := ax76_sig
  ax77 := ax77_sig
  ax78 := ax78_sig
  ax79 := ax79_sig
  ax80 := ax80_sig
  axQuaIndividualOfEndurant := quaIndividualOf_endurant_sig

/-- Complete analysis package for the selected part-based repair. -/
instance : UFOAxioms3_10PartRepair sig where
  toUFOAxioms3_10WithoutA73 := baseAxioms
  ax73Part := ax73_part_sig

/-- Complete comparison package retained for the guarded-overlap experiment. -/
instance : UFOAxioms3_10GuardedOverlapRepair sig where
  toUFOAxioms3_10WithoutA73 := baseAxioms
  ax73GuardedOverlap := ax73_guarded_overlap_sig

/--
Positive satisfiability witness for the selected repair: a relator with two
qua-individual proper parts, distinct mediated bearers, and one shared
foundation.
-/
theorem positive_relator_witness :
    sig.Relator .relator .actual ∧
    sig.ProperPart .quaA .relator .actual ∧
    sig.ProperPart .quaB .relator .actual ∧
    sig.QuaIndividualOf .quaA .bearerA .actual ∧
    sig.QuaIndividualOf .quaB .bearerB .actual ∧
    Thing.bearerA ≠ Thing.bearerB ∧
    FoundationOf sig .quaA .actual = FoundationOf sig .quaB .actual ∧
    sig.Mediates .relator .bearerA .actual ∧
    sig.Mediates .relator .bearerB .actual := by
  refine ⟨by change Model3_3.relator .relator; trivial,
    (properPart_relator_iff .quaA .actual).2 (Or.inl rfl),
    (properPart_relator_iff .quaB .actual).2 (Or.inr rfl),
    by change quaIndividualOf .quaA .bearerA; trivial,
    by change quaIndividualOf .quaB .bearerB; trivial,
    by decide, (foundationOf_quaA .actual).trans (foundationOf_quaB .actual).symm,
    ?_, ?_⟩
  · change Model3_3.relator .relator ∧ Model3_1.endurant .bearerA ∧
      ∃ z, quaIndividualOf z .bearerA ∧ Model3_5.part z .relator
    exact ⟨trivial, trivial, ⟨.quaA, trivial, by simp [Model3_5.part]⟩⟩
  · change Model3_3.relator .relator ∧ Model3_1.endurant .bearerB ∧
      ∃ z, quaIndividualOf z .bearerB ∧ Model3_5.part z .relator
    exact ⟨trivial, trivial, ⟨.quaB, trivial, by simp [Model3_5.part]⟩⟩

end RelatorRepair.Model3_10
