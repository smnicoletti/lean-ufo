import LeanUfo.UFO.DSL.Diagnostic.Analysis

/-!
# Derived-assertion diagnostic regressions

These tests cover the pre-certification assertion path separately from
registered-axiom diagnostics. Exact counts use the primitive-call model.
-/

namespace LeanUfo.Test.Complexity.DerivedAssertions

open Lean LeanUfo.UFO.DSL
open private
  genericFunctionalDependenceRequiredMissingCosted
  genericFunctionalDependenceRequiredMissingCosted_value
  genericFunctionalDependenceRequiredMissingCosted_cost_le
  individualFunctionalDependenceRequiredMissingCosted
  individualFunctionalDependenceRequiredMissingCosted_value
  individualFunctionalDependenceRequiredMissingCosted_cost_le
  componentOfRequiredMissingCosted
  componentOfRequiredMissingCosted_value
  componentOfRequiredMissingCosted_cost_le
  genericConstitutionalDependenceRequiredMissingCosted
  genericConstitutionalDependenceRequiredMissingCosted_value
  genericConstitutionalDependenceRequiredMissingCosted_cost_le
  constitutionRequiredMissingCosted
  constitutionRequiredMissingCosted_value
  constitutionRequiredMissingCosted_cost_le
  genericFunctionalDependenceEvidenceCosted
  genericFunctionalDependenceEvidenceCosted_value
  genericFunctionalDependenceEvidenceCosted_cost_le
  genericFunctionalDependenceEvidenceCosted_size
  individualFunctionalDependenceEvidenceCosted
  individualFunctionalDependenceEvidenceCosted_value
  individualFunctionalDependenceEvidenceCosted_cost_le
  individualFunctionalDependenceEvidenceCosted_size
  componentOfEvidenceCosted
  componentOfEvidenceCosted_value
  componentOfEvidenceCosted_cost_le
  componentOfEvidenceCosted_size
  genericConstitutionalDependenceEvidenceCosted
  genericConstitutionalDependenceEvidenceCosted_value
  genericConstitutionalDependenceEvidenceCosted_cost_le
  genericConstitutionalDependenceEvidenceCosted_size
  constitutionEvidenceCosted
  constitutionEvidenceCosted_value
  constitutionEvidenceCosted_cost_le
  constitutionEvidenceCosted_size
  from LeanUfo.UFO.DSL.Diagnostic.DerivedAssertions
open private declaredExternalCandidatesCosted externallyDependentModeStatusCostBound
  externallyDependentWitnessCostBound
  from LeanUfo.UFO.DSL.Diagnostic.AxiomAnalysis
open private thingIndexByStringCosted thingIndexByStringCosted_value
  thingIndexByStringCosted_cost_le
  uniqueRelatedThingCosted uniqueRelatedThingCosted_value uniqueRelatedThingCosted_cost_le
  qualityLookup qualityStructureLookup
  simpleQualityLookupCosted simpleQualityLookupCosted_value simpleQualityLookupCosted_cost_le
  complexQualityLookupCosted complexQualityLookupCosted_value complexQualityLookupCosted_cost_le
  qualityTypeInstancesCosted qualityTypeInstancesCosted_value qualityTypeInstancesCosted_cost_le
  qualityTypeInstances_simple_cost_le qualityTypeInstances_complex_cost_le
  firstInvalidInstanceCosted firstInvalidInstanceCosted_value firstInvalidInstanceCosted_cost_le
  firstInvalidInstance_simple_cost_le firstInvalidInstance_complex_cost_le
  simpleQualityTypeLookup complexQualityTypeLookup
  firstRelatedThingCosted firstRelatedThingCosted_value firstRelatedThingCosted_cost_le
  firstRelationDifferenceCosted firstRelationDifferenceCosted_value firstRelationDifferenceCosted_cost_le
  nonEmptySetLookupCosted nonEmptySetLookupCosted_value nonEmptySetLookupCosted_cost_le
  subsetLookup subsetLookupCosted subsetLookupCosted_value subsetLookupCosted_cost_le
  properSubsetLookupCosted properSubsetLookupCosted_value properSubsetLookupCosted_cost_le
  properSubLookupCosted properSubLookupCosted_value properSubLookupCosted_cost_le
  categorizesLookupCosted categorizesLookupCosted_value categorizesLookupCosted_cost_le typeLookup
  firstSharedInstanceCosted firstSharedInstanceCosted_value firstSharedInstanceCosted_cost_le
  firstCoveredInstanceFailureCosted firstCoveredInstanceFailureCosted_value firstCoveredInstanceFailureCosted_cost_le
  isDisjointWithLookupCosted isDisjointWithLookupCosted_value isDisjointWithLookupCosted_cost_le
  isCompletelyCoveredByLookupCosted isCompletelyCoveredByLookupCosted_value isCompletelyCoveredByLookupCosted_cost_le
  isPartitionedIntoLookupCosted isPartitionedIntoLookupCosted_value isPartitionedIntoLookupCosted_cost_le
  ultimateBearerOfLookupCosted ultimateBearerOfLookupCosted_value ultimateBearerOfLookupCosted_cost_le
  withResolvedThingCosted withResolvedThingCosted_value withResolvedThingCosted_cost_le
  evalNamedDerivedFactSpec evalNamedDerivedFactCosted evalNamedDerivedFactCosted_value
  evalNamedDerivedFactCosted_cost_le namedDerivedPredicateCostBound
  namedDerivedPredicateCostBound_mono
  FailedDerivedAssertion FailedDerivedAssertion.mk failedDerivedAtCosted
  firstScopedDerivedFailureCosted firstDerivedFailureAtIndexCosted
  firstDerivedAssertionFailureCosted firstDerivedAssertionFailureSpec
  firstDerivedAssertionFailureCosted_value firstDerivedAssertionFailureCosted_cost_le
  firstDerivedAssertionFailureCostBound_mono
  relatedCandidatesCosted relatedCandidatesCosted_value relatedCandidatesCosted_sparse_value
  relatedCandidatesCosted_cost_le relatedCandidatesCosted_size_le
  firstFunctionalDependenceFailureCosted firstFunctionalDependenceFailureCosted_value
  firstFunctionalDependenceFailureCosted_cost_le
  firstConstitutionalDependenceFailureCosted firstConstitutionalDependenceFailureCosted_value
  firstConstitutionalDependenceFailureCosted_cost_le
  derivedAssertionSuggestionCosted derivedAssertionSuggestionSpec
  derivedAssertionSuggestionCosted_value derivedAssertionSuggestionCosted_cost_le
  qualityStatusEvidenceCosted qualityStatusEvidenceSpec qualityStatusEvidenceCosted_value
  qualityStatusEvidenceCosted_cost_le qualityStatusEvidenceCosted_size
  qualityRequiredMissingCosted qualityRequiredMissingCosted_value qualityRequiredMissingCosted_cost_le
  qualityStructureRequiredMissingCosted qualityStructureRequiredMissingCosted_value
  qualityStructureRequiredMissingCosted_cost_le
  qualityStructureEvidenceCosted qualityStructureEvidenceSpec
  qualityStructureEvidenceCosted_value qualityStructureEvidenceCosted_cost_le qualityStructureEvidenceCosted_size
  qualityEvidenceCosted qualityEvidenceCosted_value qualityEvidenceCosted_cost_le qualityEvidenceCosted_size
  quaIndividualTargetsCosted quaIndividualTargetsCosted_value
  quaIndividualTargetsCosted_sparse_value quaIndividualTargetsCosted_cost_le
  quaIndividualTargetsCosted_size_le quaIndividualTargetsCosted_nodup
  quaIndividualEvidenceCosted quaIndividualEvidenceCosted_value
  quaIndividualEvidenceCosted_cost_le quaIndividualEvidenceCosted_size
  quaIndividualRequiredMissingCosted quaIndividualRequiredMissingCosted_value
  quaIndividualRequiredMissingCosted_cost
  requiredMissingFallbackCosted requiredMissingFallbackCosted_value requiredMissingFallbackCosted_cost_le
  simpleQualityTypeRequiredMissingCosted
  complexQualityTypeRequiredMissingCosted
  simpleQualityTypeEvidenceCosted
  complexQualityTypeEvidenceCosted
  simpleQualityTypeRequiredMissingCosted_value
  simpleQualityTypeRequiredMissingCosted_cost_le
  complexQualityTypeRequiredMissingCosted_value
  complexQualityTypeRequiredMissingCosted_cost_le
  simpleQualityTypeEvidenceCosted_value
  simpleQualityTypeEvidenceCosted_cost_le
  simpleQualityTypeEvidenceCosted_size_le
  complexQualityTypeEvidenceCosted_value
  complexQualityTypeEvidenceCosted_cost_le
  complexQualityTypeEvidenceCosted_size_le
  simpleQualityRequiredMissingCosted
  complexQualityRequiredMissingCosted
  simpleQualityEvidenceCosted
  complexQualityEvidenceCosted
  simpleQualityRequiredMissingCosted_value
  simpleQualityRequiredMissingCosted_cost_le
  complexQualityRequiredMissingCosted_value
  complexQualityRequiredMissingCosted_cost_le
  simpleQualityEvidenceCosted_value
  simpleQualityEvidenceCosted_cost_le
  simpleQualityEvidenceCosted_size
  complexQualityEvidenceCosted_value
  complexQualityEvidenceCosted_cost_le
  complexQualityEvidenceCosted_size
  subsetRequiredMissingCosted
  subsetEvidenceCosted
  properSubsetRequiredMissingCosted
  properSubsetEvidenceCosted
  subsetRequiredMissingCosted_value
  subsetRequiredMissingCosted_cost_le
  subsetEvidenceCosted_value
  subsetEvidenceCosted_cost_le
  subsetEvidenceCosted_size_le
  properSubsetRequiredMissingCosted_value
  properSubsetRequiredMissingCosted_cost_le
  properSubsetEvidenceCosted_value
  properSubsetEvidenceCosted_cost_le
  properSubsetEvidenceCosted_size
  nonEmptySetRequiredMissingCosted
  nonEmptySetEvidenceCosted
  properSubRequiredMissingCosted
  properSubEvidenceCosted
  nonEmptySetRequiredMissingCosted_value
  nonEmptySetRequiredMissingCosted_cost
  nonEmptySetEvidenceCosted_value
  nonEmptySetEvidenceCosted_cost_le
  nonEmptySetEvidenceCosted_size
  properSubRequiredMissingCosted_value
  properSubRequiredMissingCosted_cost_le
  properSubEvidenceCosted_value
  properSubEvidenceCosted_cost_le
  properSubEvidenceCosted_size
  firstDeclaredOrInherenceCandidateCosted firstDeclaredOrInherenceCandidateCosted_value
  firstDeclaredOrInherenceCandidateCosted_cost_le
  externalModeRequiredMissingCosted externalModeRequiredMissingCosted_value
  externalModeRequiredMissingCosted_cost_le
  ultimateBearerRequiredMissingCosted ultimateBearerRequiredMissingCosted_cost_le
  ultimateBearerEvidenceCosted ultimateBearerEvidenceCosted_cost_le ultimateBearerEvidenceCosted_size
  externalModeEvidenceCosted externalModeEvidenceCosted_cost_le externalModeEvidenceCosted_size_le
  externallyDependentRequiredMissingCosted externallyDependentRequiredMissingCosted_cost_le
  externallyDependentEvidenceCosted externallyDependentEvidenceCosted_cost_le externallyDependentEvidenceCosted_size
  existentialDependenceRequiredMissingCosted existentialDependenceRequiredMissingCosted_cost_le
  existentialDependenceEvidenceCosted existentialDependenceEvidenceCosted_cost_le existentialDependenceEvidenceCosted_size
  existentialIndependenceRequiredMissingCosted existentialIndependenceRequiredMissingCosted_cost_le
  existentialIndependenceEvidenceCosted existentialIndependenceEvidenceCosted_cost_le existentialIndependenceEvidenceCosted_size
  categorizesRequiredMissingCosted
  categorizesEvidenceCosted
  disjointTypesRequiredMissingCosted
  disjointTypesEvidenceCosted
  completeCoverageRequiredMissingCosted
  completeCoverageEvidenceCosted
  partitionRequiredMissingCosted
  partitionEvidenceCosted
  categorizesRequiredMissingCosted_value
  categorizesRequiredMissingCosted_cost_le
  disjointTypesRequiredMissingCosted_value
  disjointTypesRequiredMissingCosted_cost_le
  completeCoverageRequiredMissingCosted_value
  completeCoverageRequiredMissingCosted_cost_le
  partitionRequiredMissingCosted_value
  partitionRequiredMissingCosted_cost_le
  categorizesEvidenceCosted_value
  categorizesEvidenceCosted_cost_le
  categorizesEvidenceCosted_size
  disjointTypesEvidenceCosted_value
  disjointTypesEvidenceCosted_cost_le
  disjointTypesEvidenceCosted_size
  completeCoverageEvidenceCosted_value
  completeCoverageEvidenceCosted_cost_le
  completeCoverageEvidenceCosted_size
  partitionEvidenceCosted_value
  partitionEvidenceCosted_cost_le
  partitionEvidenceCosted_size
  unreconstructedDerivedReportCosted unreconstructedDerivedReportCosted_value
  unreconstructedDerivedReportCosted_cost_le unreconstructedDerivedReportCosted_size
  from LeanUfo.UFO.DSL.Diagnostic.DerivedAssertions

-- A two-operation predicate adds three control operations on a false match,
-- four on the first true match, and three on the terminating second match.
example : Complexity.uniqueIndexCosted 0 (fun _ => .tick true 2) = ⟨none, 1⟩ := by native_decide
example : Complexity.uniqueIndexCosted 3 (fun _ => .tick false 2) = ⟨none, 16⟩ := by native_decide
example : Complexity.uniqueIndexCosted 3 (fun i => .tick (i == 1) 2) =
    ⟨some 1, 17⟩ := by native_decide
example : Complexity.uniqueIndexCosted 3 (fun i => .tick (i < 2) 2) =
    ⟨none, 11⟩ := by native_decide
example : Complexity.uniqueIndexCosted 100000 (fun _ => .tick true 2) =
    ⟨none, 11⟩ := by native_decide

example (W T : Nat) (tables : FactTables) (unary : UnaryField) (binary : BinaryField) (x w : Nat) :
    (uniqueRelatedThingCosted W T tables unary binary x w).cost ≤ 34 * T + 2 :=
  uniqueRelatedThingCosted_cost_le W T tables unary binary x w

example {smaller larger : Nat} (h : smaller ≤ larger) :
    34 * smaller + 2 ≤ 34 * larger + 2 := by omega

example (W T : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (unary : UnaryField) (binary : BinaryField) (x : Fin T) (w : Fin W) :
    (uniqueRelatedThingCosted W T tables unary binary x w).value =
      (((List.range T).filter fun y => tables.unaryLookup unary.toTableField y w &&
        tables.binaryLookup binary.toTableField x y w).length == 1) :=
  uniqueRelatedThingCosted_value W T tables agreement unary binary x w

private def twoThingTables (facts : Array CompiledFact) : FactTables :=
  compileExplicitModelAST { worldCount := 1, thingCount := 2, facts }

-- A failed classification skips the binary lookup: 16 per candidate, then
-- the domain-end and result-option tests. One complete match adds 18.
example : uniqueRelatedThingCosted 1 0 {} .qualityKind .inst 0 0 =
    ⟨false, 2⟩ := by native_decide
example : uniqueRelatedThingCosted 1 2 (twoThingTables #[]) .qualityKind .inst 0 0 =
    ⟨false, 34⟩ := by native_decide
example : uniqueRelatedThingCosted 1 2
    (twoThingTables #[.unary .qualityKind 1 0, .binary .inst 0 1 0])
    .qualityKind .inst 0 0 = ⟨true, 52⟩ := by native_decide
example : uniqueRelatedThingCosted 1 2
    (twoThingTables #[.unary .qualityKind 0 0, .binary .inst 0 0 0,
      .unary .qualityKind 1 0, .binary .inst 0 1 0])
    .qualityKind .inst 0 0 = ⟨false, 68⟩ := by native_decide

-- The two production predicates select different fields. Repeated facts
-- describe one relation cell and cannot create a second witness.
example : qualityLookup 1 2
    (twoThingTables #[.unary .qualityKind 1 0, .binary .inst 0 1 0,
      .binary .inst 0 1 0]) 0 0 = true := by native_decide
example : qualityStructureLookup 1 2
    (twoThingTables #[.unary .qualityKind 1 0, .binary .inst 0 1 0]) 0 0 = false := by native_decide
example : qualityStructureLookup 1 2
    (twoThingTables #[.unary .qualityType 1 0, .binary .associatedWith 0 1 0]) 0 0 = true :=
  by native_decide
example : qualityLookup 1 2
    (twoThingTables #[.unary .qualityType 1 0, .binary .associatedWith 0 1 0]) 0 0 = false :=
  by native_decide

example (W T : Nat) (tables : FactTables) (x w : Nat) :
    (simpleQualityLookupCosted W T tables x w).cost ≤ 55 * T + 4 :=
  simpleQualityLookupCosted_cost_le W T tables x w
example (W T : Nat) (tables : FactTables) (x w : Nat) :
    (complexQualityLookupCosted W T tables x w).cost ≤ 55 * T + 4 :=
  complexQualityLookupCosted_cost_le W T tables x w
example {smaller larger : Nat} (h : smaller ≤ larger) :
    55 * smaller + 4 ≤ 55 * larger + 4 := by omega

example (W T : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (x : Fin T) (w : Fin W) :
    (simpleQualityLookupCosted W T tables x w).value =
      (qualityLookup W T tables x w &&
        !((List.range T).any fun y => tables.binaryLookup "inheresIn" y x w)) :=
  simpleQualityLookupCosted_value W T tables agreement x w
example (W T : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (x : Fin T) (w : Fin W) :
    (complexQualityLookupCosted W T tables x w).value =
      (qualityLookup W T tables x w &&
        ((List.range T).any fun y => tables.binaryLookup "inheresIn" y x w)) :=
  complexQualityLookupCosted_value W T tables agreement x w

-- Failure of Quality skips inherence. Otherwise each inherence query costs
-- 21 including search control. An early match adds the three-operation stop.
example : simpleQualityLookupCosted 1 2 (twoThingTables #[]) 0 0 =
    ⟨false, 35⟩ := by native_decide
example : complexQualityLookupCosted 1 2 (twoThingTables #[]) 0 0 =
    ⟨false, 35⟩ := by native_decide
example : simpleQualityLookupCosted 1 2
    (twoThingTables #[.unary .qualityKind 1 0, .binary .inst 0 1 0]) 0 0 =
    ⟨true, 96⟩ := by native_decide
example : complexQualityLookupCosted 1 2
    (twoThingTables #[.unary .qualityKind 1 0, .binary .inst 0 1 0]) 0 0 =
    ⟨false, 96⟩ := by native_decide
example : simpleQualityLookupCosted 1 2
    (twoThingTables #[.unary .qualityKind 1 0, .binary .inst 0 1 0,
      .binary .inheresIn 0 0 0]) 0 0 = ⟨false, 78⟩ := by native_decide
example : complexQualityLookupCosted 1 2
    (twoThingTables #[.unary .qualityKind 1 0, .binary .inst 0 1 0,
      .binary .inheresIn 0 0 0]) 0 0 = ⟨true, 78⟩ := by native_decide
example : simpleQualityLookupCosted 1 2
    (twoThingTables #[.unary .qualityKind 1 0, .binary .inst 0 1 0,
      .binary .inheresIn 1 0 0]) 0 0 = ⟨false, 96⟩ := by native_decide
example : complexQualityLookupCosted 1 2
    (twoThingTables #[.unary .qualityKind 1 0, .binary .inst 0 1 0,
      .binary .inheresIn 1 0 0]) 0 0 = ⟨true, 96⟩ := by native_decide

example (W T : Nat) (tables : FactTables) (t w : Nat) :
    (qualityTypeInstancesCosted W T tables t w
      (fun x => simpleQualityLookupCosted W T tables x w)).cost ≤ T * (55 * T + 27) + 14 :=
  qualityTypeInstances_simple_cost_le W T tables t w
example (W T : Nat) (tables : FactTables) (t w : Nat) :
    (qualityTypeInstancesCosted W T tables t w
      (fun x => complexQualityLookupCosted W T tables x w)).cost ≤ T * (55 * T + 27) + 14 :=
  qualityTypeInstances_complex_cost_le W T tables t w
example {smaller larger : Nat} (h : smaller ≤ larger) :
    smaller * (55 * smaller + 27) + 14 ≤ larger * (55 * larger + 27) + 14 :=
  Nat.add_le_add_right (Nat.mul_le_mul h (by omega)) 14

example (W T : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (t : Fin T) (w : Fin W) (condition : Nat → Complexity.Costed Bool) :
    (qualityTypeInstancesCosted W T tables t w condition).value =
      (tables.unaryLookup "qualityType" t w &&
        !((List.range T).any fun x => tables.binaryLookup "inst" x t w && !(condition x).value)) :=
  qualityTypeInstancesCosted_value W T tables agreement t w condition

example (W T : Nat) (tables : FactTables) (t w : Nat)
    (condition : Nat → Complexity.Costed Bool) (P : Nat)
    (bounded : ∀ x, x < T → (condition x).cost ≤ P) :
    (qualityTypeInstancesCosted W T tables t w condition).cost ≤ T * (P + 23) + 14 :=
  qualityTypeInstancesCosted_cost_le W T tables t w condition P bounded

-- A false quality-type classification skips every instance. With a true
-- classification, non-instances skip the supplied condition even if it is
-- costly. These checks use a two-operation condition for visited instances.
example : qualityTypeInstancesCosted 1 2 (twoThingTables #[]) 1 0
    (fun _ => .tick false 100000) = ⟨false, 13⟩ := by native_decide
example : qualityTypeInstancesCosted 1 2 (twoThingTables #[.unary .qualityType 1 0]) 1 0
    (fun _ => .tick false 100000) = ⟨true, 58⟩ := by native_decide
example : qualityTypeInstancesCosted 1 2
    (twoThingTables #[.unary .qualityType 1 0, .binary .inst 0 1 0]) 1 0
    (fun _ => .tick false 2) = ⟨false, 42⟩ := by native_decide
example : qualityTypeInstancesCosted 1 2
    (twoThingTables #[.unary .qualityType 1 0, .binary .inst 1 1 0]) 1 0
    (fun _ => .tick false 2) = ⟨false, 61⟩ := by native_decide

example : qualityTypeInstancesCosted 1 2
    (twoThingTables #[.unary .qualityType 1 0, .unary .qualityKind 1 0, .binary .inst 0 1 0]) 1 0
    (fun x => simpleQualityLookupCosted 1 2
      (twoThingTables #[.unary .qualityType 1 0, .unary .qualityKind 1 0, .binary .inst 0 1 0]) x 0) =
    ⟨true, 155⟩ := by native_decide
example : qualityTypeInstancesCosted 1 2
    (twoThingTables #[.unary .qualityType 1 0, .unary .qualityKind 1 0, .binary .inst 0 1 0]) 1 0
    (fun x => complexQualityLookupCosted 1 2
      (twoThingTables #[.unary .qualityType 1 0, .unary .qualityKind 1 0, .binary .inst 0 1 0]) x 0) =
    ⟨false, 136⟩ := by native_decide
example : simpleQualityTypeLookup 1 2
    (twoThingTables #[.unary .qualityType 1 0, .unary .qualityKind 1 0,
      .binary .inst 0 1 0, .binary .inheresIn 0 0 0]) 1 0 = false := by native_decide
example : complexQualityTypeLookup 1 2
    (twoThingTables #[.unary .qualityType 1 0, .unary .qualityKind 1 0,
      .binary .inst 0 1 0, .binary .inheresIn 0 0 0]) 1 0 = true := by native_decide

-- Set predicates keep ascending witness order and skip right-hand queries
-- when the left relation is false. Each fully visited difference candidate
-- costs 40; a false left relation costs 22. The result-option test costs one.
example : nonEmptySetLookupCosted 1 0 {} 0 0 = ⟨false, 1⟩ := by native_decide
example : nonEmptySetLookupCosted 1 2 (twoThingTables #[]) 1 0 =
    ⟨false, 43⟩ := by native_decide
example : nonEmptySetLookupCosted 1 2 (twoThingTables #[.binary .memberOf 0 1 0]) 1 0 =
    ⟨true, 25⟩ := by native_decide
example : nonEmptySetLookupCosted 1 2 (twoThingTables #[.binary .memberOf 1 1 0]) 1 0 =
    ⟨true, 43⟩ := by native_decide
example : nonEmptySetLookupCosted 1 2 (twoThingTables #[.binary .inheresIn 0 1 0]) 1 0 =
    ⟨false, 43⟩ := by native_decide

example : subsetLookupCosted 1 0 {} 0 0 0 = ⟨true, 1⟩ := by native_decide
example : subsetLookupCosted 1 2 (twoThingTables #[]) 0 1 0 =
    ⟨true, 45⟩ := by native_decide
example : subsetLookupCosted 1 2 (twoThingTables #[.binary .memberOf 0 0 0]) 0 1 0 =
    ⟨false, 44⟩ := by native_decide
example : subsetLookupCosted 1 2 (twoThingTables #[.binary .memberOf 1 0 0]) 0 1 0 =
    ⟨false, 63⟩ := by native_decide
example : subsetLookupCosted 1 2
    (twoThingTables #[.binary .memberOf 0 0 0, .binary .memberOf 0 1 0]) 0 1 0 =
    ⟨true, 63⟩ := by native_decide

example : properSubsetLookupCosted 1 0 {} 0 0 0 = ⟨false, 3⟩ := by native_decide
example : properSubsetLookupCosted 1 2 (twoThingTables #[]) 0 1 0 =
    ⟨false, 91⟩ := by native_decide
example : properSubsetLookupCosted 1 2 (twoThingTables #[.binary .memberOf 0 1 0]) 0 1 0 =
    ⟨true, 90⟩ := by native_decide
example : properSubsetLookupCosted 1 2 (twoThingTables #[.binary .memberOf 0 0 0]) 0 1 0 =
    ⟨false, 45⟩ := by native_decide
example : properSubsetLookupCosted 1 2
    (twoThingTables #[.binary .memberOf 0 0 0, .binary .memberOf 0 1 0]) 0 1 0 =
    ⟨false, 127⟩ := by native_decide

example : properSubLookupCosted 1 2 (twoThingTables #[]) 0 1 0 =
    ⟨false, 18⟩ := by native_decide
example : properSubLookupCosted 1 2 (twoThingTables #[.binary .sub 0 1 0]) 0 1 0 =
    ⟨true, 36⟩ := by native_decide
example : properSubLookupCosted 1 2
    (twoThingTables #[.binary .sub 0 1 0, .binary .sub 1 0 0]) 0 1 0 =
    ⟨false, 36⟩ := by native_decide

-- Typehood searches worlds before things. Its first instance costs 21 in
-- this domain. A failed typehood test skips the categorization search.
example : categorizesLookupCosted 1 2 (twoThingTables #[]) 0 1 0 =
    ⟨false, 41⟩ := by native_decide
example : categorizesLookupCosted 1 2 (twoThingTables #[.binary .inst 0 0 0]) 0 1 0 =
    ⟨false, 66⟩ := by native_decide
example : categorizesLookupCosted 1 2 (twoThingTables #[.binary .inst 1 0 0]) 0 1 0 =
    ⟨false, 104⟩ := by native_decide
example : categorizesLookupCosted 1 2
    (twoThingTables #[.binary .inst 0 0 0, .binary .sub 0 1 0]) 0 1 0 =
    ⟨true, 85⟩ := by native_decide
-- Cross-world typehood costs 61, the conjunction costs one, and the empty
-- current-world difference search costs 44 plus its result test: 107 total.
example : categorizesLookupCosted 2 2
    (compileExplicitModelAST {
      worldCount := 2, thingCount := 2, facts := #[.binary .inst 0 0 1] }) 0 1 0 =
    ⟨true, 107⟩ := by native_decide

example (W T : Nat) (tables : FactTables) (s t w : Nat) :
    (subsetLookupCosted W T tables s t w).cost ≤ 40 * T + 1 :=
  subsetLookupCosted_cost_le W T tables s t w
example (W T : Nat) (tables : FactTables) (s t w : Nat) :
    (properSubsetLookupCosted W T tables s t w).cost ≤ 80 * T + 3 :=
  properSubsetLookupCosted_cost_le W T tables s t w
example (W T : Nat) (tables : FactTables) (x y w : Nat) :
    (properSubLookupCosted W T tables x y w).cost ≤ 36 :=
  properSubLookupCosted_cost_le W T tables x y w
example (W T : Nat) (tables : FactTables) (s w : Nat) :
    (nonEmptySetLookupCosted W T tables s w).cost ≤ 21 * T + 1 :=
  nonEmptySetLookupCosted_cost_le W T tables s w
example (W T : Nat) (tables : FactTables) (s t w : Nat) :
    (categorizesLookupCosted W T tables s t w).cost ≤ W * (T * 19 + 2) + 40 * T + 2 :=
  categorizesLookupCosted_cost_le W T tables s t w

example {W₁ W₂ T₁ T₂ : Nat} (hw : W₁ ≤ W₂) (ht : T₁ ≤ T₂) :
    W₁ * (T₁ * 19 + 2) + 40 * T₁ + 2 ≤ W₂ * (T₂ * 19 + 2) + 40 * T₂ + 2 := by
  have h := Nat.mul_le_mul hw (show T₁ * 19 + 2 ≤ T₂ * 19 + 2 by omega)
  omega

example (W T : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (s t : Fin T) (w : Fin W) :
    (subsetLookupCosted W T tables s t w).value =
      !((List.range T).any fun x => tables.binaryLookup "memberOf" x s w &&
        !tables.binaryLookup "memberOf" x t w) :=
  subsetLookupCosted_value W T tables agreement s t w
example (W T : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (s t : Fin T) (w : Fin W) :
    (properSubsetLookupCosted W T tables s t w).value =
      (subsetLookup W T tables s t w &&
        ((List.range T).any fun x => tables.binaryLookup "memberOf" x t w &&
          !tables.binaryLookup "memberOf" x s w)) :=
  properSubsetLookupCosted_value W T tables agreement s t w
example (W T : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (x y : Fin T) (w : Fin W) :
    (properSubLookupCosted W T tables x y w).value =
      (tables.binaryLookup "sub" x y w && !tables.binaryLookup "sub" y x w) :=
  properSubLookupCosted_value W T tables agreement x y w
example (W T : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (s : Fin T) (w : Fin W) :
    (nonEmptySetLookupCosted W T tables s w).value =
      ((List.range T).any fun x => tables.binaryLookup "memberOf" x s w) :=
  nonEmptySetLookupCosted_value W T tables agreement s w
example (W T : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (s t : Fin T) (w : Fin W) :
    (categorizesLookupCosted W T tables s t w).value =
      (typeLookup W T tables s &&
        !((List.range T).any fun x => tables.binaryLookup "inst" x s w &&
          !tables.binaryLookup "sub" x t w)) :=
  categorizesLookupCosted_value W T tables agreement s t w

private def threeTypeTables (facts : Array CompiledFact) : FactTables :=
  compileExplicitModelAST { worldCount := 1, thingCount := 3, facts }

-- Disjointness preserves the left-associated conjunction: a false first
-- typehood test still incurs both conjunction branches (59 + 2 here).
example : isDisjointWithLookupCosted 1 3 (threeTypeTables #[]) 0 1 0 =
    ⟨false, 61⟩ := by native_decide
example : isDisjointWithLookupCosted 1 3 (threeTypeTables #[.binary .inst 0 0 0]) 0 1 0 =
    ⟨false, 82⟩ := by native_decide
example : isDisjointWithLookupCosted 1 3
    (threeTypeTables #[.binary .inst 0 0 0, .binary .inst 1 1 0]) 0 1 0 =
    ⟨true, 147⟩ := by native_decide
example : isDisjointWithLookupCosted 1 3
    (threeTypeTables #[.binary .inst 0 0 0, .binary .inst 0 1 0]) 0 1 0 =
    ⟨false, 87⟩ := by native_decide
example : isDisjointWithLookupCosted 1 3
    (threeTypeTables #[.binary .inst 2 0 0, .binary .inst 2 1 0]) 0 1 0 =
    ⟨false, 204⟩ := by native_decide

-- A match in the first covering type skips the second covering query,
-- saving 17 operations. A counterexample ends the entire search.
example : isCompletelyCoveredByLookupCosted 1 3 (threeTypeTables #[]) 0 1 2 0 =
    ⟨true, 67⟩ := by native_decide
example : isCompletelyCoveredByLookupCosted 1 3
    (threeTypeTables #[.binary .inst 0 0 0]) 0 1 2 0 = ⟨false, 62⟩ := by native_decide
example : isCompletelyCoveredByLookupCosted 1 3
    (threeTypeTables #[.binary .inst 2 0 0]) 0 1 2 0 = ⟨false, 103⟩ := by native_decide
example : isCompletelyCoveredByLookupCosted 1 3
    (threeTypeTables #[.binary .inst 0 0 0, .binary .inst 0 1 0]) 0 1 2 0 =
    ⟨true, 86⟩ := by native_decide
example : isCompletelyCoveredByLookupCosted 1 3
    (threeTypeTables #[.binary .inst 0 0 0, .binary .inst 0 2 0]) 0 1 2 0 =
    ⟨true, 103⟩ := by native_decide

example : isPartitionedIntoLookupCosted 1 3
    (threeTypeTables #[.binary .inst 0 0 0]) 0 1 2 0 = ⟨false, 63⟩ := by native_decide
example : isPartitionedIntoLookupCosted 1 3 (threeTypeTables #[]) 0 1 2 0 =
    ⟨false, 129⟩ := by native_decide
example : isPartitionedIntoLookupCosted 1 3
    (threeTypeTables #[.binary .inst 0 1 0, .binary .inst 1 2 0]) 0 1 2 0 =
    ⟨true, 215⟩ := by native_decide

example (W T : Nat) (tables : FactTables) (s t w : Nat) :
    (isDisjointWithLookupCosted W T tables s t w).cost ≤
      2 * (W * (T * 19 + 2)) + 39 * T + 3 :=
  isDisjointWithLookupCosted_cost_le W T tables s t w
example (W T : Nat) (tables : FactTables) (s t u w : Nat) :
    (isCompletelyCoveredByLookupCosted W T tables s t u w).cost ≤ 58 * T + 1 :=
  isCompletelyCoveredByLookupCosted_cost_le W T tables s t u w
example (W T : Nat) (tables : FactTables) (s t u w : Nat) :
    (isPartitionedIntoLookupCosted W T tables s t u w).cost ≤
      2 * (W * (T * 19 + 2)) + 97 * T + 5 :=
  isPartitionedIntoLookupCosted_cost_le W T tables s t u w

example (W T : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (s t : Fin T) (w : Fin W) :
    (isDisjointWithLookupCosted W T tables s t w).value =
      (typeLookup W T tables s && typeLookup W T tables t &&
        !((List.range T).any fun x => tables.binaryLookup "inst" x s w &&
          tables.binaryLookup "inst" x t w)) :=
  isDisjointWithLookupCosted_value W T tables agreement s t w
example (W T : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (s t u : Fin T) (w : Fin W) :
    (isCompletelyCoveredByLookupCosted W T tables s t u w).value =
      !((List.range T).any fun x => tables.binaryLookup "inst" x s w &&
        !(tables.binaryLookup "inst" x t w || tables.binaryLookup "inst" x u w)) :=
  isCompletelyCoveredByLookupCosted_value W T tables agreement s t u w

example {W₁ W₂ T₁ T₂ : Nat} (hw : W₁ ≤ W₂) (ht : T₁ ≤ T₂) :
    2 * (W₁ * (T₁ * 19 + 2)) + 97 * T₁ + 5 ≤
      2 * (W₂ * (T₂ * 19 + 2)) + 97 * T₂ + 5 := by
  have h := Nat.mul_le_mul hw (show T₁ * 19 + 2 ≤ T₂ * 19 + 2 by omega)
  omega

example {W₁ W₂ T₁ T₂ : Nat} (hw : W₁ ≤ W₂) (ht : T₁ ≤ T₂) :
    (21 * T₁ + 1 ≤ 21 * T₂ + 1) ∧
    (40 * T₁ + 1 ≤ 40 * T₂ + 1) ∧
    (80 * T₁ + 3 ≤ 80 * T₂ + 3) ∧
    (58 * T₁ + 1 ≤ 58 * T₂ + 1) ∧
    (2 * (W₁ * (T₁ * 19 + 2)) + 39 * T₁ + 3 ≤
      2 * (W₂ * (T₂ * 19 + 2)) + 39 * T₂ + 3) := by
  have h := Nat.mul_le_mul hw (show T₁ * 19 + 2 ≤ T₂ * 19 + 2 by omega)
  omega

example (tables : FactTables) (T w m b : Nat) :
    (tables.momentOfClosureCosted T w m b).value = tables.momentOfClosure T w m b :=
  FactTables.momentOfClosureCosted_value tables T w m b
example (tables : FactTables) (T w m b : Nat) :
    (tables.momentOfClosureCosted T w m b).cost ≤ 6 :=
  FactTables.momentOfClosureCosted_cost_le tables T w m b

-- Missing matrices stop after the read and option test. A present matrix
-- adds index arithmetic, the cell read, and the cell-option test.
example : ({} : FactTables).momentOfClosureCosted 2 0 0 1 = ⟨false, 2⟩ := by native_decide
example : ({ inherenceClosures := #[#[]] } : FactTables).momentOfClosureCosted 2 0 0 1 =
    ⟨false, 6⟩ := by native_decide
example : ({ denseThingCount := 99, inherenceClosures := #[#[false, false, true, false]] } :
    FactTables).momentOfClosureCosted 2 0 1 0 = ⟨true, 6⟩ := by native_decide

example (W T : Nat) (tables : FactTables) (b m w : Nat) :
    (ultimateBearerOfLookupCosted W T tables b m w).cost ≤ 20 :=
  ultimateBearerOfLookupCosted_cost_le W T tables b m w
example (W T : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (b m : Fin T) (w : Fin W) :
    (ultimateBearerOfLookupCosted W T tables b m w).value =
      (!tables.unaryLookup "moment" b w && tables.momentOfClosure T w m b) :=
  ultimateBearerOfLookupCosted_value W T tables agreement b m w

example : ultimateBearerOfLookupCosted 1 2 {} 1 0 0 = ⟨false, 16⟩ := by native_decide
example : ultimateBearerOfLookupCosted 1 2 (twoThingTables #[]) 1 0 0 =
    ⟨false, 20⟩ := by native_decide
example : ultimateBearerOfLookupCosted 1 2
    (twoThingTables #[.binary .inheresIn 0 1 0]) 1 0 0 = ⟨true, 20⟩ := by native_decide
example : ultimateBearerOfLookupCosted 1 2
    (twoThingTables #[.binary .inheresIn 0 1 0, .unary .moment 1 0]) 1 0 0 =
    ⟨false, 14⟩ := by native_decide
example : ultimateBearerOfLookupCosted 1 3
    (threeTypeTables #[.binary .inheresIn 0 1 0, .binary .inheresIn 1 2 0]) 2 0 0 =
    ⟨true, 20⟩ := by native_decide
example : ultimateBearerOfLookupCosted 1 2
    (twoThingTables #[.binary .inheresIn 0 1 0, .binary .inheresIn 1 0 0]) 0 0 0 =
    ⟨true, 20⟩ := by native_decide

example (worldNames thingNames : Array Name) (tables : FactTables)
    (fact : NamedDerivedFact) (w : Nat) :
    (evalNamedDerivedFactCosted worldNames thingNames tables fact w).value =
      evalNamedDerivedFactSpec worldNames thingNames tables fact w :=
  evalNamedDerivedFactCosted_value worldNames thingNames tables fact w
example (worldNames thingNames : Array Name) (tables : FactTables)
    (fact : NamedDerivedFact) (w : Nat) :
    (evalNamedDerivedFactCosted worldNames thingNames tables fact w).cost ≤
      namedDerivedPredicateCostBound worldNames.size thingNames.size tables + 36 * thingNames.size + 19 :=
  evalNamedDerivedFactCosted_cost_le worldNames thingNames tables fact w

example {W₁ W₂ T₁ T₂ : Nat} (tables₁ tables₂ : FactTables)
    (hW : W₁ ≤ W₂) (hT : T₁ ≤ T₂)
    (hD : tables₁.derivedProps.size ≤ tables₂.derivedProps.size) :
    namedDerivedPredicateCostBound W₁ T₁ tables₁ + 36 * T₁ + 19 ≤
      namedDerivedPredicateCostBound W₂ T₂ tables₂ + 36 * T₂ + 19 := by
  have h := namedDerivedPredicateCostBound_mono tables₁ tables₂ hW hT hD
  omega

-- Missing names skip the continuation. Known unary/binary fields are tested
-- after name resolution. Unknown ternary/quaternary fields skip resolution.
example : withResolvedThingCosted #[] "x" (fun _ => .tick (some true) 100000) =
    ⟨none, 1⟩ := by native_decide
example : withResolvedThingCosted #[`x, `y] "missing" (fun _ => .tick (some true) 100000) =
    ⟨none, 19⟩ := by native_decide
example : withResolvedThingCosted #[`x, `y] "x" (fun _ => .tick (some true) 7) =
    ⟨some true, 20⟩ := by native_decide
example : evalNamedDerivedFactCosted #[`w] #[`x, `y] (twoThingTables #[])
    (.unary "Quality" "missing") 0 = ⟨none, 20⟩ := by native_decide
example : evalNamedDerivedFactCosted #[`w] #[`x, `y] (twoThingTables #[])
    (.binary "ProperSub" "x" "missing") 0 = ⟨none, 33⟩ := by native_decide
example : evalNamedDerivedFactCosted #[`w] #[`x, `y] (twoThingTables #[])
    (.ternary "unknown" "x" "y" "missing") 0 = ⟨none, 5⟩ := by native_decide
example : evalNamedDerivedFactCosted #[`w] #[`x, `y] (twoThingTables #[])
    (.quaternary "unknown" "x" "y" "x" "missing") 0 = ⟨none, 7⟩ := by native_decide
example : evalNamedDerivedFactCosted #[`w] #[`x, `y] (twoThingTables #[])
    (.ternary "IsCompletelyCoveredBy" "missing" "y" "y") 0 = ⟨none, 22⟩ := by native_decide
example : evalNamedDerivedFactCosted #[`w] #[`x, `y] (twoThingTables #[])
    (.quaternary "Constitution" "x" "y" "x" "missing") 0 = ⟨none, 71⟩ := by native_decide

-- Counts include the arity test, visited name searches and option tests,
-- field comparisons, and the selected predicate's full cost.
example : evalNamedDerivedFactCosted #[`w] #[`x, `y]
    (twoThingTables #[.unary .qualityKind 1 0, .binary .inst 0 1 0])
    (.unary "Quality" "x") 0 = ⟨some true, 68⟩ := by native_decide
example : evalNamedDerivedFactCosted #[`w] #[`x, `y] (twoThingTables #[])
    (.unary "NonEmptySet" "x") 0 = ⟨some false, 61⟩ := by native_decide
example : evalNamedDerivedFactCosted #[`w] #[`x, `y] (twoThingTables #[])
    (.unary "QualityStructure" "x") 0 = ⟨some false, 54⟩ := by native_decide
example : evalNamedDerivedFactCosted #[`w] #[`x, `y] (twoThingTables #[])
    (.unary "SimpleQuality" "x") 0 = ⟨some false, 57⟩ := by native_decide
example : evalNamedDerivedFactCosted #[`w] #[`x, `y] (twoThingTables #[])
    (.unary "ComplexQuality" "x") 0 = ⟨some false, 59⟩ := by native_decide
example : evalNamedDerivedFactCosted #[`w] #[`x, `y] (twoThingTables #[])
    (.unary "SimpleQualityType" "x") 0 = ⟨some false, 39⟩ := by native_decide
example : evalNamedDerivedFactCosted #[`w] #[`x, `y] (twoThingTables #[])
    (.unary "ComplexQualityType" "x") 0 = ⟨some false, 41⟩ := by native_decide
example : evalNamedDerivedFactCosted #[`w] #[`x, `y] (twoThingTables #[])
    (.binary "ProperSub" "x" "y") 0 = ⟨some false, 55⟩ := by native_decide
example : evalNamedDerivedFactCosted #[`w] #[`x, `y] (twoThingTables #[])
    (.binary "SubsetOf" "x" "y") 0 = ⟨some true, 84⟩ := by native_decide
example : evalNamedDerivedFactCosted #[`w] #[`x, `y] (twoThingTables #[])
    (.binary "ProperSubsetOf" "x" "y") 0 = ⟨some false, 132⟩ := by native_decide
example : evalNamedDerivedFactCosted #[`w] #[`x, `y] (twoThingTables #[])
    (.binary "IsDisjointWith" "x" "y") 0 = ⟨some false, 85⟩ := by native_decide
example : evalNamedDerivedFactCosted #[`w] #[`x, `y] (twoThingTables #[])
    (.binary "Categorizes" "x" "y") 0 = ⟨some false, 86⟩ := by native_decide
example : evalNamedDerivedFactCosted #[`w] #[`x, `y] (twoThingTables #[])
    (.ternary "IsCompletelyCoveredBy" "x" "y" "y") 0 = ⟨some true, 99⟩ := by native_decide

example (names : Array Name) (text : String) :
    (thingIndexByStringCosted names text).value =
      names.findIdx? (fun name => name.toString == text) :=
  thingIndexByStringCosted_value names text

example (names : Array Name) (text : String) :
    (thingIndexByStringCosted names text).cost ≤ 9 * names.size :=
  thingIndexByStringCosted_cost_le names text

example {smaller larger : Nat} (h : smaller ≤ larger) : 9 * smaller ≤ 9 * larger :=
  Nat.mul_le_mul_left 9 h

-- Each visited name costs nine. A match before the last entry adds three
-- for the next stop test, without reading or rendering the next name.
example : thingIndexByStringCosted #[] "x" = ⟨none, 0⟩ := by native_decide
example : thingIndexByStringCosted #[`x] "x" = ⟨some 0, 9⟩ := by native_decide
example : thingIndexByStringCosted #[`x, `y] "x" = ⟨some 0, 12⟩ := by native_decide
example : thingIndexByStringCosted #[`x, `y] "y" = ⟨some 1, 18⟩ := by native_decide
example : thingIndexByStringCosted #[`x, `y] "missing" = ⟨none, 18⟩ := by native_decide
example : thingIndexByStringCosted #[`x, `x] "x" = ⟨some 0, 12⟩ := by native_decide
example : thingIndexByStringCosted #[`x, `y] "X" = ⟨none, 18⟩ := by native_decide
example : thingIndexByStringCosted #[`left.one, `left.two] "left.two" =
    ⟨some 1, 18⟩ := by native_decide
example : thingIndexByStringCosted (Array.replicate 100000 `x) "x" =
    ⟨some 0, 12⟩ := by native_decide

-- With no derived assertion, the preliminary check has no failure report.
example : derivedAssertionFailure? #[`w] #[`x] #[] #[] {} = none := by native_decide
example : derivedAssertionFailure? #[`w] #[`x]
    #[.unary .moment "x" .everywhere] #[.unary .moment 0 .everywhere] {} = none :=
  by native_decide

private def qualityWithParts : FactTables :=
  twoThingTables #[.unary .qualityKind 1 0, .binary .inst 0 1 0,
    .binary .inheresIn 0 0 0, .binary .inheresIn 1 0 0]

example : (evalNamedDerivedFactCosted #[`w] #[`x, `kind] qualityWithParts
    (.unary "Quality" "x") 0).value = some true := by native_decide
example : (evalNamedDerivedFactCosted #[`w] #[`x, `kind] qualityWithParts
    (.unary "SimpleQuality" "x") 0).value = some false := by native_decide
example : (evalNamedDerivedFactCosted #[`w] #[`x, `kind] qualityWithParts
    (.unary "ComplexQuality" "x") 0).value = some true := by native_decide

-- Report selection retains the first inhering thing when two are available.
example : ((derivedAssertionFailure? #[`w] #[`x, `kind]
    #[.derived (.unary "SimpleQuality" "x") .everywhere]
    #[.derived (fun _ => "") .everywhere] qualityWithParts).getD #[])[1]? =
    some "Required but missing: `SimpleQuality(x)` requires no thing to inhere in it; conflicting `InheresIn(x, x)` is present." :=
  by native_decide
example : ((derivedAssertionFailure? #[`w] #[`x, `kind]
    #[.derived (.unary "SimpleQuality" "x") .everywhere]
    #[.derived (fun _ => "") .everywhere] qualityWithParts).getD #[])[5]? =
    some "  - Computed SimpleQuality: false, because `x` inheres in `x` at `w`." := by native_decide

example : ((derivedAssertionFailure? #[`w] #[`left, `right]
    #[.derived (.binary "SubsetOf" "left" "right") .everywhere]
    #[.derived (fun _ => "") .everywhere]
    (twoThingTables #[.binary .memberOf 0 0 0, .binary .memberOf 1 0 0])).getD #[])[5]? =
    some "  - Computed SubsetOf: false, because `left` is a member of `left` but not of `right` at `w`." :=
  by native_decide
example : ((derivedAssertionFailure? #[`w] #[`left, `right]
    #[.derived (.binary "IsDisjointWith" "left" "right") .everywhere]
    #[.derived (fun _ => "") .everywhere]
    (twoThingTables #[.binary .inst 0 0 0, .binary .inst 0 1 0,
      .binary .inst 1 0 0, .binary .inst 1 1 0])).getD #[])[5]? =
    some "  - Computed IsDisjointWith: false, because `left` instantiates both types at `w`." :=
  by native_decide

example : (evalNamedDerivedFactCosted #[`w] #[`x] {} (.unary "NonEmptySet" "x") 0).value =
    some false := by native_decide
example : (evalNamedDerivedFactCosted #[`w] #[`x] {} (.unary "NonEmptySet" "missing") 0).value =
    none := by native_decide
example : (evalNamedDerivedFactCosted #[`w] #[`x] {} (.ternary "Unknown" "x" "x" "x") 0).value =
    none := by native_decide

-- A scoped first fact fails at w1 before a later fact scoped to w0.
example : ((derivedAssertionFailure? #[`w0, `w1] #[`x]
    #[.derived (.unary "NonEmptySet" "x") (.at "w1"),
      .derived (.unary "NonEmptySet" "x") (.at "w0")]
    #[.derived (fun _ => "") (.at 1), .derived (fun _ => "") (.at 0)] {}).getD #[])[0]? =
    some "Counterexample assignment: w = w1." := by native_decide

-- Everywhere scope starts at the first world. No world means no check.
example : ((derivedAssertionFailure? #[`w0, `w1] #[`x]
    #[.derived (.unary "NonEmptySet" "x") .everywhere]
    #[.derived (fun _ => "") .everywhere] {}).getD #[])[0]? =
    some "Counterexample assignment: w = w0." := by native_decide
example : derivedAssertionFailure? #[] #[`x]
    #[.derived (.unary "NonEmptySet" "x") .everywhere]
    #[.derived (fun _ => "") .everywhere] {} = none := by native_decide

-- A missing result adds one option test. A Boolean result adds two tests.
example : failedDerivedAtCosted #[`w] #[`x, `y] (twoThingTables #[])
    (.ternary "unknown" "x" "y" "x") .everywhere 0 =
    ⟨some (FailedDerivedAssertion.mk (.ternary "unknown" "x" "y" "x") .everywhere 0 false), 6⟩ := by
  native_decide
example : failedDerivedAtCosted #[`w] #[`x, `y] (twoThingTables #[])
    (.unary "NonEmptySet" "x") .everywhere 0 =
    ⟨some (FailedDerivedAssertion.mk (.unary "NonEmptySet" "x") .everywhere 0 true), 63⟩ := by
  native_decide
example : failedDerivedAtCosted #[`w] #[`x, `y] (twoThingTables #[])
    (.binary "SubsetOf" "x" "y") .everywhere 0 = ⟨none, 86⟩ := by
  native_decide

-- Unknown ternary fields cost six per assignment regardless of table size.
-- The scope tag costs one. Each visited world adds three loop controls,
-- and an early failure adds the next stop test without evaluating that world.
example : firstScopedDerivedFailureCosted #[] #[] {}
    (.ternary "unknown" "x" "y" "z") .everywhere .everywhere = ⟨none, 1⟩ := by
  native_decide
example : firstScopedDerivedFailureCosted #[] #[] {}
    (.ternary "unknown" "x" "y" "z") (.at "w") (.at 7) =
    ⟨some (FailedDerivedAssertion.mk (.ternary "unknown" "x" "y" "z") (.at "w") 7 false), 7⟩ := by
  native_decide
example : firstScopedDerivedFailureCosted #[`w0] #[] {}
    (.ternary "unknown" "x" "y" "z") .everywhere .everywhere =
    ⟨some (FailedDerivedAssertion.mk (.ternary "unknown" "x" "y" "z") .everywhere 0 false), 10⟩ := by
  native_decide
example : firstScopedDerivedFailureCosted #[`w0, `w1] #[] {}
    (.ternary "unknown" "x" "y" "z") .everywhere .everywhere =
    ⟨some (FailedDerivedAssertion.mk (.ternary "unknown" "x" "y" "z") .everywhere 0 false), 13⟩ := by
  native_decide

-- Paired array reads cost two. Named and resolved constructor tests cost
-- at most four. Missing and non-derived pairs never evaluate an assertion.
example : firstDerivedFailureAtIndexCosted #[] #[] #[] #[] {} 0 =
    ⟨none, 3⟩ := by native_decide
example : firstDerivedAssertionFailureCosted #[] #[] #[] #[] {} =
    ⟨none, 0⟩ := by native_decide
example : firstDerivedAssertionFailureCosted #[] #[]
    #[.unary .moment "x" .everywhere] #[] {} = ⟨none, 7⟩ := by native_decide
example : firstDerivedAssertionFailureCosted #[] #[]
    #[.derived (.unary "Quality" "x") .everywhere] #[] {} =
    ⟨none, 8⟩ := by native_decide
example : firstDerivedAssertionFailureCosted #[] #[]
    #[.derived (.unary "Quality" "x") .everywhere]
    #[.unary .moment 0 .everywhere] {} = ⟨none, 9⟩ := by native_decide
example : firstDerivedAssertionFailureCosted #[] #[]
    #[.derived (.unary "Quality" "x") .everywhere]
    #[.derived (fun _ => "unused") .everywhere] {} = ⟨none, 10⟩ := by native_decide

-- The first source entry wins even if its world index is greater. A trailing
-- entry adds only the three-operation stop test. Its predicate is not run.
example : firstDerivedAssertionFailureCosted #[`w0, `w1] #[]
    #[.derived (.ternary "unknown" "x" "y" "z") (.at "w1"),
      .derived (.unary "Quality" "missing") (.at "w0")]
    #[.derived (fun _ => "unused") (.at 1), .derived (fun _ => "unused") (.at 0)] {} =
    ⟨some (FailedDerivedAssertion.mk (.ternary "unknown" "x" "y" "z") (.at "w1") 1 false), 19⟩ := by
  native_decide
example : (firstDerivedAssertionFailureCosted #[`w] #[]
    (Array.replicate 100000 (.derived (.ternary "unknown" "x" "y" "z") (.at "w")))
    #[.derived (fun _ => "unused") (.at 0)] {}).cost = 19 := by native_decide

-- A successful first world must not hide a failure at the last world.
-- The two assignment costs are 45 and 63, plus six loop controls and the scope tag.
example : firstScopedDerivedFailureCosted #[`w0, `w1] #[`x, `y]
    (compileExplicitModelAST { worldCount := 2, thingCount := 2, facts := #[.binary .memberOf 0 0 0] })
    (.unary "NonEmptySet" "x") .everywhere .everywhere =
    ⟨some (FailedDerivedAssertion.mk (.unary "NonEmptySet" "x") .everywhere 1 true), 115⟩ := by
  native_decide
example : firstScopedDerivedFailureCosted #[`w0, `w1] #[`x, `y]
    (compileExplicitModelAST { worldCount := 2, thingCount := 2, facts := #[] })
    (.binary "SubsetOf" "x" "y") .everywhere .everywhere = ⟨none, 179⟩ := by
  native_decide

example (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (scopedFacts : Array ScopedCompiledFact) (tables : FactTables) :
    (firstDerivedAssertionFailureCosted worldNames thingNames namedFacts scopedFacts tables).value =
      firstDerivedAssertionFailureSpec worldNames thingNames namedFacts scopedFacts tables :=
  firstDerivedAssertionFailureCosted_value _ _ _ _ _
example (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (scopedFacts : Array ScopedCompiledFact) (tables : FactTables) :
    (firstDerivedAssertionFailureCosted worldNames thingNames namedFacts scopedFacts tables).cost ≤
      namedFacts.size * (10 + (worldNames.size + 1) *
        (namedDerivedPredicateCostBound worldNames.size thingNames.size tables +
          36 * thingNames.size + 24)) :=
  firstDerivedAssertionFailureCosted_cost_le _ _ _ _ _
example {F₁ F₂ W₁ W₂ T₁ T₂ : Nat} (tables₁ tables₂ : FactTables)
    (hF : F₁ ≤ F₂) (hW : W₁ ≤ W₂) (hT : T₁ ≤ T₂)
    (hD : tables₁.derivedProps.size ≤ tables₂.derivedProps.size) :
    F₁ * (10 + (W₁ + 1) * (namedDerivedPredicateCostBound W₁ T₁ tables₁ + 36 * T₁ + 24)) ≤
    F₂ * (10 + (W₂ + 1) * (namedDerivedPredicateCostBound W₂ T₂ tables₂ + 36 * T₂ + 24)) :=
  firstDerivedAssertionFailureCostBound_mono tables₁ tables₂ hF hW hT hD

-- Report collectors retain all matches in order. A failed classification
-- costs 17 per candidate. A complete match costs 35, including the write.
example : relatedCandidatesCosted 0 0 {} .qualityKind .inst 0 0 =
    ⟨#[], 1⟩ := by native_decide
example : relatedCandidatesCosted 1 2 (twoThingTables #[]) .qualityKind .inst 0 0 =
    ⟨#[], 35⟩ := by native_decide
example : relatedCandidatesCosted 1 2
    (twoThingTables #[.unary .qualityKind 1 0, .binary .inst 0 1 0])
    .qualityKind .inst 0 0 = ⟨#[1], 53⟩ := by native_decide
example : relatedCandidatesCosted 1 2
    (twoThingTables #[.unary .qualityKind 1 0, .binary .inst 0 1 0,
      .unary .qualityKind 0 0, .binary .inst 0 0 0, .binary .inst 0 0 0])
    .qualityKind .inst 0 0 = ⟨#[0, 1], 71⟩ := by native_decide
example : relatedCandidatesCosted 1 2
    (twoThingTables #[.unary .qualityKind 1 0, .binary .inst 0 1 0])
    .qualityType .associatedWith 0 0 = ⟨#[], 35⟩ := by native_decide
example : relatedCandidatesCosted 1 2
    (twoThingTables #[.unary .qualityType 1 0, .binary .associatedWith 0 1 0])
    .qualityType .associatedWith 0 0 = ⟨#[1], 53⟩ := by native_decide

example (W T : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (classification : UnaryField) (relation : BinaryField) (x : Fin T) (w : Fin W) :
    (relatedCandidatesCosted W T tables classification relation x w).value =
      ((List.range T).filter fun y => tables.unaryLookup classification.toTableField y w &&
        tables.binaryLookup relation.toTableField x y w).toArray :=
  relatedCandidatesCosted_sparse_value W T tables agreement classification relation x w
example (W T : Nat) (tables : FactTables)
    (classification : UnaryField) (relation : BinaryField) (x w : Nat) :
    (relatedCandidatesCosted W T tables classification relation x w).cost ≤ 1 + 35 * T :=
  relatedCandidatesCosted_cost_le W T tables classification relation x w
example (W T : Nat) (tables : FactTables)
    (classification : UnaryField) (relation : BinaryField) (x w : Nat) :
    (relatedCandidatesCosted W T tables classification relation x w).value.size ≤ T :=
  relatedCandidatesCosted_size_le W T tables classification relation x w
example {T₁ T₂ : Nat} (hT : T₁ ≤ T₂) : 1 + 35 * T₁ ≤ 1 + 35 * T₂ := by omega

-- Ineligible sources skip the entire target search. Functional eligibility
-- adds one branch for its two-part source test: 23 per source versus 22.
example : firstFunctionalDependenceFailureCosted 0 0 {} 0 0 0 = ⟨none, 0⟩ := by native_decide
example : firstConstitutionalDependenceFailureCosted 0 0 {} 0 0 0 = ⟨none, 0⟩ := by native_decide
example : firstFunctionalDependenceFailureCosted 1 2 (twoThingTables #[]) 0 1 0 =
    ⟨none, 46⟩ := by native_decide
example : firstConstitutionalDependenceFailureCosted 1 2 (twoThingTables #[]) 0 1 0 =
    ⟨none, 44⟩ := by native_decide

-- The first eligible source fails after a full target scan. A remaining
-- source adds only the three-operation stop test. Last-source failures do not.
example : firstFunctionalDependenceFailureCosted 1 2
    (twoThingTables #[.binary .inst 0 0 0, .binary .functionsAs 0 0 0]) 0 1 0 =
    ⟨some 0, 71⟩ := by native_decide
example : firstFunctionalDependenceFailureCosted 1 2
    (twoThingTables #[.binary .inst 1 0 0, .binary .functionsAs 1 0 0]) 0 1 0 =
    ⟨some 1, 91⟩ := by native_decide
example : firstConstitutionalDependenceFailureCosted 1 2
    (twoThingTables #[.binary .inst 0 0 0]) 0 1 0 = ⟨some 0, 66⟩ := by native_decide
example : firstConstitutionalDependenceFailureCosted 1 2
    (twoThingTables #[.binary .inst 1 0 0]) 0 1 0 = ⟨some 1, 85⟩ := by native_decide

-- A source cannot witness its own functional dependence. Constitutional
-- dependence has no distinctness condition, and uses source-to-target direction.
example : firstFunctionalDependenceFailureCosted 1 2
    (twoThingTables #[.binary .inst 0 0 0, .binary .functionsAs 0 0 0,
      .binary .inst 0 1 0, .binary .functionsAs 0 1 0]) 0 1 0 =
    ⟨some 0, 71⟩ := by native_decide
example : firstConstitutionalDependenceFailureCosted 1 2
    (twoThingTables #[.binary .inst 0 0 0, .binary .inst 0 1 0,
      .binary .constitutedBy 0 0 0]) 0 1 0 = ⟨none, 82⟩ := by native_decide
example : firstConstitutionalDependenceFailureCosted 1 2
    (twoThingTables #[.binary .inst 0 0 0, .binary .inst 1 1 0,
      .binary .constitutedBy 1 0 0]) 0 1 0 = ⟨some 0, 83⟩ := by native_decide

-- First- and last-target witnesses both succeed. The first-target case skips
-- the other candidate. No list of target coordinates is built at runtime.
example : firstFunctionalDependenceFailureCosted 1 2
    (twoThingTables #[.binary .inst 0 0 0, .binary .functionsAs 0 0 0,
      .binary .inst 1 1 0, .binary .functionsAs 1 1 0]) 0 1 0 =
    ⟨none, 108⟩ := by native_decide
example : firstFunctionalDependenceFailureCosted 1 2
    (twoThingTables #[.binary .inst 1 0 0, .binary .functionsAs 1 0 0,
      .binary .inst 0 1 0, .binary .functionsAs 0 1 0]) 0 1 0 =
    ⟨none, 103⟩ := by native_decide
example : firstConstitutionalDependenceFailureCosted 1 2
    (twoThingTables #[.binary .inst 0 0 0, .binary .inst 1 1 0,
      .binary .constitutedBy 0 1 0]) 0 1 0 = ⟨none, 102⟩ := by native_decide

-- Public reports retain the first source witness when both sources fail.
example : ((derivedAssertionFailure? #[`w] #[`source, `target]
    #[.derived (.binary "GenericFunctionalDependence" "source" "target") .everywhere]
    #[.derived (fun _ => "unused") .everywhere]
    (twoThingTables #[.binary .inst 0 0 0, .binary .functionsAs 0 0 0,
      .binary .inst 1 0 0, .binary .functionsAs 1 0 0])).getD #[])[5]? =
    some "  - Computed GenericFunctionalDependence: false, because `source` instantiates and functions as `source` at `w`, but there is no distinct thing that instantiates and functions as `target`." := by
  native_decide
example : ((derivedAssertionFailure? #[`w] #[`source, `target]
    #[.derived (.binary "GenericConstitutionalDependence" "source" "target") .everywhere]
    #[.derived (fun _ => "unused") .everywhere]
    (twoThingTables #[.binary .inst 0 0 0, .binary .inst 1 0 0])).getD #[])[5]? =
    some "  - Computed GenericConstitutionalDependence: false, because `source` instantiates `source` at `w`, but no `target` instance is related by `ConstitutedBy(source, _)`." := by
  native_decide

example (W T : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (sourceType targetType : Fin T) (w : Fin W) :
    (firstFunctionalDependenceFailureCosted W T tables sourceType targetType w).value =
      (List.range T).find? (fun x =>
        (tables.binaryLookup "inst" x sourceType w &&
          tables.binaryLookup "functionsAs" x sourceType w) &&
        !((List.finRange T).any fun y =>
          (y.val != x && tables.binaryLookup "inst" y targetType w) &&
            tables.binaryLookup "functionsAs" y targetType w)) :=
  firstFunctionalDependenceFailureCosted_value W T tables agreement sourceType targetType w
example (W T : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (sourceType targetType : Fin T) (w : Fin W) :
    (firstConstitutionalDependenceFailureCosted W T tables sourceType targetType w).value =
      (List.range T).find? (fun x => tables.binaryLookup "inst" x sourceType w &&
        !((List.finRange T).any fun y => tables.binaryLookup "inst" y targetType w &&
          tables.binaryLookup "constitutedBy" x y w)) :=
  firstConstitutionalDependenceFailureCosted_value W T tables agreement sourceType targetType w
example (W T : Nat) (tables : FactTables) (sourceType targetType w : Nat) :
    (firstFunctionalDependenceFailureCosted W T tables sourceType targetType w).cost ≤
      T * (39 * T + 41) :=
  firstFunctionalDependenceFailureCosted_cost_le W T tables sourceType targetType w
example (W T : Nat) (tables : FactTables) (sourceType targetType w : Nat) :
    (firstConstitutionalDependenceFailureCosted W T tables sourceType targetType w).cost ≤
      T * (37 * T + 23) :=
  firstConstitutionalDependenceFailureCosted_cost_le W T tables sourceType targetType w
example {T₁ T₂ : Nat} (hT : T₁ ≤ T₂) :
    T₁ * (39 * T₁ + 41) ≤ T₂ * (39 * T₂ + 41) :=
  Nat.mul_le_mul hT (Nat.add_le_add_right (Nat.mul_le_mul_left 39 hT) 41)
example {T₁ T₂ : Nat} (hT : T₁ ≤ T₂) :
    T₁ * (37 * T₁ + 23) ≤ T₂ * (37 * T₂ + 23) :=
  Nat.mul_le_mul hT (Nat.add_le_add_right (Nat.mul_le_mul_left 37 hT) 23)

-- Every supported suggestion retains its literal and charges only visited
-- field tests. The four arities share the same one-operation tag test.
example : derivedAssertionSuggestionCosted (.unary "Quality" "unused") =
    ⟨derivedAssertionSuggestionSpec (.unary "Quality" "unused"), 3⟩ := by native_decide
example : derivedAssertionSuggestionCosted (.unary "ExternallyDependentMode" "unused") =
    ⟨derivedAssertionSuggestionSpec (.unary "ExternallyDependentMode" "unused"), 5⟩ := by native_decide
example : derivedAssertionSuggestionCosted (.unary "QuaIndividual" "unused") =
    ⟨derivedAssertionSuggestionSpec (.unary "QuaIndividual" "unused"), 7⟩ := by native_decide
example : derivedAssertionSuggestionCosted (.unary "NonEmptySet" "unused") =
    ⟨derivedAssertionSuggestionSpec (.unary "NonEmptySet" "unused"), 9⟩ := by native_decide
example : derivedAssertionSuggestionCosted (.unary "QualityStructure" "unused") =
    ⟨derivedAssertionSuggestionSpec (.unary "QualityStructure" "unused"), 11⟩ := by native_decide
example : derivedAssertionSuggestionCosted (.unary "SimpleQuality" "unused") =
    ⟨derivedAssertionSuggestionSpec (.unary "SimpleQuality" "unused"), 13⟩ := by native_decide
example : derivedAssertionSuggestionCosted (.unary "ComplexQuality" "unused") =
    ⟨derivedAssertionSuggestionSpec (.unary "ComplexQuality" "unused"), 15⟩ := by native_decide
example : derivedAssertionSuggestionCosted (.unary "SimpleQualityType" "unused") =
    ⟨derivedAssertionSuggestionSpec (.unary "SimpleQualityType" "unused"), 17⟩ := by native_decide
example : derivedAssertionSuggestionCosted (.unary "ComplexQualityType" "unused") =
    ⟨derivedAssertionSuggestionSpec (.unary "ComplexQualityType" "unused"), 19⟩ := by native_decide
example : derivedAssertionSuggestionCosted (.binary "ProperSub" "unused" "unused") =
    ⟨derivedAssertionSuggestionSpec (.binary "ProperSub" "unused" "unused"), 3⟩ := by native_decide
example : derivedAssertionSuggestionCosted (.binary "GenericFunctionalDependence" "unused" "unused") =
    ⟨derivedAssertionSuggestionSpec (.binary "GenericFunctionalDependence" "unused" "unused"), 5⟩ := by native_decide
example : derivedAssertionSuggestionCosted (.quaternary "IndividualFunctionalDependence" "unused" "unused" "unused" "unused") =
    ⟨derivedAssertionSuggestionSpec (.quaternary "IndividualFunctionalDependence" "unused" "unused" "unused" "unused"), 3⟩ := by native_decide
example : derivedAssertionSuggestionCosted (.quaternary "ComponentOf" "unused" "unused" "unused" "unused") =
    ⟨derivedAssertionSuggestionSpec (.quaternary "ComponentOf" "unused" "unused" "unused" "unused"), 5⟩ := by native_decide
example : derivedAssertionSuggestionCosted (.binary "GenericConstitutionalDependence" "unused" "unused") =
    ⟨derivedAssertionSuggestionSpec (.binary "GenericConstitutionalDependence" "unused" "unused"), 7⟩ := by native_decide
example : derivedAssertionSuggestionCosted (.quaternary "Constitution" "unused" "unused" "unused" "unused") =
    ⟨derivedAssertionSuggestionSpec (.quaternary "Constitution" "unused" "unused" "unused" "unused"), 7⟩ := by native_decide
example : derivedAssertionSuggestionCosted (.binary "ExternallyDependent" "unused" "unused") =
    ⟨derivedAssertionSuggestionSpec (.binary "ExternallyDependent" "unused" "unused"), 9⟩ := by native_decide
example : derivedAssertionSuggestionCosted (.binary "ExistentialDependence" "unused" "unused") =
    ⟨derivedAssertionSuggestionSpec (.binary "ExistentialDependence" "unused" "unused"), 11⟩ := by native_decide
example : derivedAssertionSuggestionCosted (.binary "ExistentialIndependence" "unused" "unused") =
    ⟨derivedAssertionSuggestionSpec (.binary "ExistentialIndependence" "unused" "unused"), 13⟩ := by native_decide
example : derivedAssertionSuggestionCosted (.binary "UltimateBearerOf" "unused" "unused") =
    ⟨derivedAssertionSuggestionSpec (.binary "UltimateBearerOf" "unused" "unused"), 15⟩ := by native_decide
example : derivedAssertionSuggestionCosted (.binary "SubsetOf" "unused" "unused") =
    ⟨derivedAssertionSuggestionSpec (.binary "SubsetOf" "unused" "unused"), 17⟩ := by native_decide
example : derivedAssertionSuggestionCosted (.binary "ProperSubsetOf" "unused" "unused") =
    ⟨derivedAssertionSuggestionSpec (.binary "ProperSubsetOf" "unused" "unused"), 19⟩ := by native_decide
example : derivedAssertionSuggestionCosted (.binary "IsDisjointWith" "unused" "unused") =
    ⟨derivedAssertionSuggestionSpec (.binary "IsDisjointWith" "unused" "unused"), 21⟩ := by native_decide
example : derivedAssertionSuggestionCosted (.ternary "IsCompletelyCoveredBy" "unused" "unused" "unused") =
    ⟨derivedAssertionSuggestionSpec (.ternary "IsCompletelyCoveredBy" "unused" "unused" "unused"), 3⟩ := by native_decide
example : derivedAssertionSuggestionCosted (.ternary "IsPartitionedInto" "unused" "unused" "unused") =
    ⟨derivedAssertionSuggestionSpec (.ternary "IsPartitionedInto" "unused" "unused" "unused"), 5⟩ := by native_decide
example : derivedAssertionSuggestionCosted (.binary "Categorizes" "unused" "unused") =
    ⟨derivedAssertionSuggestionSpec (.binary "Categorizes" "unused" "unused"), 23⟩ := by native_decide
example : (derivedAssertionSuggestionCosted (.unary "unknown" "unused")).cost =
    19 := by native_decide
example : (derivedAssertionSuggestionCosted (.binary "unknown" "unused" "unused")).cost =
    23 := by native_decide
example : (derivedAssertionSuggestionCosted (.ternary "unknown" "unused" "unused" "unused")).cost =
    5 := by native_decide
example : (derivedAssertionSuggestionCosted (.quaternary "unknown" "unused" "unused" "unused" "unused")).cost =
    7 := by native_decide

example (fact : NamedDerivedFact) :
    (derivedAssertionSuggestionCosted fact).value = derivedAssertionSuggestionSpec fact :=
  derivedAssertionSuggestionCosted_value fact
example (fact : NamedDerivedFact) : (derivedAssertionSuggestionCosted fact).cost ≤ 23 :=
  derivedAssertionSuggestionCosted_cost_le fact

-- The complete quality row includes candidate collection, indexed names,
-- size tests, text concatenations, array initialization, and one emitted row.
example : qualityStatusEvidenceCosted 0 #[] {} 7 0 =
    ⟨#["  - Computed Quality: false, because `#7` instantiates no `QualityKind` at this world."], 13⟩ := by
  native_decide
example : qualityStatusEvidenceCosted 1 #[`x, `kind] (twoThingTables #[]) 0 0 =
    ⟨#["  - Computed Quality: false, because `x` instantiates no `QualityKind` at this world."], 47⟩ := by
  native_decide
example : qualityStatusEvidenceCosted 1 #[`x, `kind]
    (twoThingTables #[.unary .qualityKind 1 0, .binary .inst 0 1 0]) 0 0 =
    ⟨#["  - Computed Quality: true, uniquely witnessed by `QualityKind(kind)` and `x :: kind`."], 77⟩ := by
  native_decide
example : qualityStatusEvidenceCosted 1 #[`x, `kind]
    (twoThingTables #[.unary .qualityKind 1 0, .binary .inst 0 1 0,
      .unary .qualityKind 0 0, .binary .inst 0 0 0]) 0 0 =
    ⟨#["  - Computed Quality: false, because `x` instantiates multiple quality kinds at this world: x, kind."], 105⟩ := by
  native_decide
example : qualityStatusEvidenceCosted 1 #[`x, `kind]
    (twoThingTables #[.unary .qualityKind 1 0, .binary .inst 0 1 0, .binary .inst 0 1 0]) 0 0 =
    ⟨#["  - Computed Quality: true, uniquely witnessed by `QualityKind(kind)` and `x :: kind`."], 77⟩ := by
  native_decide

example (W : Nat) (names : Array Name) (tables : FactTables) (x w : Nat) :
    (qualityStatusEvidenceCosted W names tables x w).value = qualityStatusEvidenceSpec W names tables x w :=
  qualityStatusEvidenceCosted_value W names tables x w
example (W : Nat) (names : Array Name) (tables : FactTables) (x w : Nat) :
    (qualityStatusEvidenceCosted W names tables x w).cost ≤ 44 * names.size + 25 :=
  qualityStatusEvidenceCosted_cost_le W names tables x w
example (W : Nat) (names : Array Name) (tables : FactTables) (x w : Nat) :
    (qualityStatusEvidenceCosted W names tables x w).value.size = 1 :=
  qualityStatusEvidenceCosted_size W names tables x w
example {T₁ T₂ : Nat} (h : T₁ ≤ T₂) : 44 * T₁ + 25 ≤ 44 * T₂ + 25 := by omega

-- Fallback text counts all summary and world-name work. Undeclared world
-- indices preserve the #n spelling and have the same four-operation name cost.
example : requiredMissingFallbackCosted #[`w] (.unary "Unknown" "x") 0 =
    ⟨"asserted derived relation `Unknown(x)` must be true under the computed semantics at `w`, but its definition evaluates to false.", 12⟩ := by
  native_decide
example : requiredMissingFallbackCosted #[] (.quaternary "Unknown" "a" "b" "c" "d") 7 =
    ⟨"asserted derived relation `Unknown(a, b, c, d)` must be true under the computed semantics at `#7`, but its definition evaluates to false.", 18⟩ := by
  native_decide

-- An unreconstructible relation emits two rows, with no names or tables to search.
example : unreconstructedDerivedReportCosted (.unary "Unknown" "x") =
    ⟨#["Could not reconstruct the asserted derived relation `Unknown(x)` at the DSL level.",
      "Suggestion: check that all mentioned things are declared and that the relation has a registered diagnostic evaluator."], 11⟩ := by
  native_decide
example : (unreconstructedDerivedReportCosted (.binary "Unknown" "x" "y")).cost = 13 := by
  native_decide
example : (unreconstructedDerivedReportCosted (.ternary "Unknown" "x" "y" "z")).cost = 15 := by
  native_decide
example : (unreconstructedDerivedReportCosted (.quaternary "Unknown" "a" "b" "c" "d")).cost = 17 := by
  native_decide
example : derivedAssertionFailure? #[`w] #[]
    #[.derived (.ternary "Unknown" "x" "y" "z") .everywhere]
    #[.derived (fun _ => "unused") .everywhere] {} =
    some #["Could not reconstruct the asserted derived relation `Unknown(x, y, z)` at the DSL level.",
      "Suggestion: check that all mentioned things are declared and that the relation has a registered diagnostic evaluator."] := by
  native_decide

example (names : Array Name) (fact : NamedDerivedFact) (w : Nat) :
    (requiredMissingFallbackCosted names fact w).value =
      s!"asserted derived relation `{namedDerivedFactSummary fact}` must be true under the computed semantics at `{indexedName names w}`, but its definition evaluates to false." :=
  requiredMissingFallbackCosted_value names fact w
example (names : Array Name) (fact : NamedDerivedFact) (w : Nat) :
    (requiredMissingFallbackCosted names fact w).cost ≤ 18 :=
  requiredMissingFallbackCosted_cost_le names fact w
example (fact : NamedDerivedFact) : (unreconstructedDerivedReportCosted fact).cost ≤ 17 :=
  unreconstructedDerivedReportCosted_cost_le fact
example (fact : NamedDerivedFact) : (unreconstructedDerivedReportCosted fact).value.size = 2 :=
  unreconstructedDerivedReportCosted_size fact

-- The checker and reports use the same first-invalid-instance search. An
-- instance costs 17 for lookup, one branch, the condition, one negation,
-- and four search controls. An early failure adds the three-operation stop.
example : firstInvalidInstanceCosted 0 0 {} 0 0 (fun _ => .tick false 100000) =
    ⟨none, 0⟩ := by native_decide
example : firstInvalidInstanceCosted 1 2 (twoThingTables #[]) 1 0
    (fun _ => .tick false 100000) = ⟨none, 44⟩ := by native_decide
example : firstInvalidInstanceCosted 1 2
    (twoThingTables #[.binary .inst 0 1 0, .binary .inst 1 1 0]) 1 0
    (fun x => .tick false (if x == 0 then 2 else 100000)) = ⟨some 0, 28⟩ := by
  native_decide
example : firstInvalidInstanceCosted 1 2
    (twoThingTables #[.binary .inst 1 1 0]) 1 0
    (fun _ => .tick false 2) = ⟨some 1, 47⟩ := by native_decide
example : firstInvalidInstanceCosted 1 2
    (twoThingTables #[.binary .inst 0 1 0, .binary .inst 1 1 0]) 1 0
    (fun x => .tick (x == 0) 2) = ⟨some 1, 50⟩ := by native_decide
example : firstInvalidInstanceCosted 1 2
    (twoThingTables #[.binary .inst 0 1 0, .binary .inst 1 1 0]) 1 0
    (fun _ => .tick true 2) = ⟨none, 50⟩ := by native_decide
example : firstInvalidInstanceCosted 1 2
    (twoThingTables #[.binary .inst 0 1 0, .binary .inst 0 1 0]) 1 0
    (fun _ => .tick false 2) = ⟨some 0, 28⟩ := by native_decide

example (W T : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (t : Fin T) (w : Fin W) (condition : Nat → Complexity.Costed Bool) :
    (firstInvalidInstanceCosted W T tables t w condition).value =
      (List.range T).find? (fun x => tables.binaryLookup "inst" x t w && !(condition x).value) :=
  firstInvalidInstanceCosted_value W T tables agreement t w condition
example (W T P : Nat) (tables : FactTables) (t w : Nat)
    (condition : Nat → Complexity.Costed Bool)
    (bounded : ∀ x, x < T → (condition x).cost ≤ P) :
    (firstInvalidInstanceCosted W T tables t w condition).cost ≤ T * (P + 23) :=
  firstInvalidInstanceCosted_cost_le W T tables t w condition P bounded
example (W T : Nat) (tables : FactTables) (t w : Nat) :
    (firstInvalidInstanceCosted W T tables t w
      (fun x => simpleQualityLookupCosted W T tables x w)).cost ≤ T * (55 * T + 27) :=
  firstInvalidInstance_simple_cost_le W T tables t w
example (W T : Nat) (tables : FactTables) (t w : Nat) :
    (firstInvalidInstanceCosted W T tables t w
      (fun x => complexQualityLookupCosted W T tables x w)).cost ≤ T * (55 * T + 27) :=
  firstInvalidInstance_complex_cost_le W T tables t w
example {T₁ T₂ P₁ P₂ : Nat} (ht : T₁ ≤ T₂) (hp : P₁ ≤ P₂) :
    T₁ * (P₁ + 23) ≤ T₂ * (P₂ + 23) :=
  Nat.mul_le_mul ht (Nat.add_le_add_right hp 23)
example {T₁ T₂ : Nat} (ht : T₁ ≤ T₂) :
    T₁ * (55 * T₁ + 27) ≤ T₂ * (55 * T₂ + 27) :=
  Nat.mul_le_mul ht (by omega)

-- Both reports must name the first invalid instance, even with two failures.
-- This exercises the public precheck and both required-missing/evidence rows.
example : ((derivedAssertionFailure? #[`w] #[`x, `kind]
    #[.derived (.unary "SimpleQualityType" "kind") .everywhere]
    #[.derived (fun _ => "unused") .everywhere]
    (twoThingTables #[.unary .qualityType 1 0, .binary .inst 0 1 0,
      .binary .inst 1 1 0])).getD #[])[1]? =
    some "Required but missing: `SimpleQualityType(kind)` requires every instance to be a computed `SimpleQuality`; instance `x` is not simple." := by native_decide
example : ((derivedAssertionFailure? #[`w] #[`x, `kind]
    #[.derived (.unary "SimpleQualityType" "kind") .everywhere]
    #[.derived (fun _ => "unused") .everywhere]
    (twoThingTables #[.unary .qualityType 1 0, .binary .inst 0 1 0,
      .binary .inst 1 1 0])).getD #[])[5]? =
    some "  - Computed SimpleQualityType: false, because instance `x` is not a computed `SimpleQuality` at `w`." := by native_decide
example : ((derivedAssertionFailure? #[`w] #[`x, `kind]
    #[.derived (.unary "ComplexQualityType" "kind") .everywhere]
    #[.derived (fun _ => "unused") .everywhere]
    (twoThingTables #[.unary .qualityType 1 0, .binary .inst 0 1 0,
      .binary .inst 1 1 0])).getD #[])[1]? =
    some "Required but missing: `ComplexQualityType(kind)` requires every instance to be a computed `ComplexQuality`; instance `x` is not complex." := by native_decide
example : ((derivedAssertionFailure? #[`w] #[`x, `kind]
    #[.derived (.unary "ComplexQualityType" "kind") .everywhere]
    #[.derived (fun _ => "unused") .everywhere]
    (twoThingTables #[.unary .qualityType 1 0, .binary .inst 0 1 0,
      .binary .inst 1 1 0])).getD #[])[5]? =
    some "  - Computed ComplexQualityType: false, because instance `x` is not a computed `ComplexQuality` at `w`." := by native_decide

-- The required-missing path has no thing-zero fallback. Collection costs 41
-- with two things and no stored assertions. Selection adds two, followed by
-- an inherence scan costing 24 for the first target or 42 for a full scan.
example : firstDeclaredOrInherenceCandidateCosted 0 0 {} 0 0 = ⟨none, 3⟩ := by native_decide
example : firstDeclaredOrInherenceCandidateCosted 1 2 (twoThingTables #[]) 0 0 =
    ⟨none, 85⟩ := by native_decide
example : firstDeclaredOrInherenceCandidateCosted 1 2
    (twoThingTables #[.binary .inheresIn 0 0 0, .binary .inheresIn 0 1 0]) 0 0 =
    ⟨some 0, 67⟩ := by native_decide
example : firstDeclaredOrInherenceCandidateCosted 1 2
    (twoThingTables #[.binary .inheresIn 0 1 0]) 0 0 = ⟨some 1, 85⟩ := by native_decide
example : firstDeclaredOrInherenceCandidateCosted 1 2
    (twoThingTables #[.binary .inheresIn 1 0 0]) 0 0 = ⟨none, 85⟩ := by native_decide

private def declaredModeFailureTables : FactTables :=
  { twoThingTables #[.unary .mode 0 0, .unary .ex 0 0, .binary .inheresIn 0 0 0] with
    derivedProps := #["sig.ExternallyDependent (⟨0, by decide⟩ : Fin data.thingCount) (⟨1, by decide⟩ : Fin data.thingCount) (⟨0, by decide⟩ : Fin data.worldCount)"] }

-- The declared target y takes precedence over the earlier inherence target x.
-- The collector costs 50; reading its first entry adds three and skips the scan.
example : firstDeclaredOrInherenceCandidateCosted 1 2 declaredModeFailureTables 0 0 =
    ⟨some 1, 53⟩ := by native_decide

-- A missing Mode uses one query (12), names (8), negation/branch (2), and
-- ten concatenations. No candidates or failure reasons are evaluated.
example : externalModeRequiredMissingCosted #[`w] #[`x, `y] (twoThingTables #[]) 0 0 =
    ⟨"`ExternallyDependentMode(x)` requires `Mode(x)` and some computed `ExternallyDependent(x, y)`; missing `Mode(x)` at `w`.", 32⟩ := by native_decide
example : (externalModeRequiredMissingCosted #[`w] #[`x, `y]
    { twoThingTables #[] with derivedProps := Array.replicate 1000 "unused" } 0 0).cost = 32 := by
  native_decide
example : externalModeRequiredMissingCosted #[] #[] {} 7 3 =
    ⟨"`ExternallyDependentMode(#7)` requires `Mode(#7)` and some computed `ExternallyDependent(#7, y)`; missing `Mode(#7)` at `#3`.", 22⟩ := by native_decide
example : externalModeRequiredMissingCosted #[`w] #[`x, `y]
    (twoThingTables #[.unary .mode 0 0]) 0 0 =
    ⟨"`ExternallyDependentMode(x)` requires `Mode(x)` and at least one computed `ExternallyDependent(x, y)`; missing any candidate witness and any relevant `InheresIn` bearer evidence.", 110⟩ := by native_decide

-- The missing Ex reason costs 49. The other work costs 32 plus candidate
-- selection: 85 through inherence, or 53 through the declared assertion.
example : externalModeRequiredMissingCosted #[`w] #[`x, `y]
    (twoThingTables #[.unary .mode 0 0, .unary .ex 0 0, .binary .inheresIn 0 1 0]) 0 0 =
    ⟨"`ExternallyDependentMode(x)` requires `Mode(x)` and at least one computed `ExternallyDependent(x, y)`; missing such a witness. Candidate `y` fails because `x` exists at `w`, but `y` does not; this breaks existential dependence.", 166⟩ := by native_decide
example : externalModeRequiredMissingCosted #[`w] #[`x, `y] declaredModeFailureTables 0 0 =
    ⟨"`ExternallyDependentMode(x)` requires `Mode(x)` and at least one computed `ExternallyDependent(x, y)`; missing such a witness. Candidate `y` fails because `x` exists at `w`, but `y` does not; this breaks existential dependence.", 134⟩ := by native_decide
example : ((derivedAssertionFailure? #[`w] #[`x, `y]
    #[.derived (.unary "ExternallyDependentMode" "x") .everywhere]
    #[.derived (fun _ => "unused") .everywhere] declaredModeFailureTables).getD #[])[1]? =
    some "Required but missing: `ExternallyDependentMode(x)` requires `Mode(x)` and at least one computed `ExternallyDependent(x, y)`; missing such a witness. Candidate `y` fails because `x` exists at `w`, but `y` does not; this breaks existential dependence." := by native_decide

example (W T : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (x : Fin T) (w : Fin W) :
    (firstDeclaredOrInherenceCandidateCosted W T tables x w).value =
      let declared := (declaredExternalCandidatesCosted T tables x w).value
      if h : 0 < declared.size then some declared[0] else
        (List.range T).find? (fun y => tables.binaryLookup "inheresIn" x y w) :=
  firstDeclaredOrInherenceCandidateCosted_value W T tables agreement x w
example (W T : Nat) (tables : FactTables) (x w : Nat) :
    (firstDeclaredOrInherenceCandidateCosted W T tables x w).cost ≤
      T * (4 * tables.derivedProps.size + 42) + 4 :=
  firstDeclaredOrInherenceCandidateCosted_cost_le W T tables x w
example (worlds things : Array Name) (tables : FactTables) (x w : Nat) :
    (externalModeRequiredMissingCosted worlds things tables x w).cost ≤
      things.size * (4 * tables.derivedProps.size + 42) +
        (30 * worlds.size + things.size * (60 * worlds.size + 40) + 28) + 36 :=
  externalModeRequiredMissingCosted_cost_le worlds things tables x w
example {W₁ W₂ T₁ T₂ D₁ D₂ : Nat} (hw : W₁ ≤ W₂) (ht : T₁ ≤ T₂) (hd : D₁ ≤ D₂) :
    T₁ * (4 * D₁ + 42) + (30 * W₁ + T₁ * (60 * W₁ + 40) + 28) + 36 ≤
      T₂ * (4 * D₂ + 42) + (30 * W₂ + T₂ * (60 * W₂ + 40) + 28) + 36 := by
  apply Nat.add_le_add_right
  apply Nat.add_le_add
  · exact Nat.mul_le_mul ht (by omega)
  · apply Nat.add_le_add_right
    exact Nat.add_le_add (by omega) (Nat.mul_le_mul ht (by omega))

-- QuaIndividualOf targets are collected in coordinate order. A query costs
-- 17, its branch one, an emitted index one, and each loop iteration three.
-- Array initialization costs one, including when the domain is empty.
example : quaIndividualTargetsCosted 0 0 {} 0 0 = ⟨#[], 1⟩ := by native_decide
example : quaIndividualTargetsCosted 1 2 (twoThingTables #[]) 0 0 = ⟨#[], 43⟩ := by native_decide
example : quaIndividualTargetsCosted 1 2
    (twoThingTables #[.binary .quaIndividualOf 0 1 0]) 0 0 = ⟨#[1], 44⟩ := by native_decide
example : quaIndividualTargetsCosted 1 2
    (twoThingTables #[.binary .quaIndividualOf 0 1 0, .binary .quaIndividualOf 0 0 0,
      .binary .quaIndividualOf 0 1 0]) 0 0 = ⟨#[0, 1], 45⟩ := by native_decide
example : quaIndividualTargetsCosted 1 2
    (twoThingTables #[.binary .quaIndividualOf 1 0 0, .binary .inheresIn 0 1 0]) 0 0 =
    ⟨#[], 43⟩ := by native_decide

-- Both evidence rows include source-name rendering and row emission. Joining
-- target names runs only for nonempty results and retains duplicate spellings.
example : quaIndividualEvidenceCosted 0 #[] {} 7 0 =
    ⟨#["  - User assertion: `QuaIndividual(#7)`.",
      "  - Computed QuaIndividual: false, because no `QuaIndividualOf` fact has this thing on the left."], 15⟩ := by native_decide
example : quaIndividualEvidenceCosted 1 #[`x, `y] (twoThingTables #[]) 0 0 =
    ⟨#["  - User assertion: `QuaIndividual(x)`.",
      "  - Computed QuaIndividual: false, because no `QuaIndividualOf` fact has this thing on the left."], 57⟩ := by native_decide
example : quaIndividualEvidenceCosted 1 #[`x, `y]
    (twoThingTables #[.binary .quaIndividualOf 0 1 0]) 0 0 =
    ⟨#["  - User assertion: `QuaIndividual(x)`.",
      "  - `QuaIndividualOf` candidate(s) exist: y; inspect the corresponding §3.10 foundation diagnostics if certification still fails."], 68⟩ := by native_decide
example : quaIndividualEvidenceCosted 1 #[`x, `y]
    (twoThingTables #[.binary .quaIndividualOf 0 1 0, .binary .quaIndividualOf 0 0 0]) 0 0 =
    ⟨#["  - User assertion: `QuaIndividual(x)`.",
      "  - `QuaIndividualOf` candidate(s) exist: x, y; inspect the corresponding §3.10 foundation diagnostics if certification still fails."], 78⟩ := by native_decide
example : quaIndividualEvidenceCosted 1 #[`same, `same]
    (twoThingTables #[.binary .quaIndividualOf 0 1 0, .binary .quaIndividualOf 0 0 0]) 0 0 =
    ⟨#["  - User assertion: `QuaIndividual(same)`.",
      "  - `QuaIndividualOf` candidate(s) exist: same, same; inspect the corresponding §3.10 foundation diagnostics if certification still fails."], 78⟩ := by native_decide
example : quaIndividualRequiredMissingCosted #[`w] #[`x] 0 0 =
    ⟨"`QuaIndividual(x)` requires some `QuaIndividualOf(x, y)`; missing any such fact at `w`.", 14⟩ := by native_decide
example : quaIndividualRequiredMissingCosted #[] #[] 7 3 =
    ⟨"`QuaIndividual(#7)` requires some `QuaIndividualOf(#7, y)`; missing any such fact at `#3`.", 14⟩ := by native_decide

example : ((derivedAssertionFailure? #[`w] #[`x, `y]
    #[.derived (.unary "QuaIndividual" "x") .everywhere]
    #[.derived (fun _ => "unused") .everywhere] (twoThingTables #[])).getD #[])[1]? =
    some "Required but missing: `QuaIndividual(x)` requires some `QuaIndividualOf(x, y)`; missing any such fact at `w`." := by native_decide
example : ((derivedAssertionFailure? #[`w] #[`x, `y]
    #[.derived (.unary "QuaIndividual" "x") .everywhere]
    #[.derived (fun _ => "unused") .everywhere] (twoThingTables #[])).getD #[])[5]? =
    some "  - Computed QuaIndividual: false, because no `QuaIndividualOf` fact has this thing on the left." := by native_decide

example (W T : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (x : Fin T) (w : Fin W) :
    (quaIndividualTargetsCosted W T tables x w).value =
      ((List.range T).filter fun y => tables.binaryLookup "quaIndividualOf" x y w).toArray :=
  quaIndividualTargetsCosted_sparse_value W T tables agreement x w
example (W T : Nat) (tables : FactTables) (x w : Nat) :
    (quaIndividualTargetsCosted W T tables x w).cost ≤ 22 * T + 1 :=
  quaIndividualTargetsCosted_cost_le W T tables x w
example (W T : Nat) (tables : FactTables) (x w : Nat) :
    (quaIndividualTargetsCosted W T tables x w).value.size ≤ T :=
  quaIndividualTargetsCosted_size_le W T tables x w
example (W T : Nat) (tables : FactTables) (x w : Nat) :
    (quaIndividualTargetsCosted W T tables x w).value.toList.Nodup :=
  quaIndividualTargetsCosted_nodup W T tables x w
example (W : Nat) (names : Array Name) (tables : FactTables) (x w : Nat) :
    (quaIndividualEvidenceCosted W names tables x w).cost ≤ 31 * names.size + 18 :=
  quaIndividualEvidenceCosted_cost_le W names tables x w
example (W : Nat) (names : Array Name) (tables : FactTables) (x w : Nat) :
    (quaIndividualEvidenceCosted W names tables x w).value.size = 2 :=
  quaIndividualEvidenceCosted_size W names tables x w
example (worlds things : Array Name) (x w : Nat) :
    (quaIndividualRequiredMissingCosted worlds things x w).cost = 14 :=
  quaIndividualRequiredMissingCosted_cost worlds things x w
example {T₁ T₂ : Nat} (h : T₁ ≤ T₂) : 31 * T₁ + 18 ≤ 31 * T₂ + 18 := by omega


-- Complete quality explanations include candidate collection, names, size
-- tests, and each text concatenation. The required-missing format is called
-- after a failed assertion; these fixtures exercise absent and competing kinds.
example : qualityRequiredMissingCosted #[`w] #[`x, `y] (twoThingTables #[]) 0 0 =
    ⟨"`Quality(x)` requires exactly one `QualityKind` instantiation; missing any `QualityKind(k)` with `x :: k` at `w`.", 52⟩ := by native_decide
example : qualityRequiredMissingCosted #[`w] #[`x, `y] (twoThingTables #[.unary .qualityKind 1 0, .binary .inst 0 1 0,
      .unary .qualityKind 0 0, .binary .inst 0 0 0]) 0 0 =
    ⟨"`Quality(x)` requires exactly one `QualityKind` instantiation; found competing quality kinds x, y at `w`.", 105⟩ := by native_decide
example : qualityRequiredMissingCosted #[] #[] {} 7 3 =
    ⟨"`Quality(#7)` requires exactly one `QualityKind` instantiation; missing any `QualityKind(k)` with `#7 :: k` at `#3`.", 18⟩ := by native_decide
example : qualityStructureRequiredMissingCosted #[`w] #[`x, `y] (twoThingTables #[]) 0 0 =
    ⟨"`QualityStructure(x)` requires exactly one associated `QualityType`; missing any `AssociatedWith(x, t)` where `QualityType(t)` holds.", 46⟩ := by native_decide
example : qualityStructureRequiredMissingCosted #[`w] #[`x, `y] (twoThingTables #[.unary .qualityType 1 0, .binary .associatedWith 0 1 0,
      .unary .qualityType 0 0, .binary .associatedWith 0 0 0]) 0 0 =
    ⟨"`QualityStructure(x)` requires exactly one associated `QualityType`; found competing associated quality types x, y.", 99⟩ := by native_decide
example : qualityStructureRequiredMissingCosted #[] #[] {} 7 3 =
    ⟨"`QualityStructure(#7)` requires exactly one associated `QualityType`; missing any `AssociatedWith(#7, t)` where `QualityType(t)` holds.", 12⟩ := by native_decide

-- The assertion row precedes the status row. Quality copies one status row
-- at cost three, in addition to the nine operations for its assertion row.
example : qualityEvidenceCosted 1 #[`x, `y] (twoThingTables #[]) 0 0 =
    ⟨#["  - User assertion: `Quality(x)`.",
      "  - Computed Quality: false, because `x` instantiates no `QualityKind` at this world."], 59⟩ := by native_decide
example : qualityEvidenceCosted 1 #[`x, `y] (twoThingTables #[.unary .qualityKind 1 0, .binary .inst 0 1 0]) 0 0 =
    ⟨#["  - User assertion: `Quality(x)`.",
      "  - Computed Quality: true, uniquely witnessed by `QualityKind(y)` and `x :: y`."], 89⟩ := by native_decide
example : qualityEvidenceCosted 1 #[`x, `y] (twoThingTables #[.unary .qualityKind 1 0, .binary .inst 0 1 0,
      .unary .qualityKind 0 0, .binary .inst 0 0 0]) 0 0 =
    ⟨#["  - User assertion: `Quality(x)`.",
      "  - Computed Quality: false, because `x` instantiates multiple quality kinds at this world: x, y."], 117⟩ := by native_decide
example : qualityEvidenceCosted 0 #[] {} 7 3 =
    ⟨#["  - User assertion: `Quality(#7)`.",
      "  - Computed Quality: false, because `#7` instantiates no `QualityKind` at this world."], 25⟩ := by native_decide
example : qualityStructureEvidenceCosted #[`w] #[`x, `y] (twoThingTables #[]) 0 0 =
    ⟨#["  - User assertion: `QualityStructure(x)`.",
      "  - Computed QualityStructure: false, because `x` is not associated with any `QualityType` at `w`."], 57⟩ := by native_decide
example : qualityStructureEvidenceCosted #[`w] #[`x, `y] (twoThingTables #[.unary .qualityType 1 0, .binary .associatedWith 0 1 0]) 0 0 =
    ⟨#["  - User assertion: `QualityStructure(x)`.",
      "  - Computed QualityStructure: true, uniquely associated with `y`."], 77⟩ := by native_decide
example : qualityStructureEvidenceCosted #[`w] #[`x, `y] (twoThingTables #[.unary .qualityType 1 0, .binary .associatedWith 0 1 0,
      .unary .qualityType 0 0, .binary .associatedWith 0 0 0]) 0 0 =
    ⟨#["  - User assertion: `QualityStructure(x)`.",
      "  - Computed QualityStructure: false, because multiple associated quality types are present: x, y."], 107⟩ := by native_decide
example : qualityStructureEvidenceCosted #[] #[] {} 7 3 =
    ⟨#["  - User assertion: `QualityStructure(#7)`.",
      "  - Computed QualityStructure: false, because `#7` is not associated with any `QualityType` at `#3`."], 23⟩ := by native_decide
example : qualityStructureEvidenceCosted #[`w] #[`same, `same] (twoThingTables #[.unary .qualityType 1 0, .binary .associatedWith 0 1 0,
      .unary .qualityType 0 0, .binary .associatedWith 0 0 0]) 0 0 =
    ⟨#["  - User assertion: `QualityStructure(same)`.",
      "  - Computed QualityStructure: false, because multiple associated quality types are present: same, same."], 107⟩ := by native_decide

example (worlds things : Array Name) (tables : FactTables) (x w : Nat) :
    (qualityRequiredMissingCosted worlds things tables x w).cost ≤ 44 * things.size + 19 :=
  qualityRequiredMissingCosted_cost_le worlds things tables x w
example (worlds things : Array Name) (tables : FactTables) (x w : Nat) :
    (qualityStructureRequiredMissingCosted worlds things tables x w).cost ≤ 44 * things.size + 13 :=
  qualityStructureRequiredMissingCosted_cost_le worlds things tables x w
example (worlds things : Array Name) (tables : FactTables) (x w : Nat) :
    (qualityEvidenceCosted worlds.size things tables x w).cost ≤ 44 * things.size + 37 :=
  qualityEvidenceCosted_cost_le worlds.size things tables x w
example (worlds things : Array Name) (tables : FactTables) (x w : Nat) :
    (qualityStructureEvidenceCosted worlds things tables x w).cost ≤ 44 * things.size + 25 :=
  qualityStructureEvidenceCosted_cost_le worlds things tables x w
example (worlds things : Array Name) (tables : FactTables) (x w : Nat) :
    (qualityStructureEvidenceCosted worlds things tables x w).value =
      qualityStructureEvidenceSpec worlds things tables x w :=
  qualityStructureEvidenceCosted_value worlds things tables x w
example (W : Nat) (things : Array Name) (tables : FactTables) (x w : Nat) :
    (qualityEvidenceCosted W things tables x w).value =
      #[s!"  - User assertion: `Quality({indexedName things x})`."] ++ qualityStatusEvidenceSpec W things tables x w :=
  qualityEvidenceCosted_value W things tables x w
example (worlds things : Array Name) (tables : FactTables) (x w : Nat) :
    (qualityStructureEvidenceCosted worlds things tables x w).value.size = 2 :=
  qualityStructureEvidenceCosted_size worlds things tables x w
example (W : Nat) (things : Array Name) (tables : FactTables) (x w : Nat) :
    (qualityEvidenceCosted W things tables x w).value.size = 2 :=
  qualityEvidenceCosted_size W things tables x w
example {T₁ T₂ C : Nat} (h : T₁ ≤ T₂) : 44 * T₁ + C ≤ 44 * T₂ + C := by omega

example : ((derivedAssertionFailure? #[`w] #[`x, `y]
    #[.derived (.unary "Quality" "x") .everywhere]
    #[.derived (fun _ => "unused") .everywhere] (twoThingTables #[.unary .qualityKind 1 0, .binary .inst 0 1 0,
      .unary .qualityKind 0 0, .binary .inst 0 0 0])).getD #[])[1]? =
    some "Required but missing: `Quality(x)` requires exactly one `QualityKind` instantiation; found competing quality kinds x, y at `w`." := by native_decide
example : ((derivedAssertionFailure? #[`w] #[`x, `y]
    #[.derived (.unary "Quality" "x") .everywhere]
    #[.derived (fun _ => "unused") .everywhere] (twoThingTables #[.unary .qualityKind 1 0, .binary .inst 0 1 0,
      .unary .qualityKind 0 0, .binary .inst 0 0 0])).getD #[])[5]? =
    some "  - Computed Quality: false, because `x` instantiates multiple quality kinds at this world: x, y." := by native_decide
example : ((derivedAssertionFailure? #[`w] #[`x, `y]
    #[.derived (.unary "QualityStructure" "x") .everywhere]
    #[.derived (fun _ => "unused") .everywhere] (twoThingTables #[.unary .qualityType 1 0, .binary .associatedWith 0 1 0,
      .unary .qualityType 0 0, .binary .associatedWith 0 0 0])).getD #[])[1]? =
    some "Required but missing: `QualityStructure(x)` requires exactly one associated `QualityType`; found competing associated quality types x, y." := by native_decide
example : ((derivedAssertionFailure? #[`w] #[`x, `y]
    #[.derived (.unary "QualityStructure" "x") .everywhere]
    #[.derived (fun _ => "unused") .everywhere] (twoThingTables #[.unary .qualityType 1 0, .binary .associatedWith 0 1 0,
      .unary .qualityType 0 0, .binary .associatedWith 0 0 0])).getD #[])[5]? =
    some "  - Computed QualityStructure: false, because multiple associated quality types are present: x, y." := by native_decide

-- Member evidence keeps the first incoming MemberOf edge. A selected member
-- adds six rendering operations to the empty-case cost of 20.
example : nonEmptySetEvidenceCosted #[`w] #[`x, `y] (twoThingTables #[]) 0 0 =
    ⟨#["  - User assertion: `NonEmptySet(x)`.", "  - Computed NonEmptySet: false, because no `MemberOf(_, x)` fact holds at `w`."], 62⟩ := by native_decide
example : nonEmptySetEvidenceCosted #[`w] #[`x, `y] (twoThingTables #[.binary .memberOf 0 0 0]) 0 0 =
    ⟨#["  - User assertion: `NonEmptySet(x)`.", "  - Computed NonEmptySet: true, witnessed by `MemberOf(x, x)` at `w`."], 50⟩ := by native_decide
example : nonEmptySetEvidenceCosted #[`w] #[`x, `y] (twoThingTables #[.binary .memberOf 1 0 0]) 0 0 =
    ⟨#["  - User assertion: `NonEmptySet(x)`.", "  - Computed NonEmptySet: true, witnessed by `MemberOf(y, x)` at `w`."], 68⟩ := by native_decide
example : nonEmptySetEvidenceCosted #[`w] #[`x, `y] (twoThingTables #[.binary .memberOf 1 0 0, .binary .memberOf 0 0 0]) 0 0 =
    ⟨#["  - User assertion: `NonEmptySet(x)`.", "  - Computed NonEmptySet: true, witnessed by `MemberOf(x, x)` at `w`."], 50⟩ := by native_decide
example : nonEmptySetEvidenceCosted #[`w] #[`x, `y] (twoThingTables #[.binary .memberOf 1 0 0, .binary .memberOf 1 0 0]) 0 0 =
    ⟨#["  - User assertion: `NonEmptySet(x)`.", "  - Computed NonEmptySet: true, witnessed by `MemberOf(y, x)` at `w`."], 68⟩ := by native_decide
example : nonEmptySetEvidenceCosted #[`w] #[`x, `y] (twoThingTables #[.binary .memberOf 0 1 0, .binary .sub 1 0 0]) 0 0 =
    ⟨#["  - User assertion: `NonEmptySet(x)`.", "  - Computed NonEmptySet: false, because no `MemberOf(_, x)` fact holds at `w`."], 62⟩ := by native_decide
example : nonEmptySetEvidenceCosted #[] #[] {} 7 3 =
    ⟨#["  - User assertion: `NonEmptySet(#7)`.", "  - Computed NonEmptySet: false, because no `MemberOf(_, #7)` fact holds at `#3`."], 20⟩ := by native_decide
example : nonEmptySetRequiredMissingCosted #[`w] #[`x] 0 0 =
    ⟨"`NonEmptySet(x)` requires some `MemberOf(member, x)`; missing any member at `w`.", 14⟩ := by native_decide
example : nonEmptySetRequiredMissingCosted #[] #[] 7 3 =
    ⟨"`NonEmptySet(#7)` requires some `MemberOf(member, #7)`; missing any member at `#3`.", 14⟩ := by native_decide

-- Both directed Sub queries run in every evidence case: 34 query operations
-- plus 33 for names, text, Boolean branches, and the three output rows.
example : properSubEvidenceCosted #[`w] #[`x, `y] (twoThingTables #[]) 0 1 0 =
    ⟨#["  - User assertion: `ProperSub(x, y)`.", "  - Sub(x, y): false.",
      "  - Reverse Sub(y, x): false."], 67⟩ := by native_decide
example : properSubEvidenceCosted #[`w] #[`x, `y] (twoThingTables #[.binary .sub 0 1 0]) 0 1 0 =
    ⟨#["  - User assertion: `ProperSub(x, y)`.", "  - Sub(x, y): true.",
      "  - Reverse Sub(y, x): false."], 67⟩ := by native_decide
example : properSubEvidenceCosted #[`w] #[`x, `y] (twoThingTables #[.binary .sub 1 0 0]) 0 1 0 =
    ⟨#["  - User assertion: `ProperSub(x, y)`.", "  - Sub(x, y): false.",
      "  - Reverse Sub(y, x): true."], 67⟩ := by native_decide
example : properSubEvidenceCosted #[`w] #[`x, `y] (twoThingTables #[.binary .sub 0 1 0, .binary .sub 1 0 0]) 0 1 0 =
    ⟨#["  - User assertion: `ProperSub(x, y)`.", "  - Sub(x, y): true.",
      "  - Reverse Sub(y, x): true."], 67⟩ := by native_decide
example : properSubRequiredMissingCosted #[`w] #[`x, `y] (twoThingTables #[]) 0 1 0 =
    ⟨"`ProperSub(x, y)` requires `Sub(x, y)`; missing the forward `Sub` fact.", 35⟩ := by native_decide
example : properSubRequiredMissingCosted #[`w] #[`x, `y] (twoThingTables #[.binary .sub 0 1 0, .binary .sub 1 0 0]) 0 1 0 =
    ⟨"`ProperSub(x, y)` requires absence of reverse `Sub`; conflicting `Sub(y, x)` is present.", 35⟩ := by native_decide
example : properSubEvidenceCosted #[`w] #[`x, `y]
    (twoThingTables #[.binary .sub 0 0 0, .binary .sub 0 0 0]) 0 0 0 =
    ⟨#["  - User assertion: `ProperSub(x, x)`.", "  - Sub(x, x): true.",
      "  - Reverse Sub(x, x): true."], 67⟩ := by native_decide
example : properSubRequiredMissingCosted #[] #[] {} 7 8 3 =
    ⟨"`ProperSub(#7, #8)` requires `Sub(#7, #8)`; missing the forward `Sub` fact.", 20⟩ := by native_decide
example : properSubEvidenceCosted #[] #[] {} 7 8 3 =
    ⟨#["  - User assertion: `ProperSub(#7, #8)`.", "  - Sub(#7, #8): false.",
      "  - Reverse Sub(#8, #7): false."], 37⟩ := by native_decide

example (worlds things : Array Name) (x w : Nat) :
    (nonEmptySetRequiredMissingCosted worlds things x w).cost = 14 :=
  nonEmptySetRequiredMissingCosted_cost worlds things x w
example (worlds things : Array Name) (tables : FactTables) (x w : Nat) :
    (nonEmptySetEvidenceCosted worlds things tables x w).cost ≤ 21 * things.size + 26 :=
  nonEmptySetEvidenceCosted_cost_le worlds things tables x w
example (worlds things : Array Name) (tables : FactTables) (x y w : Nat) :
    (properSubRequiredMissingCosted worlds things tables x y w).cost ≤ 35 :=
  properSubRequiredMissingCosted_cost_le worlds things tables x y w
example (worlds things : Array Name) (tables : FactTables) (x y w : Nat) :
    (properSubEvidenceCosted worlds things tables x y w).cost ≤ 67 :=
  properSubEvidenceCosted_cost_le worlds things tables x y w
example (worlds things : Array Name) (tables : FactTables) (x w : Nat) :
    (nonEmptySetEvidenceCosted worlds things tables x w).value.size = 2 :=
  nonEmptySetEvidenceCosted_size worlds things tables x w
example (worlds things : Array Name) (tables : FactTables) (x y w : Nat) :
    (properSubEvidenceCosted worlds things tables x y w).value.size = 3 :=
  properSubEvidenceCosted_size worlds things tables x y w
example {T₁ T₂ : Nat} (h : T₁ ≤ T₂) : 21 * T₁ + 26 ≤ 21 * T₂ + 26 := by omega

example : ((derivedAssertionFailure? #[`w] #[`x, `y]
    #[.derived (.unary "NonEmptySet" "x") .everywhere]
    #[.derived (fun _ => "unused") .everywhere] (twoThingTables #[])).getD #[])[1]? =
    some "Required but missing: `NonEmptySet(x)` requires some `MemberOf(member, x)`; missing any member at `w`." := by native_decide
example : ((derivedAssertionFailure? #[`w] #[`x, `y]
    #[.derived (.unary "NonEmptySet" "x") .everywhere]
    #[.derived (fun _ => "unused") .everywhere] (twoThingTables #[])).getD #[])[5]? =
    some "  - Computed NonEmptySet: false, because no `MemberOf(_, x)` fact holds at `w`." := by native_decide
example : ((derivedAssertionFailure? #[`w] #[`x, `y]
    #[.derived (.binary "ProperSub" "x" "y") .everywhere]
    #[.derived (fun _ => "unused") .everywhere] (twoThingTables #[.binary .sub 1 0 0])).getD #[])[1]? =
    some "Required but missing: `ProperSub(x, y)` requires `Sub(x, y)`; missing the forward `Sub` fact." := by native_decide
example : ((derivedAssertionFailure? #[`w] #[`x, `y]
    #[.derived (.binary "ProperSub" "x" "y") .everywhere]
    #[.derived (fun _ => "unused") .everywhere] (twoThingTables #[.binary .sub 1 0 0])).getD #[])[5]? =
    some "  - Sub(x, y): false." := by native_decide
example : ((derivedAssertionFailure? #[`w] #[`x, `y]
    #[.derived (.binary "ProperSub" "x" "y") .everywhere]
    #[.derived (fun _ => "unused") .everywhere] (twoThingTables #[.binary .sub 1 0 0])).getD #[])[6]? =
    some "  - Reverse Sub(y, x): true." := by native_decide

-- Each report component runs the difference search once. For two things,
-- its exact cost is 43 with a first-candidate witness and 62 with a last one.
example : subsetRequiredMissingCosted #[`w] #[`x, `y] (twoThingTables #[.binary .memberOf 0 0 0]) 0 1 0 "fallback" =
    ⟨"`SubsetOf(x, y)` requires every left member to be a right member; `x` is in `x` but missing from `y`.", 66⟩ := by native_decide
example : properSubsetRequiredMissingCosted #[`w] #[`x, `y] (twoThingTables #[.binary .memberOf 0 0 0]) 0 1 0 =
    ⟨"`ProperSubsetOf(x, y)` first requires `SubsetOf`; `x` is in the left set but missing from the right set.", 62⟩ := by native_decide
example : subsetEvidenceCosted #[`w] #[`x, `y] (twoThingTables #[.binary .memberOf 0 0 0]) 0 1 0 =
    ⟨#["  - User assertion: `SubsetOf(x, y)`.",
      "  - Computed SubsetOf: false, because `x` is a member of `x` but not of `y` at `w`."], 77⟩ := by native_decide
example : properSubsetEvidenceCosted #[`w] #[`x, `y] (twoThingTables #[.binary .memberOf 0 0 0]) 0 1 0 =
    ⟨#["  - User assertion: `ProperSubsetOf(x, y)`.",
      "  - Computed ProperSubsetOf: false, because the subset condition already fails: `x` is a member of `x` but not of `y` at `w`."], 77⟩ := by native_decide
example : subsetRequiredMissingCosted #[`w] #[`x, `y] (twoThingTables #[.binary .memberOf 1 0 0]) 0 1 0 "fallback" =
    ⟨"`SubsetOf(x, y)` requires every left member to be a right member; `y` is in `x` but missing from `y`.", 85⟩ := by native_decide
example : properSubsetRequiredMissingCosted #[`w] #[`x, `y] (twoThingTables #[.binary .memberOf 1 0 0]) 0 1 0 =
    ⟨"`ProperSubsetOf(x, y)` first requires `SubsetOf`; `y` is in the left set but missing from the right set.", 81⟩ := by native_decide
example : subsetEvidenceCosted #[`w] #[`x, `y] (twoThingTables #[.binary .memberOf 1 0 0]) 0 1 0 =
    ⟨#["  - User assertion: `SubsetOf(x, y)`.",
      "  - Computed SubsetOf: false, because `y` is a member of `x` but not of `y` at `w`."], 96⟩ := by native_decide
example : properSubsetEvidenceCosted #[`w] #[`x, `y] (twoThingTables #[.binary .memberOf 1 0 0]) 0 1 0 =
    ⟨#["  - User assertion: `ProperSubsetOf(x, y)`.",
      "  - Computed ProperSubsetOf: false, because the subset condition already fails: `y` is a member of `x` but not of `y` at `w`."], 96⟩ := by native_decide
example : subsetRequiredMissingCosted #[`w] #[`x, `y] (twoThingTables #[.binary .memberOf 1 0 0, .binary .memberOf 0 0 0]) 0 1 0 "fallback" =
    ⟨"`SubsetOf(x, y)` requires every left member to be a right member; `x` is in `x` but missing from `y`.", 66⟩ := by native_decide
example : properSubsetRequiredMissingCosted #[`w] #[`x, `y] (twoThingTables #[.binary .memberOf 1 0 0, .binary .memberOf 0 0 0]) 0 1 0 =
    ⟨"`ProperSubsetOf(x, y)` first requires `SubsetOf`; `x` is in the left set but missing from the right set.", 62⟩ := by native_decide
example : subsetEvidenceCosted #[`w] #[`x, `y] (twoThingTables #[.binary .memberOf 1 0 0, .binary .memberOf 0 0 0]) 0 1 0 =
    ⟨#["  - User assertion: `SubsetOf(x, y)`.",
      "  - Computed SubsetOf: false, because `x` is a member of `x` but not of `y` at `w`."], 77⟩ := by native_decide
example : properSubsetEvidenceCosted #[`w] #[`x, `y] (twoThingTables #[.binary .memberOf 1 0 0, .binary .memberOf 0 0 0]) 0 1 0 =
    ⟨#["  - User assertion: `ProperSubsetOf(x, y)`.",
      "  - Computed ProperSubsetOf: false, because the subset condition already fails: `x` is a member of `x` but not of `y` at `w`."], 77⟩ := by native_decide
example : subsetRequiredMissingCosted #[`w] #[`x, `y] (twoThingTables #[.binary .memberOf 1 0 0, .binary .memberOf 1 0 0]) 0 1 0 "fallback" =
    ⟨"`SubsetOf(x, y)` requires every left member to be a right member; `y` is in `x` but missing from `y`.", 85⟩ := by native_decide
example : properSubsetRequiredMissingCosted #[`w] #[`x, `y] (twoThingTables #[.binary .memberOf 1 0 0, .binary .memberOf 1 0 0]) 0 1 0 =
    ⟨"`ProperSubsetOf(x, y)` first requires `SubsetOf`; `y` is in the left set but missing from the right set.", 81⟩ := by native_decide
example : subsetEvidenceCosted #[`w] #[`x, `y] (twoThingTables #[.binary .memberOf 1 0 0, .binary .memberOf 1 0 0]) 0 1 0 =
    ⟨#["  - User assertion: `SubsetOf(x, y)`.",
      "  - Computed SubsetOf: false, because `y` is a member of `x` but not of `y` at `w`."], 96⟩ := by native_decide
example : properSubsetEvidenceCosted #[`w] #[`x, `y] (twoThingTables #[.binary .memberOf 1 0 0, .binary .memberOf 1 0 0]) 0 1 0 =
    ⟨#["  - User assertion: `ProperSubsetOf(x, y)`.",
      "  - Computed ProperSubsetOf: false, because the subset condition already fails: `y` is a member of `x` but not of `y` at `w`."], 96⟩ := by native_decide

-- An absent witness gives SubsetOf no evidence. ProperSubsetOf reports that
-- the strictness condition is missing. The caller constructs fallback text.
example : subsetRequiredMissingCosted #[`w] #[`x, `y] (twoThingTables #[]) 0 1 0 "fallback" =
    ⟨"fallback", 45⟩ := by native_decide
example : subsetEvidenceCosted #[`w] #[`x, `y] (twoThingTables #[]) 0 1 0 =
    ⟨#[], 46⟩ := by native_decide
example : properSubsetRequiredMissingCosted #[`w] #[`x, `y] (twoThingTables #[]) 0 1 0 =
    ⟨"`ProperSubsetOf(x, y)` requires strictness; missing a member of `y` that is not also a member of `x`.", 61⟩ := by native_decide
example : properSubsetEvidenceCosted #[`w] #[`x, `y] (twoThingTables #[]) 0 1 0 =
    ⟨#["  - User assertion: `ProperSubsetOf(x, y)`.", "  - Computed ProperSubsetOf: false, because no member of `y` is outside `x` at `w`."], 72⟩ := by native_decide
example : properSubsetEvidenceCosted #[`w] #[`x, `y]
    (twoThingTables #[.binary .memberOf 0 0 0, .binary .memberOf 0 1 0,
      .binary .memberOf 1 0 0, .binary .memberOf 1 1 0]) 0 1 0 =
    ⟨#["  - User assertion: `ProperSubsetOf(x, y)`.", "  - Computed ProperSubsetOf: false, because no member of `y` is outside `x` at `w`."], 108⟩ := by native_decide
example : subsetEvidenceCosted #[`w] #[`x, `y]
    (twoThingTables #[.binary .memberOf 0 1 0, .binary .sub 1 0 0]) 0 1 0 =
    ⟨#[], 46⟩ := by native_decide
example : subsetRequiredMissingCosted #[] #[] {} 7 8 3 "fallback" =
    ⟨"fallback", 1⟩ := by native_decide
example : subsetEvidenceCosted #[] #[] {} 7 8 3 = ⟨#[], 2⟩ := by native_decide
example : properSubsetRequiredMissingCosted #[] #[] {} 7 8 3 =
    ⟨"`ProperSubsetOf(#7, #8)` requires strictness; missing a member of `#8` that is not also a member of `#7`.", 17⟩ := by native_decide
example : properSubsetEvidenceCosted #[] #[] {} 7 8 3 =
    ⟨#["  - User assertion: `ProperSubsetOf(#7, #8)`.",
      "  - Computed ProperSubsetOf: false, because no member of `#8` is outside `#7` at `#3`."], 28⟩ := by native_decide

example (worlds things : Array Name) (tables : FactTables) (x y w : Nat) (fallback : String) :
    (subsetRequiredMissingCosted worlds things tables x y w fallback).cost ≤ 40 * things.size + 23 :=
  subsetRequiredMissingCosted_cost_le worlds things tables x y w fallback
example (worlds things : Array Name) (tables : FactTables) (x y w : Nat) :
    (subsetEvidenceCosted worlds things tables x y w).cost ≤ 40 * things.size + 34 :=
  subsetEvidenceCosted_cost_le worlds things tables x y w
example (worlds things : Array Name) (tables : FactTables) (x y w : Nat) :
    (properSubsetRequiredMissingCosted worlds things tables x y w).cost ≤ 40 * things.size + 19 :=
  properSubsetRequiredMissingCosted_cost_le worlds things tables x y w
example (worlds things : Array Name) (tables : FactTables) (x y w : Nat) :
    (properSubsetEvidenceCosted worlds things tables x y w).cost ≤ 40 * things.size + 34 :=
  properSubsetEvidenceCosted_cost_le worlds things tables x y w
example (worlds things : Array Name) (tables : FactTables) (x y w : Nat) :
    (subsetEvidenceCosted worlds things tables x y w).value.size ≤ 2 :=
  subsetEvidenceCosted_size_le worlds things tables x y w
example (worlds things : Array Name) (tables : FactTables) (x y w : Nat) :
    (properSubsetEvidenceCosted worlds things tables x y w).value.size = 2 :=
  properSubsetEvidenceCosted_size worlds things tables x y w
example {T₁ T₂ C : Nat} (h : T₁ ≤ T₂) : 40 * T₁ + C ≤ 40 * T₂ + C := by omega

example : ((derivedAssertionFailure? #[`w] #[`x, `y]
    #[.derived (.binary "SubsetOf" "x" "y") .everywhere]
    #[.derived (fun _ => "unused") .everywhere] (twoThingTables #[.binary .memberOf 1 0 0, .binary .memberOf 0 0 0])).getD #[])[1]? =
    some "Required but missing: `SubsetOf(x, y)` requires every left member to be a right member; `x` is in `x` but missing from `y`." := by native_decide
example : ((derivedAssertionFailure? #[`w] #[`x, `y]
    #[.derived (.binary "SubsetOf" "x" "y") .everywhere]
    #[.derived (fun _ => "unused") .everywhere] (twoThingTables #[.binary .memberOf 1 0 0, .binary .memberOf 0 0 0])).getD #[])[5]? =
    some "  - Computed SubsetOf: false, because `x` is a member of `x` but not of `y` at `w`." := by native_decide
example : ((derivedAssertionFailure? #[`w] #[`x, `y]
    #[.derived (.binary "ProperSubsetOf" "x" "y") .everywhere]
    #[.derived (fun _ => "unused") .everywhere] (twoThingTables #[.binary .memberOf 1 0 0, .binary .memberOf 0 0 0])).getD #[])[1]? =
    some "Required but missing: `ProperSubsetOf(x, y)` first requires `SubsetOf`; `x` is in the left set but missing from the right set." := by native_decide
example : ((derivedAssertionFailure? #[`w] #[`x, `y]
    #[.derived (.binary "ProperSubsetOf" "x" "y") .everywhere]
    #[.derived (fun _ => "unused") .everywhere] (twoThingTables #[.binary .memberOf 1 0 0, .binary .memberOf 0 0 0])).getD #[])[5]? =
    some "  - Computed ProperSubsetOf: false, because the subset condition already fails: `x` is a member of `x` but not of `y` at `w`." := by native_decide
example : ((derivedAssertionFailure? #[`w] #[`x, `y]
    #[.derived (.binary "ProperSubsetOf" "x" "y") .everywhere]
    #[.derived (fun _ => "unused") .everywhere] (twoThingTables #[])).getD #[])[1]? =
    some "Required but missing: `ProperSubsetOf(x, y)` requires strictness; missing a member of `y` that is not also a member of `x`." := by native_decide
example : ((derivedAssertionFailure? #[`w] #[`x, `y]
    #[.derived (.binary "ProperSubsetOf" "x" "y") .everywhere]
    #[.derived (fun _ => "unused") .everywhere] (twoThingTables #[])).getD #[])[5]? =
    some "  - Computed ProperSubsetOf: false, because no member of `y` is outside `x` at `w`." := by native_decide

-- Missing quality runs the uniqueness check and the complete status report.
-- Both costs are included. Inherence facts are irrelevant on that branch.
example : simpleQualityEvidenceCosted #[`w] #[`x, `y] (twoThingTables #[]) 0 0 =
    ⟨#["  - User assertion: `SimpleQuality(x)`.",
      "  - Computed Quality: false, because `x` instantiates no `QualityKind` at this world."], 95⟩ := by native_decide
example : simpleQualityEvidenceCosted #[`w] #[`x, `y] (twoThingTables #[.unary .qualityKind 1 0, .binary .inst 0 1 0, .unary .qualityKind 0 0, .binary .inst 0 0 0]) 0 0 =
    ⟨#["  - User assertion: `SimpleQuality(x)`.",
      "  - Computed Quality: false, because `x` instantiates multiple quality kinds at this world: x, y."], 187⟩ := by native_decide
example : simpleQualityEvidenceCosted #[`w] #[`x, `y] (twoThingTables #[.binary .inheresIn 0 0 0, .binary .inheresIn 1 0 0]) 0 0 =
    ⟨#["  - User assertion: `SimpleQuality(x)`.",
      "  - Computed Quality: false, because `x` instantiates no `QualityKind` at this world."], 95⟩ := by native_decide
example : simpleQualityEvidenceCosted #[] #[] {} 7 3 =
    ⟨#["  - User assertion: `SimpleQuality(#7)`.",
      "  - Computed Quality: false, because `#7` instantiates no `QualityKind` at this world."], 29⟩ := by native_decide
example : complexQualityEvidenceCosted #[`w] #[`x, `y] (twoThingTables #[]) 0 0 =
    ⟨#["  - User assertion: `ComplexQuality(x)`.",
      "  - Computed Quality: false, because `x` instantiates no `QualityKind` at this world."], 95⟩ := by native_decide
example : complexQualityEvidenceCosted #[`w] #[`x, `y] (twoThingTables #[.unary .qualityKind 1 0, .binary .inst 0 1 0, .unary .qualityKind 0 0, .binary .inst 0 0 0]) 0 0 =
    ⟨#["  - User assertion: `ComplexQuality(x)`.",
      "  - Computed Quality: false, because `x` instantiates multiple quality kinds at this world: x, y."], 187⟩ := by native_decide
example : complexQualityEvidenceCosted #[`w] #[`x, `y] (twoThingTables #[.binary .inheresIn 0 0 0, .binary .inheresIn 1 0 0]) 0 0 =
    ⟨#["  - User assertion: `ComplexQuality(x)`.",
      "  - Computed Quality: false, because `x` instantiates no `QualityKind` at this world."], 95⟩ := by native_decide
example : complexQualityEvidenceCosted #[] #[] {} 7 3 =
    ⟨#["  - User assertion: `ComplexQuality(#7)`.",
      "  - Computed Quality: false, because `#7` instantiates no `QualityKind` at this world."], 29⟩ := by native_decide

-- A valid quality uses the first incoming InheresIn edge in declaration order.
-- An outgoing edge cannot serve as that witness. Duplicate facts have no effect.
example : simpleQualityEvidenceCosted #[`w] #[`x, `y] (twoThingTables #[.unary .qualityKind 1 0, .binary .inst 0 1 0]) 0 0 =
    ⟨#["  - User assertion: `SimpleQuality(x)`.",
      "  - Computed SimpleQuality: true, because it is a computed `Quality` and no thing inheres in it."], 108⟩ := by native_decide
example : complexQualityEvidenceCosted #[`w] #[`x, `y] (twoThingTables #[.unary .qualityKind 1 0, .binary .inst 0 1 0]) 0 0 =
    ⟨#["  - User assertion: `ComplexQuality(x)`.",
      "  - Computed ComplexQuality: false, because it is a computed `Quality` but no thing inheres in it."], 108⟩ := by native_decide
example : simpleQualityEvidenceCosted #[`w] #[`x, `y] (twoThingTables #[.unary .qualityKind 1 0, .binary .inst 0 1 0, .binary .inheresIn 0 0 0]) 0 0 =
    ⟨#["  - User assertion: `SimpleQuality(x)`.",
      "  - Computed SimpleQuality: false, because `x` inheres in `x` at `w`."], 104⟩ := by native_decide
example : complexQualityEvidenceCosted #[`w] #[`x, `y] (twoThingTables #[.unary .qualityKind 1 0, .binary .inst 0 1 0, .binary .inheresIn 0 0 0]) 0 0 =
    ⟨#["  - User assertion: `ComplexQuality(x)`.",
      "  - Computed ComplexQuality: true, witnessed by `InheresIn(x, x)` at `w`."], 104⟩ := by native_decide
example : simpleQualityEvidenceCosted #[`w] #[`x, `y] (twoThingTables #[.unary .qualityKind 1 0, .binary .inst 0 1 0, .binary .inheresIn 1 0 0]) 0 0 =
    ⟨#["  - User assertion: `SimpleQuality(x)`.",
      "  - Computed SimpleQuality: false, because `y` inheres in `x` at `w`."], 122⟩ := by native_decide
example : complexQualityEvidenceCosted #[`w] #[`x, `y] (twoThingTables #[.unary .qualityKind 1 0, .binary .inst 0 1 0, .binary .inheresIn 1 0 0]) 0 0 =
    ⟨#["  - User assertion: `ComplexQuality(x)`.",
      "  - Computed ComplexQuality: true, witnessed by `InheresIn(y, x)` at `w`."], 122⟩ := by native_decide
example : simpleQualityEvidenceCosted #[`w] #[`x, `y] (twoThingTables #[.unary .qualityKind 1 0, .binary .inst 0 1 0, .binary .inheresIn 1 0 0, .binary .inheresIn 0 0 0]) 0 0 =
    ⟨#["  - User assertion: `SimpleQuality(x)`.",
      "  - Computed SimpleQuality: false, because `x` inheres in `x` at `w`."], 104⟩ := by native_decide
example : complexQualityEvidenceCosted #[`w] #[`x, `y] (twoThingTables #[.unary .qualityKind 1 0, .binary .inst 0 1 0, .binary .inheresIn 1 0 0, .binary .inheresIn 0 0 0]) 0 0 =
    ⟨#["  - User assertion: `ComplexQuality(x)`.",
      "  - Computed ComplexQuality: true, witnessed by `InheresIn(x, x)` at `w`."], 104⟩ := by native_decide
example : simpleQualityEvidenceCosted #[`w] #[`x, `y] (twoThingTables #[.unary .qualityKind 1 0, .binary .inst 0 1 0, .binary .inheresIn 1 0 0, .binary .inheresIn 1 0 0]) 0 0 =
    ⟨#["  - User assertion: `SimpleQuality(x)`.",
      "  - Computed SimpleQuality: false, because `y` inheres in `x` at `w`."], 122⟩ := by native_decide
example : complexQualityEvidenceCosted #[`w] #[`x, `y] (twoThingTables #[.unary .qualityKind 1 0, .binary .inst 0 1 0, .binary .inheresIn 1 0 0, .binary .inheresIn 1 0 0]) 0 0 =
    ⟨#["  - User assertion: `ComplexQuality(x)`.",
      "  - Computed ComplexQuality: true, witnessed by `InheresIn(y, x)` at `w`."], 122⟩ := by native_decide
example : simpleQualityEvidenceCosted #[`w] #[`x, `y] (twoThingTables #[.unary .qualityKind 1 0, .binary .inst 0 1 0, .binary .inheresIn 0 1 0]) 0 0 =
    ⟨#["  - User assertion: `SimpleQuality(x)`.",
      "  - Computed SimpleQuality: true, because it is a computed `Quality` and no thing inheres in it."], 108⟩ := by native_decide
example : complexQualityEvidenceCosted #[`w] #[`x, `y] (twoThingTables #[.unary .qualityKind 1 0, .binary .inst 0 1 0, .binary .inheresIn 0 1 0]) 0 0 =
    ⟨#["  - User assertion: `ComplexQuality(x)`.",
      "  - Computed ComplexQuality: false, because it is a computed `Quality` but no thing inheres in it."], 108⟩ := by native_decide

example : simpleQualityRequiredMissingCosted #[`w] #[`x, `y] (twoThingTables #[]) 0 0 "fallback" =
    ⟨"`SimpleQuality(x)` requires computed `Quality(x)`; missing the quality condition.", 44⟩ := by native_decide
example : simpleQualityRequiredMissingCosted #[`w] #[`x, `y] (twoThingTables #[.unary .qualityKind 1 0, .binary .inst 0 1 0, .unary .qualityKind 0 0, .binary .inst 0 0 0]) 0 0 "fallback" =
    ⟨"`SimpleQuality(x)` requires computed `Quality(x)`; missing the quality condition.", 78⟩ := by native_decide
example : simpleQualityRequiredMissingCosted #[`w] #[`x, `y] (twoThingTables #[.unary .qualityKind 1 0, .binary .inst 0 1 0, .binary .inheresIn 0 0 0]) 0 0 "fallback" =
    ⟨"`SimpleQuality(x)` requires no thing to inhere in it; conflicting `InheresIn(x, x)` is present.", 93⟩ := by native_decide
example : simpleQualityRequiredMissingCosted #[`w] #[`x, `y] (twoThingTables #[.unary .qualityKind 1 0, .binary .inst 0 1 0, .binary .inheresIn 1 0 0]) 0 0 "fallback" =
    ⟨"`SimpleQuality(x)` requires no thing to inhere in it; conflicting `InheresIn(y, x)` is present.", 111⟩ := by native_decide
example : simpleQualityRequiredMissingCosted #[`w] #[`x, `y]
    (twoThingTables #[.unary .qualityKind 1 0, .binary .inst 0 1 0]) 0 0 "fallback" = ⟨"fallback", 101⟩ := by native_decide
example : simpleQualityRequiredMissingCosted #[] #[] {} 7 3 "fallback" =
    ⟨"`SimpleQuality(#7)` requires computed `Quality(#7)`; missing the quality condition.", 12⟩ := by native_decide
example : complexQualityRequiredMissingCosted #[`w] #[`x, `y] (twoThingTables #[]) 0 0 =
    ⟨"`ComplexQuality(x)` requires computed `Quality(x)`; missing the quality condition.", 44⟩ := by native_decide
example : complexQualityRequiredMissingCosted #[`w] #[`x, `y] (twoThingTables #[.unary .qualityKind 1 0, .binary .inst 0 1 0]) 0 0 =
    ⟨"`ComplexQuality(x)` requires at least one `InheresIn(part, x)`; missing any inhering part.", 62⟩ := by native_decide
example : complexQualityRequiredMissingCosted #[`w] #[`x, `y] (twoThingTables #[.unary .qualityKind 1 0, .binary .inst 0 1 0, .unary .qualityKind 0 0, .binary .inst 0 0 0]) 0 0 =
    ⟨"`ComplexQuality(x)` requires computed `Quality(x)`; missing the quality condition.", 78⟩ := by native_decide
example : complexQualityRequiredMissingCosted #[] #[] {} 7 3 =
    ⟨"`ComplexQuality(#7)` requires computed `Quality(#7)`; missing the quality condition.", 12⟩ := by native_decide

example (worlds things : Array Name) (tables : FactTables) (x w : Nat) (fallback : String) :
    (simpleQualityRequiredMissingCosted worlds things tables x w fallback).cost ≤ 55 * things.size + 19 :=
  simpleQualityRequiredMissingCosted_cost_le worlds things tables x w fallback
example (worlds things : Array Name) (tables : FactTables) (x w : Nat) :
    (complexQualityRequiredMissingCosted worlds things tables x w).cost ≤ 34 * things.size + 12 :=
  complexQualityRequiredMissingCosted_cost_le worlds things tables x w
example (worlds things : Array Name) (tables : FactTables) (x w : Nat) :
    (simpleQualityEvidenceCosted worlds things tables x w).cost ≤ 78 * things.size + 41 :=
  simpleQualityEvidenceCosted_cost_le worlds things tables x w
example (worlds things : Array Name) (tables : FactTables) (x w : Nat) :
    (complexQualityEvidenceCosted worlds things tables x w).cost ≤ 78 * things.size + 41 :=
  complexQualityEvidenceCosted_cost_le worlds things tables x w
example (worlds things : Array Name) (tables : FactTables) (x w : Nat) :
    (simpleQualityEvidenceCosted worlds things tables x w).value.size = 2 :=
  simpleQualityEvidenceCosted_size worlds things tables x w
example (worlds things : Array Name) (tables : FactTables) (x w : Nat) :
    (complexQualityEvidenceCosted worlds things tables x w).value.size = 2 :=
  complexQualityEvidenceCosted_size worlds things tables x w
example {T₁ T₂ : Nat} (h : T₁ ≤ T₂) : 55 * T₁ + 19 ≤ 55 * T₂ + 19 := by omega
example {T₁ T₂ : Nat} (h : T₁ ≤ T₂) : 34 * T₁ + 12 ≤ 34 * T₂ + 12 := by omega
example {T₁ T₂ : Nat} (h : T₁ ≤ T₂) : 78 * T₁ + 41 ≤ 78 * T₂ + 41 := by omega

example : ((derivedAssertionFailure? #[`w] #[`x, `y]
    #[.derived (.unary "SimpleQuality" "x") .everywhere]
    #[.derived (fun _ => "unused") .everywhere] (twoThingTables #[])).getD #[])[1]? =
    some "Required but missing: `SimpleQuality(x)` requires computed `Quality(x)`; missing the quality condition." := by native_decide
example : ((derivedAssertionFailure? #[`w] #[`x, `y]
    #[.derived (.unary "SimpleQuality" "x") .everywhere]
    #[.derived (fun _ => "unused") .everywhere] (twoThingTables #[])).getD #[])[5]? =
    some "  - Computed Quality: false, because `x` instantiates no `QualityKind` at this world." := by native_decide
example : ((derivedAssertionFailure? #[`w] #[`x, `y]
    #[.derived (.unary "ComplexQuality" "x") .everywhere]
    #[.derived (fun _ => "unused") .everywhere] (twoThingTables #[])).getD #[])[1]? =
    some "Required but missing: `ComplexQuality(x)` requires computed `Quality(x)`; missing the quality condition." := by native_decide
example : ((derivedAssertionFailure? #[`w] #[`x, `y]
    #[.derived (.unary "ComplexQuality" "x") .everywhere]
    #[.derived (fun _ => "unused") .everywhere] (twoThingTables #[])).getD #[])[5]? =
    some "  - Computed Quality: false, because `x` instantiates no `QualityKind` at this world." := by native_decide
example : ((derivedAssertionFailure? #[`w] #[`x, `y]
    #[.derived (.unary "SimpleQuality" "x") .everywhere]
    #[.derived (fun _ => "unused") .everywhere] (twoThingTables #[.unary .qualityKind 1 0, .binary .inst 0 1 0, .binary .inheresIn 1 0 0, .binary .inheresIn 0 0 0])).getD #[])[1]? =
    some "Required but missing: `SimpleQuality(x)` requires no thing to inhere in it; conflicting `InheresIn(x, x)` is present." := by native_decide
example : ((derivedAssertionFailure? #[`w] #[`x, `y]
    #[.derived (.unary "SimpleQuality" "x") .everywhere]
    #[.derived (fun _ => "unused") .everywhere] (twoThingTables #[.unary .qualityKind 1 0, .binary .inst 0 1 0, .binary .inheresIn 1 0 0, .binary .inheresIn 0 0 0])).getD #[])[5]? =
    some "  - Computed SimpleQuality: false, because `x` inheres in `x` at `w`." := by native_decide
example : ((derivedAssertionFailure? #[`w] #[`x, `y]
    #[.derived (.unary "ComplexQuality" "x") .everywhere]
    #[.derived (fun _ => "unused") .everywhere] (twoThingTables #[.unary .qualityKind 1 0, .binary .inst 0 1 0])).getD #[])[1]? =
    some "Required but missing: `ComplexQuality(x)` requires at least one `InheresIn(part, x)`; missing any inhering part." := by native_decide
example : ((derivedAssertionFailure? #[`w] #[`x, `y]
    #[.derived (.unary "ComplexQuality" "x") .everywhere]
    #[.derived (fun _ => "unused") .everywhere] (twoThingTables #[.unary .qualityKind 1 0, .binary .inst 0 1 0])).getD #[])[5]? =
    some "  - Computed ComplexQuality: false, because it is a computed `Quality` but no thing inheres in it." := by native_decide

-- Missing classification skips instance work. With a classified type,
-- first/last invalid instances select the same witness in all three rows.
example : simpleQualityTypeRequiredMissingCosted #[`w] #[`t, `y] (twoThingTables #[]) 0 0 "fallback" =
    ⟨"`SimpleQualityType(t)` requires `QualityType(t)`; missing that primitive classification.", 22⟩ := by native_decide
example : simpleQualityTypeEvidenceCosted #[`w] #[`t, `y] (twoThingTables #[]) 0 0 =
    ⟨#["  - User assertion: `SimpleQualityType(t)`.", "  - Computed SimpleQualityType: false, because `QualityType(t)` is not true at `w`."], 33⟩ := by native_decide
example : simpleQualityTypeRequiredMissingCosted #[`w] #[`t, `y] (twoThingTables #[.binary .inst 0 0 0, .binary .inst 1 0 0]) 0 0 "fallback" =
    ⟨"`SimpleQualityType(t)` requires `QualityType(t)`; missing that primitive classification.", 22⟩ := by native_decide
example : simpleQualityTypeEvidenceCosted #[`w] #[`t, `y] (twoThingTables #[.binary .inst 0 0 0, .binary .inst 1 0 0]) 0 0 =
    ⟨#["  - User assertion: `SimpleQualityType(t)`.", "  - Computed SimpleQualityType: false, because `QualityType(t)` is not true at `w`."], 33⟩ := by native_decide
example : simpleQualityTypeRequiredMissingCosted #[`w] #[`t, `y] (twoThingTables #[.unary .qualityType 0 0, .binary .inst 0 0 0]) 0 0 "fallback" =
    ⟨"`SimpleQualityType(t)` requires every instance to be a computed `SimpleQuality`; instance `t` is not simple.", 88⟩ := by native_decide
example : simpleQualityTypeEvidenceCosted #[`w] #[`t, `y] (twoThingTables #[.unary .qualityType 0 0, .binary .inst 0 0 0]) 0 0 =
    ⟨#["  - User assertion: `SimpleQualityType(t)`.",
      "  - Computed SimpleQualityType: false, because instance `t` is not a computed `SimpleQuality` at `w`.",
      "  - Computed Quality: false, because `t` instantiates no `QualityKind` at this world."], 149⟩ := by native_decide
example : simpleQualityTypeRequiredMissingCosted #[`w] #[`t, `y] (twoThingTables #[.unary .qualityType 0 0, .binary .inst 1 0 0]) 0 0 "fallback" =
    ⟨"`SimpleQualityType(t)` requires every instance to be a computed `SimpleQuality`; instance `y` is not simple.", 107⟩ := by native_decide
example : simpleQualityTypeEvidenceCosted #[`w] #[`t, `y] (twoThingTables #[.unary .qualityType 0 0, .binary .inst 1 0 0]) 0 0 =
    ⟨#["  - User assertion: `SimpleQualityType(t)`.",
      "  - Computed SimpleQualityType: false, because instance `y` is not a computed `SimpleQuality` at `w`.",
      "  - Computed Quality: false, because `y` instantiates no `QualityKind` at this world."], 168⟩ := by native_decide
example : simpleQualityTypeRequiredMissingCosted #[`w] #[`t, `y] (twoThingTables #[.unary .qualityType 0 0, .binary .inst 1 0 0, .binary .inst 0 0 0]) 0 0 "fallback" =
    ⟨"`SimpleQualityType(t)` requires every instance to be a computed `SimpleQuality`; instance `t` is not simple.", 88⟩ := by native_decide
example : simpleQualityTypeEvidenceCosted #[`w] #[`t, `y] (twoThingTables #[.unary .qualityType 0 0, .binary .inst 1 0 0, .binary .inst 0 0 0]) 0 0 =
    ⟨#["  - User assertion: `SimpleQualityType(t)`.",
      "  - Computed SimpleQualityType: false, because instance `t` is not a computed `SimpleQuality` at `w`.",
      "  - Computed Quality: false, because `t` instantiates no `QualityKind` at this world."], 149⟩ := by native_decide
example : simpleQualityTypeRequiredMissingCosted #[`w] #[`t, `y] (twoThingTables #[.unary .qualityType 0 0, .binary .inst 1 0 0, .binary .inst 1 0 0]) 0 0 "fallback" =
    ⟨"`SimpleQualityType(t)` requires every instance to be a computed `SimpleQuality`; instance `y` is not simple.", 107⟩ := by native_decide
example : simpleQualityTypeEvidenceCosted #[`w] #[`t, `y] (twoThingTables #[.unary .qualityType 0 0, .binary .inst 1 0 0, .binary .inst 1 0 0]) 0 0 =
    ⟨#["  - User assertion: `SimpleQualityType(t)`.",
      "  - Computed SimpleQualityType: false, because instance `y` is not a computed `SimpleQuality` at `w`.",
      "  - Computed Quality: false, because `y` instantiates no `QualityKind` at this world."], 168⟩ := by native_decide
example : simpleQualityTypeRequiredMissingCosted #[`w] #[`t, `y]
    (twoThingTables #[.unary .qualityType 0 0]) 0 0 "fallback" = ⟨"fallback", 63⟩ := by native_decide
example : simpleQualityTypeEvidenceCosted #[`w] #[`t, `y]
    (twoThingTables #[.unary .qualityType 0 0]) 0 0 =
    ⟨#["  - User assertion: `SimpleQualityType(t)`.", "  - Computed SimpleQualityType: true; every current instance is a computed `SimpleQuality`."], 70⟩ := by native_decide
example : simpleQualityTypeRequiredMissingCosted #[] #[] {} 7 3 "fallback" =
    ⟨"`SimpleQualityType(#7)` requires `QualityType(#7)`; missing that primitive classification.", 12⟩ := by native_decide
example : simpleQualityTypeEvidenceCosted #[] #[] {} 7 3 =
    ⟨#["  - User assertion: `SimpleQualityType(#7)`.",
      "  - Computed SimpleQualityType: false, because `QualityType(#7)` is not true at `#3`."], 23⟩ := by native_decide
example : complexQualityTypeRequiredMissingCosted #[`w] #[`t, `y] (twoThingTables #[]) 0 0 "fallback" =
    ⟨"`ComplexQualityType(t)` requires `QualityType(t)`; missing that primitive classification.", 22⟩ := by native_decide
example : complexQualityTypeEvidenceCosted #[`w] #[`t, `y] (twoThingTables #[]) 0 0 =
    ⟨#["  - User assertion: `ComplexQualityType(t)`.", "  - Computed ComplexQualityType: false, because `QualityType(t)` is not true at `w`."], 33⟩ := by native_decide
example : complexQualityTypeRequiredMissingCosted #[`w] #[`t, `y] (twoThingTables #[.binary .inst 0 0 0, .binary .inst 1 0 0]) 0 0 "fallback" =
    ⟨"`ComplexQualityType(t)` requires `QualityType(t)`; missing that primitive classification.", 22⟩ := by native_decide
example : complexQualityTypeEvidenceCosted #[`w] #[`t, `y] (twoThingTables #[.binary .inst 0 0 0, .binary .inst 1 0 0]) 0 0 =
    ⟨#["  - User assertion: `ComplexQualityType(t)`.", "  - Computed ComplexQualityType: false, because `QualityType(t)` is not true at `w`."], 33⟩ := by native_decide
example : complexQualityTypeRequiredMissingCosted #[`w] #[`t, `y] (twoThingTables #[.unary .qualityType 0 0, .binary .inst 0 0 0]) 0 0 "fallback" =
    ⟨"`ComplexQualityType(t)` requires every instance to be a computed `ComplexQuality`; instance `t` is not complex.", 88⟩ := by native_decide
example : complexQualityTypeEvidenceCosted #[`w] #[`t, `y] (twoThingTables #[.unary .qualityType 0 0, .binary .inst 0 0 0]) 0 0 =
    ⟨#["  - User assertion: `ComplexQualityType(t)`.",
      "  - Computed ComplexQualityType: false, because instance `t` is not a computed `ComplexQuality` at `w`.",
      "  - Computed Quality: false, because `t` instantiates no `QualityKind` at this world."], 149⟩ := by native_decide
example : complexQualityTypeRequiredMissingCosted #[`w] #[`t, `y] (twoThingTables #[.unary .qualityType 0 0, .binary .inst 1 0 0]) 0 0 "fallback" =
    ⟨"`ComplexQualityType(t)` requires every instance to be a computed `ComplexQuality`; instance `y` is not complex.", 107⟩ := by native_decide
example : complexQualityTypeEvidenceCosted #[`w] #[`t, `y] (twoThingTables #[.unary .qualityType 0 0, .binary .inst 1 0 0]) 0 0 =
    ⟨#["  - User assertion: `ComplexQualityType(t)`.",
      "  - Computed ComplexQualityType: false, because instance `y` is not a computed `ComplexQuality` at `w`.",
      "  - Computed Quality: false, because `y` instantiates no `QualityKind` at this world."], 168⟩ := by native_decide
example : complexQualityTypeRequiredMissingCosted #[`w] #[`t, `y] (twoThingTables #[.unary .qualityType 0 0, .binary .inst 1 0 0, .binary .inst 0 0 0]) 0 0 "fallback" =
    ⟨"`ComplexQualityType(t)` requires every instance to be a computed `ComplexQuality`; instance `t` is not complex.", 88⟩ := by native_decide
example : complexQualityTypeEvidenceCosted #[`w] #[`t, `y] (twoThingTables #[.unary .qualityType 0 0, .binary .inst 1 0 0, .binary .inst 0 0 0]) 0 0 =
    ⟨#["  - User assertion: `ComplexQualityType(t)`.",
      "  - Computed ComplexQualityType: false, because instance `t` is not a computed `ComplexQuality` at `w`.",
      "  - Computed Quality: false, because `t` instantiates no `QualityKind` at this world."], 149⟩ := by native_decide
example : complexQualityTypeRequiredMissingCosted #[`w] #[`t, `y] (twoThingTables #[.unary .qualityType 0 0, .binary .inst 1 0 0, .binary .inst 1 0 0]) 0 0 "fallback" =
    ⟨"`ComplexQualityType(t)` requires every instance to be a computed `ComplexQuality`; instance `y` is not complex.", 107⟩ := by native_decide
example : complexQualityTypeEvidenceCosted #[`w] #[`t, `y] (twoThingTables #[.unary .qualityType 0 0, .binary .inst 1 0 0, .binary .inst 1 0 0]) 0 0 =
    ⟨#["  - User assertion: `ComplexQualityType(t)`.",
      "  - Computed ComplexQualityType: false, because instance `y` is not a computed `ComplexQuality` at `w`.",
      "  - Computed Quality: false, because `y` instantiates no `QualityKind` at this world."], 168⟩ := by native_decide
example : complexQualityTypeRequiredMissingCosted #[`w] #[`t, `y]
    (twoThingTables #[.unary .qualityType 0 0]) 0 0 "fallback" = ⟨"fallback", 63⟩ := by native_decide
example : complexQualityTypeEvidenceCosted #[`w] #[`t, `y]
    (twoThingTables #[.unary .qualityType 0 0]) 0 0 =
    ⟨#["  - User assertion: `ComplexQualityType(t)`.", "  - Computed ComplexQualityType: true; every current instance is a computed `ComplexQuality`."], 70⟩ := by native_decide
example : complexQualityTypeRequiredMissingCosted #[] #[] {} 7 3 "fallback" =
    ⟨"`ComplexQualityType(#7)` requires `QualityType(#7)`; missing that primitive classification.", 12⟩ := by native_decide
example : complexQualityTypeEvidenceCosted #[] #[] {} 7 3 =
    ⟨#["  - User assertion: `ComplexQualityType(#7)`.",
      "  - Computed ComplexQualityType: false, because `QualityType(#7)` is not true at `#3`."], 23⟩ := by native_decide

-- A valid quality can still violate the simple/complex condition. Its extra
-- status row remains positive, distinguishing quality from the part condition.
example : simpleQualityTypeRequiredMissingCosted #[`w] #[`t, `y] (twoThingTables #[ .unary .qualityType 0 0, .unary .qualityKind 0 0, .binary .inst 1 0 0, .binary .inheresIn 0 1 0]) 0 0 "fallback" =
    ⟨"`SimpleQualityType(t)` requires every instance to be a computed `SimpleQuality`; instance `y` is not simple.", 150⟩ := by native_decide
example : simpleQualityTypeEvidenceCosted #[`w] #[`t, `y] (twoThingTables #[ .unary .qualityType 0 0, .unary .qualityKind 0 0, .binary .inst 1 0 0, .binary .inheresIn 0 1 0]) 0 0 =
    ⟨#["  - User assertion: `SimpleQualityType(t)`.",
      "  - Computed SimpleQualityType: false, because instance `y` is not a computed `SimpleQuality` at `w`.",
      "  - Computed Quality: true, uniquely witnessed by `QualityKind(t)` and `y :: t`."], 241⟩ := by native_decide
example : complexQualityTypeRequiredMissingCosted #[`w] #[`t, `y] (twoThingTables #[ .unary .qualityType 0 0, .unary .qualityKind 0 0, .binary .inst 1 0 0]) 0 0 "fallback" =
    ⟨"`ComplexQualityType(t)` requires every instance to be a computed `ComplexQuality`; instance `y` is not complex.", 168⟩ := by native_decide
example : complexQualityTypeEvidenceCosted #[`w] #[`t, `y] (twoThingTables #[ .unary .qualityType 0 0, .unary .qualityKind 0 0, .binary .inst 1 0 0]) 0 0 =
    ⟨#["  - User assertion: `ComplexQualityType(t)`.",
      "  - Computed ComplexQualityType: false, because instance `y` is not a computed `ComplexQuality` at `w`.",
      "  - Computed Quality: true, uniquely witnessed by `QualityKind(t)` and `y :: t`."], 259⟩ := by native_decide
example : simpleQualityTypeEvidenceCosted #[`w] #[`t, `y] (twoThingTables #[.unary .qualityType 0 0, .unary .qualityKind 0 0, .binary .inst 1 0 0]) 0 0 =
    ⟨#["  - User assertion: `SimpleQualityType(t)`.", "  - Computed SimpleQualityType: true; every current instance is a computed `SimpleQuality`."], 167⟩ := by native_decide
example : complexQualityTypeEvidenceCosted #[`w] #[`t, `y] (twoThingTables #[.unary .qualityType 0 0, .unary .qualityKind 0 0, .binary .inst 1 0 0, .binary .inheresIn 0 1 0]) 0 0 =
    ⟨#["  - User assertion: `ComplexQualityType(t)`.", "  - Computed ComplexQualityType: true; every current instance is a computed `ComplexQuality`."], 149⟩ := by native_decide

example (worlds things : Array Name) (tables : FactTables) (x w : Nat) (fallback : String) :
    (simpleQualityTypeRequiredMissingCosted worlds things tables x w fallback).cost ≤
      things.size * (55 * things.size + 27) + 27 :=
  simpleQualityTypeRequiredMissingCosted_cost_le worlds things tables x w fallback
example (worlds things : Array Name) (tables : FactTables) (x w : Nat) :
    (simpleQualityTypeEvidenceCosted worlds things tables x w).cost ≤
      things.size * (55 * things.size + 27) + 44 * things.size + 66 :=
  simpleQualityTypeEvidenceCosted_cost_le worlds things tables x w
example (worlds things : Array Name) (tables : FactTables) (x w : Nat) :
    (simpleQualityTypeEvidenceCosted worlds things tables x w).value.size ≤ 3 :=
  simpleQualityTypeEvidenceCosted_size_le worlds things tables x w
example (worlds things : Array Name) (tables : FactTables) (x w : Nat) (fallback : String) :
    (complexQualityTypeRequiredMissingCosted worlds things tables x w fallback).cost ≤
      things.size * (55 * things.size + 27) + 27 :=
  complexQualityTypeRequiredMissingCosted_cost_le worlds things tables x w fallback
example (worlds things : Array Name) (tables : FactTables) (x w : Nat) :
    (complexQualityTypeEvidenceCosted worlds things tables x w).cost ≤
      things.size * (55 * things.size + 27) + 44 * things.size + 66 :=
  complexQualityTypeEvidenceCosted_cost_le worlds things tables x w
example (worlds things : Array Name) (tables : FactTables) (x w : Nat) :
    (complexQualityTypeEvidenceCosted worlds things tables x w).value.size ≤ 3 :=
  complexQualityTypeEvidenceCosted_size_le worlds things tables x w
example {T₁ T₂ : Nat} (h : T₁ ≤ T₂) :
    T₁ * (55 * T₁ + 27) + 27 ≤ T₂ * (55 * T₂ + 27) + 27 := by
  have hp := Nat.mul_le_mul h (show 55 * T₁ + 27 ≤ 55 * T₂ + 27 by omega)
  omega
example {T₁ T₂ : Nat} (h : T₁ ≤ T₂) :
    T₁ * (55 * T₁ + 27) + 44 * T₁ + 66 ≤ T₂ * (55 * T₂ + 27) + 44 * T₂ + 66 := by
  have hp := Nat.mul_le_mul h (show 55 * T₁ + 27 ≤ 55 * T₂ + 27 by omega)
  omega

example : ((derivedAssertionFailure? #[`w] #[`t, `y]
    #[.derived (.unary "SimpleQualityType" "t") .everywhere]
    #[.derived (fun _ => "unused") .everywhere] (twoThingTables #[])).getD #[])[1]? =
    some "Required but missing: `SimpleQualityType(t)` requires `QualityType(t)`; missing that primitive classification." := by native_decide
example : ((derivedAssertionFailure? #[`w] #[`t, `y]
    #[.derived (.unary "SimpleQualityType" "t") .everywhere]
    #[.derived (fun _ => "unused") .everywhere] (twoThingTables #[])).getD #[])[5]? =
    some "  - Computed SimpleQualityType: false, because `QualityType(t)` is not true at `w`." := by native_decide
example : ((derivedAssertionFailure? #[`w] #[`t, `y]
    #[.derived (.unary "SimpleQualityType" "t") .everywhere]
    #[.derived (fun _ => "unused") .everywhere] (twoThingTables #[.unary .qualityType 0 0, .binary .inst 1 0 0, .binary .inst 0 0 0])).getD #[])[1]? =
    some "Required but missing: `SimpleQualityType(t)` requires every instance to be a computed `SimpleQuality`; instance `t` is not simple." := by native_decide
example : ((derivedAssertionFailure? #[`w] #[`t, `y]
    #[.derived (.unary "SimpleQualityType" "t") .everywhere]
    #[.derived (fun _ => "unused") .everywhere] (twoThingTables #[.unary .qualityType 0 0, .binary .inst 1 0 0, .binary .inst 0 0 0])).getD #[])[5]? =
    some "  - Computed SimpleQualityType: false, because instance `t` is not a computed `SimpleQuality` at `w`." := by native_decide
example : ((derivedAssertionFailure? #[`w] #[`t, `y]
    #[.derived (.unary "SimpleQualityType" "t") .everywhere]
    #[.derived (fun _ => "unused") .everywhere] (twoThingTables #[.unary .qualityType 0 0, .binary .inst 1 0 0, .binary .inst 0 0 0])).getD #[])[6]? =
    some "  - Computed Quality: false, because `t` instantiates no `QualityKind` at this world." := by native_decide
example : ((derivedAssertionFailure? #[`w] #[`t, `y]
    #[.derived (.unary "ComplexQualityType" "t") .everywhere]
    #[.derived (fun _ => "unused") .everywhere] (twoThingTables #[])).getD #[])[1]? =
    some "Required but missing: `ComplexQualityType(t)` requires `QualityType(t)`; missing that primitive classification." := by native_decide
example : ((derivedAssertionFailure? #[`w] #[`t, `y]
    #[.derived (.unary "ComplexQualityType" "t") .everywhere]
    #[.derived (fun _ => "unused") .everywhere] (twoThingTables #[])).getD #[])[5]? =
    some "  - Computed ComplexQualityType: false, because `QualityType(t)` is not true at `w`." := by native_decide
example : ((derivedAssertionFailure? #[`w] #[`t, `y]
    #[.derived (.unary "ComplexQualityType" "t") .everywhere]
    #[.derived (fun _ => "unused") .everywhere] (twoThingTables #[.unary .qualityType 0 0, .binary .inst 1 0 0, .binary .inst 0 0 0])).getD #[])[1]? =
    some "Required but missing: `ComplexQualityType(t)` requires every instance to be a computed `ComplexQuality`; instance `t` is not complex." := by native_decide
example : ((derivedAssertionFailure? #[`w] #[`t, `y]
    #[.derived (.unary "ComplexQualityType" "t") .everywhere]
    #[.derived (fun _ => "unused") .everywhere] (twoThingTables #[.unary .qualityType 0 0, .binary .inst 1 0 0, .binary .inst 0 0 0])).getD #[])[5]? =
    some "  - Computed ComplexQualityType: false, because instance `t` is not a computed `ComplexQuality` at `w`." := by native_decide
example : ((derivedAssertionFailure? #[`w] #[`t, `y]
    #[.derived (.unary "ComplexQualityType" "t") .everywhere]
    #[.derived (fun _ => "unused") .everywhere] (twoThingTables #[.unary .qualityType 0 0, .binary .inst 1 0 0, .binary .inst 0 0 0])).getD #[])[6]? =
    some "  - Computed Quality: false, because `t` instantiates no `QualityKind` at this world." := by native_decide

-- The bearer report always reads the classification and reconstructs the path.
-- With valid coordinates, common work costs 38. A missing path adds 13 for
-- traversal and ten for text. A direct path adds 18 for traversal and 19 for
-- its two names and surrounding text. Classification changes neither total.
example : ultimateBearerEvidenceCosted #[`w] #[`x, `y] (twoThingTables #[]) 0 1 0 =
    ⟨#["  - User assertion: `UltimateBearerOf(x, y)`.",
       "  - Bearer `x` is a Moment: false.",
       "  - no `InheresIn` path reaches `x` from `y` at `w`."], 61⟩ := by native_decide
example : ultimateBearerEvidenceCosted #[`w] #[`x, `y]
    (twoThingTables #[.binary .inheresIn 1 0 0]) 0 1 0 =
    ⟨#["  - User assertion: `UltimateBearerOf(x, y)`.",
       "  - Bearer `x` is a Moment: false.",
       "  - `InheresIn` path exists: y InheresIn x."], 75⟩ := by native_decide
example : ultimateBearerEvidenceCosted #[`w] #[`x, `y]
    (twoThingTables #[.unary .moment 0 0, .binary .inheresIn 1 0 0]) 0 1 0 =
    ⟨#["  - User assertion: `UltimateBearerOf(x, y)`.",
       "  - Bearer `x` is a Moment: true.",
       "  - `InheresIn` path exists: y InheresIn x."], 75⟩ := by native_decide
example : ultimateBearerEvidenceCosted #[`w] #[`x, `y]
    (twoThingTables #[.binary .inheresIn 1 0 0, .binary .inheresIn 1 0 0,
      .binary .sub 0 1 0]) 0 1 0 =
    ultimateBearerEvidenceCosted #[`w] #[`x, `y]
      (twoThingTables #[.binary .inheresIn 1 0 0]) 0 1 0 := by native_decide
example : ultimateBearerEvidenceCosted #[`w] #[`x, `y]
    (twoThingTables #[.binary .inheresIn 0 1 0]) 0 1 0 =
    ultimateBearerEvidenceCosted #[`w] #[`x, `y] (twoThingTables #[]) 0 1 0 := by native_decide

-- Two hops cost 29, and joining three names with the path prefix/suffix costs
-- 28. The total is 38+29+28. A cycle must not prevent bounded reconstruction.
example : ultimateBearerEvidenceCosted #[`w] #[`x, `y, `z]
    (compileExplicitModelAST {
      worldCount := 1, thingCount := 3,
      facts := #[.binary .inheresIn 0 1 0, .binary .inheresIn 1 0 0,
        .binary .inheresIn 1 2 0] }) 2 0 0 =
    ⟨#["  - User assertion: `UltimateBearerOf(z, x)`.",
       "  - Bearer `z` is a Moment: false.",
       "  - `InheresIn` path exists: x InheresIn y InheresIn z."], 95⟩ := by native_decide

-- Raw malformed tables are also bounded: a looping next hop consumes the
-- two-hop allowance and returns no path. This is a termination regression,
-- not evidence that raw next-hop entries describe valid inherence edges.
example : (ultimateBearerEvidenceCosted #[`w] #[`x, `y]
    { twoThingTables #[] with inherenceNextHops := #[#[none, some 0]] } 1 0 0).cost = 77 := by
  native_decide
example : ultimateBearerEvidenceCosted #[] #[] {} 7 8 3 =
    ⟨#["  - User assertion: `UltimateBearerOf(#7, #8)`.",
       "  - Bearer `#7` is a Moment: false.",
       "  - no `InheresIn` path reaches `#7` from `#8` at `#3`."], 40⟩ := by native_decide
example : ultimateBearerRequiredMissingCosted #[`w] #[`x, `y] (twoThingTables #[]) 0 1 0 =
    ⟨"`UltimateBearerOf(x, y)` requires an `InheresIn` path from `y` to bearer `x`; missing that path at `w`.", 35⟩ := by native_decide
example : ultimateBearerRequiredMissingCosted #[`w] #[`x, `y]
    (twoThingTables #[.unary .moment 0 0]) 0 1 0 =
    ⟨"`UltimateBearerOf(x, y)` requires bearer `x` not to be a `Moment`; conflicting `Moment(x)` holds.", 29⟩ := by native_decide

-- A one-row mode status adds 14 operations: eleven for the two introductory
-- rows and three for copying the status row. A missing Mode costs 29 in the
-- status builder and skips even a large array of declared candidates.
example : (externalModeEvidenceCosted #[`w] #[`x, `y] (twoThingTables #[]) 0 0).cost = 43 := by
  native_decide
example : externalModeEvidenceCosted #[`w] #[`x, `y]
    { twoThingTables #[] with derivedProps := Array.replicate 1000 "unused" } 0 0 =
    externalModeEvidenceCosted #[`w] #[`x, `y] (twoThingTables #[]) 0 0 := by native_decide
example : (externalModeEvidenceCosted #[] #[] {} 7 3).cost = 33 := by native_decide
example : externalModeEvidenceCosted #[`w] #[`x, `y]
    (twoThingTables #[.unary .mode 0 0]) 0 0 =
    ⟨#["  - User assertion: `ExternallyDependentMode(x)`.",
       "  - Certification treats this as a computed predicate, not as a primitive classification.",
       "  - Computed ExternallyDependentMode: true, witnessed by x, y."], 181⟩ := by native_decide
example : externalModeEvidenceCosted #[`w] #[`x, `y] declaredModeFailureTables 0 0 =
    ⟨#["  - User assertion: `ExternallyDependentMode(x)`.",
       "  - Certification treats this as a computed predicate, not as a primitive classification.",
       "  - Computed ExternallyDependentMode: false. `x` is a `Mode`, but no thing witnesses computed `ExternallyDependent(x, y)`.",
       "  - First candidate check: `x` exists at `w`, but `y` does not; this breaks existential dependence.",
       "  - Note: asserted `ExternallyDependent` facts name candidate(s) y, but certification uses the computed external-dependence semantics."], 284⟩ := by native_decide

-- A non-vacuous witness spans three worlds: x exists with y and bearer z,
-- y also exists without z, and z also exists without y. The complete status
-- costs 674, followed by fourteen operations for the prefix and row copy.
example : externalModeEvidenceCosted #[`actual, `yOnly, `zOnly] #[`x, `y, `z]
    (compileExplicitModelAST {
      worldCount := 3, thingCount := 3,
      facts := #[.unary .ex 0 0, .unary .ex 1 0, .unary .ex 1 1,
        .unary .ex 2 0, .unary .ex 2 2, .unary .mode 0 0,
        .binary .inheresIn 0 2 0] }) 0 0 =
    ⟨#["  - User assertion: `ExternallyDependentMode(x)`.",
       "  - Certification treats this as a computed predicate, not as a primitive classification.",
       "  - Computed ExternallyDependentMode: true, witnessed by y."], 688⟩ := by native_decide

-- Public reports keep the classification and path even when the classification
-- alone refutes the assertion. Mode reports retain the declared-candidate note.
example : ((derivedAssertionFailure? #[`w] #[`x, `y]
    #[.derived (.binary "UltimateBearerOf" "x" "y") .everywhere]
    #[.derived (fun _ => "unused") .everywhere]
    (twoThingTables #[.unary .moment 0 0, .binary .inheresIn 1 0 0])).getD #[])[6]? =
    some "  - `InheresIn` path exists: y InheresIn x." := by native_decide
example : ((derivedAssertionFailure? #[`w] #[`x, `y]
    #[.derived (.unary "ExternallyDependentMode" "x") .everywhere]
    #[.derived (fun _ => "unused") .everywhere] declaredModeFailureTables).getD #[])[8]? =
    some "  - Note: asserted `ExternallyDependent` facts name candidate(s) y, but certification uses the computed external-dependence semantics." := by native_decide

example (worlds things : Array Name) (tables : FactTables) (x y w : Nat) :
    (ultimateBearerRequiredMissingCosted worlds things tables x y w).cost ≤ 35 :=
  ultimateBearerRequiredMissingCosted_cost_le worlds things tables x y w
example (worlds things : Array Name) (tables : FactTables) (x y w : Nat) :
    (ultimateBearerEvidenceCosted worlds things tables x y w).cost ≤ 20 * things.size + 57 :=
  ultimateBearerEvidenceCosted_cost_le worlds things tables x y w
example (worlds things : Array Name) (tables : FactTables) (x y w : Nat) :
    (ultimateBearerEvidenceCosted worlds things tables x y w).value.size = 3 :=
  ultimateBearerEvidenceCosted_size worlds things tables x y w
example (worlds things : Array Name) (tables : FactTables) (x w : Nat) :
    (externalModeEvidenceCosted worlds things tables x w).value.size ≤ 5 :=
  externalModeEvidenceCosted_size_le worlds things tables x w
example (worlds things : Array Name) (tables : FactTables) (x w : Nat) :
    (externalModeEvidenceCosted worlds things tables x w).cost ≤
      things.size * (28 * worlds.size + things.size * (56 * worlds.size + 22) + 6) +
      things.size * (4 * tables.derivedProps.size + 51) +
      (30 * worlds.size + things.size * (60 * worlds.size + 40) + 28) + 65 := by
  have h := externalModeEvidenceCosted_cost_le worlds things tables x w
  simp only [externallyDependentModeStatusCostBound, externallyDependentWitnessCostBound] at h
  omega
example {T₁ T₂ : Nat} (h : T₁ ≤ T₂) : 20 * T₁ + 57 ≤ 20 * T₂ + 57 := by omega
example {W₁ W₂ T₁ T₂ D₁ D₂ : Nat} (hw : W₁ ≤ W₂) (ht : T₁ ≤ T₂) (hd : D₁ ≤ D₂) :
    T₁ * (28 * W₁ + T₁ * (56 * W₁ + 22) + 6) + T₁ * (4 * D₁ + 51) +
      (30 * W₁ + T₁ * (60 * W₁ + 40) + 28) + 65 ≤
    T₂ * (28 * W₂ + T₂ * (56 * W₂ + 22) + 6) + T₂ * (4 * D₂ + 51) +
      (30 * W₂ + T₂ * (60 * W₂ + 40) + 28) + 65 := by
  have hi := Nat.mul_le_mul ht (show 56 * W₁ + 22 ≤ 56 * W₂ + 22 by omega)
  have he := Nat.mul_le_mul ht
    (show 28 * W₁ + T₁ * (56 * W₁ + 22) + 6 ≤
      28 * W₂ + T₂ * (56 * W₂ + 22) + 6 by omega)
  have hd' := Nat.mul_le_mul ht (show 4 * D₁ + 51 ≤ 4 * D₂ + 51 by omega)
  have hr := Nat.mul_le_mul ht (show 60 * W₁ + 40 ≤ 60 * W₂ + 40 by omega)
  omega

-- A one-world failed implication costs 30 to search and 19 to explain.
-- External-dependence required-missing text adds 15; three-row evidence adds
-- 20. Unrelated inherence facts cannot trigger a bearer search on this path.
example : externallyDependentRequiredMissingCosted #[`w] #[`x, `y]
    (twoThingTables #[.unary .ex 0 0]) 0 1 0 =
    ⟨"`ExternallyDependent(x, y)` requires existential dependence plus independence from every bearer of `x`; missing condition: `x` exists at `w`, but `y` does not; this breaks existential dependence.", 64⟩ := by native_decide
example : externallyDependentEvidenceCosted #[`w] #[`x, `y]
    (twoThingTables #[.unary .ex 0 0]) 0 1 0 =
    ⟨#["  - User assertion: `ExternallyDependent(x, y)`.",
       "  - Certification computes this from existential dependence plus existential independence from every bearer.",
       "  - Computed ExternallyDependent: false. `x` exists at `w`, but `y` does not; this breaks existential dependence."], 69⟩ := by native_decide
example : externallyDependentEvidenceCosted #[`w] #[`x, `y]
    (twoThingTables #[.unary .ex 0 0, .unary .ex 0 0,
      .binary .inheresIn 0 0 0, .binary .inheresIn 0 1 0]) 0 1 0 =
    externallyDependentEvidenceCosted #[`w] #[`x, `y]
      (twoThingTables #[.unary .ex 0 0]) 0 1 0 := by native_decide
example : (externallyDependentRequiredMissingCosted #[] #[] {} 7 8 3).cost = 17 := by native_decide
example : (externallyDependentEvidenceCosted #[] #[] {} 7 8 3).cost = 22 := by native_decide

-- Once the existence implication holds, the bearer scan must run. It costs
-- 121 here, followed by 27 to render the bearer reason. Together with the
-- implication search (30), match (one), and report (twenty), the total is 199.
example : externallyDependentEvidenceCosted #[`w] #[`x, `y]
    (twoThingTables #[.unary .ex 0 0, .unary .ex 1 0,
      .binary .inheresIn 0 1 0]) 0 1 0 =
    ⟨#["  - User assertion: `ExternallyDependent(x, y)`.",
       "  - Certification computes this from existential dependence plus existential independence from every bearer.",
       "  - Computed ExternallyDependent: false. `x` inheres in `y` at `w`, but `y` is not existentially independent from that bearer: the assertion needs one witness world where Ex(y) holds without Ex(y), and one witness world where Ex(y) holds without Ex(y); neither witness exists in the current `Ex` facts."], 199⟩ := by native_decide

-- Without Ex(x), the world costs 17 and no failure is found. A failed
-- implication costs 30. The required-missing formatter adds one for a
-- fallback or 25 for a witness; evidence adds eighteen or 28 respectively.
example : existentialDependenceRequiredMissingCosted #[`w] #[`x, `y]
    (twoThingTables #[]) 0 1 "fallback" = ⟨"fallback", 18⟩ := by native_decide
example : existentialDependenceRequiredMissingCosted #[`w] #[`x, `y]
    (twoThingTables #[.unary .ex 0 0]) 0 1 "fallback" =
    ⟨"`ExistentialDependence(x, y)` requires `Ex(y)` in every world where `Ex(x)` holds; missing `Ex(y)` at `w`.", 55⟩ := by native_decide
example : existentialDependenceEvidenceCosted #[`w] #[`x, `y]
    (twoThingTables #[.unary .ex 0 0]) 0 1 =
    ⟨#["  - User assertion: `ExistentialDependence(x, y)`.",
       "  - Computed ExistentialDependence: false, because `x` exists at `w` but `y` does not."], 58⟩ := by native_decide
example : (existentialDependenceEvidenceCosted #[`w] #[`x, `y] (twoThingTables #[]) 0 1).cost = 35 := by native_decide
example : existentialDependenceRequiredMissingCosted #[] #[] {} 7 8 "fallback" =
    ⟨"fallback", 1⟩ := by native_decide
example : (existentialDependenceEvidenceCosted #[] #[] {} 7 8).cost = 18 := by native_decide

private def twoWorldModalTables (facts : Array CompiledFact) : FactTables :=
  compileExplicitModelAST { worldCount := 2, thingCount := 2, facts }

-- The first world is retained even when both fail. A later failure requires
-- the earlier world's query; duplicates and declaration order do not change it.
example : existentialDependenceEvidenceCosted #[`first, `last] #[`x, `y]
    (twoWorldModalTables #[.unary .ex 0 1, .unary .ex 0 0, .unary .ex 0 0]) 0 1 =
    ⟨#["  - User assertion: `ExistentialDependence(x, y)`.",
       "  - Computed ExistentialDependence: false, because `x` exists at `first` but `y` does not."], 61⟩ := by native_decide
example : existentialDependenceEvidenceCosted #[`first, `last] #[`x, `y]
    (twoWorldModalTables #[.unary .ex 0 1]) 0 1 =
    ⟨#["  - User assertion: `ExistentialDependence(x, y)`.",
       "  - Computed ExistentialDependence: false, because `x` exists at `last` but `y` does not."], 75⟩ := by native_decide

-- Missing both separation witnesses costs 17+17+18 in the shared reason.
-- Missing only the reverse witness costs 30+17+14. Independence evidence adds
-- twenty, including its match and both rows. Both searches still run.
example : existentialIndependenceRequiredMissingCosted #[`w] #[`x, `y]
    (twoThingTables #[]) 0 1 "fallback" =
    ⟨"`ExistentialIndependence(x, y)` requires two modal `Ex` separation witnesses; missing condition: the assertion needs one witness world where Ex(x) holds without Ex(y), and one witness world where Ex(y) holds without Ex(x); neither witness exists in the current `Ex` facts.", 67⟩ := by native_decide
example : (existentialIndependenceEvidenceCosted #[`w] #[`x, `y]
    (twoThingTables #[]) 0 1).cost = 72 := by native_decide
example : existentialIndependenceEvidenceCosted #[`w] #[`x, `y]
    (twoThingTables #[.unary .ex 0 0]) 0 1 =
    ⟨#["  - User assertion: `ExistentialIndependence(x, y)`.",
       "  - Computed ExistentialIndependence: false: the assertion needs a witness world where Ex(y) holds without Ex(x), but no such world exists in the current `Ex` facts."], 81⟩ := by native_decide
example : (existentialIndependenceEvidenceCosted #[`w] #[`x, `y]
    (twoThingTables #[.unary .ex 1 0]) 0 1).cost = 81 := by native_decide
example : (existentialIndependenceEvidenceCosted #[`w] #[`x, `y]
    (twoThingTables #[.unary .ex 0 0, .unary .ex 1 0]) 0 1).cost = 98 := by native_decide
example : (existentialIndependenceEvidenceCosted #[] #[] {} 7 8).cost = 38 := by native_decide

-- With both witnesses present, the two searches cost 33 and 47. The reason
-- builder adds two matches and returns none. The wrappers must not invent a
-- failure: they return the supplied fallback or the no-reason evidence row.
example : existentialIndependenceRequiredMissingCosted #[`first, `last] #[`x, `y]
    (twoWorldModalTables #[.unary .ex 0 0, .unary .ex 1 1]) 0 1 "fallback" =
    ⟨"fallback", 83⟩ := by native_decide
example : existentialIndependenceEvidenceCosted #[`first, `last] #[`x, `y]
    (twoWorldModalTables #[.unary .ex 0 0, .unary .ex 1 1]) 0 1 =
    ⟨#["  - User assertion: `ExistentialIndependence(x, y)`.",
       "  - No concrete missing independence witness was isolated; inspect world-scoped `Ex` facts."], 100⟩ := by native_decide

example : ((derivedAssertionFailure? #[`w] #[`x, `y]
    #[.derived (.binary "ExternallyDependent" "x" "y") .everywhere]
    #[.derived (fun _ => "unused") .everywhere]
    (twoThingTables #[.unary .ex 0 0])).getD #[])[6]? =
    some "  - Computed ExternallyDependent: false. `x` exists at `w`, but `y` does not; this breaks existential dependence." := by native_decide
example : ((derivedAssertionFailure? #[`first, `last] #[`x, `y]
    #[.derived (.binary "ExistentialDependence" "x" "y") .everywhere]
    #[.derived (fun _ => "unused") .everywhere]
    (twoWorldModalTables #[.unary .ex 0 1])).getD #[])[5]? =
    some "  - Computed ExistentialDependence: false, because `x` exists at `last` but `y` does not." := by native_decide
example : ((derivedAssertionFailure? #[`w] #[`x, `y]
    #[.derived (.binary "ExistentialIndependence" "x" "y") .everywhere]
    #[.derived (fun _ => "unused") .everywhere]
    (twoThingTables #[.unary .ex 0 0])).getD #[])[5]? =
    some "  - Computed ExistentialIndependence: false: the assertion needs a witness world where Ex(y) holds without Ex(x), but no such world exists in the current `Ex` facts." := by native_decide

example (worlds things : Array Name) (tables : FactTables) (x y w : Nat) :
    (externallyDependentRequiredMissingCosted worlds things tables x y w).cost ≤ 30 * worlds.size + things.size * (60 * worlds.size + 40) + 43 :=
  externallyDependentRequiredMissingCosted_cost_le worlds things tables x y w
example (worlds things : Array Name) (tables : FactTables) (x y w : Nat) :
    (externallyDependentEvidenceCosted worlds things tables x y w).cost ≤ 30 * worlds.size + things.size * (60 * worlds.size + 40) + 48 :=
  externallyDependentEvidenceCosted_cost_le worlds things tables x y w
example (worlds things : Array Name) (tables : FactTables) (x y w : Nat) :
    (externallyDependentEvidenceCosted worlds things tables x y w).value.size = 3 :=
  externallyDependentEvidenceCosted_size worlds things tables x y w
example (worlds things : Array Name) (tables : FactTables) (x y : Nat) (fallback : String) :
    (existentialDependenceRequiredMissingCosted worlds things tables x y fallback).cost ≤ 30 * worlds.size + 25 :=
  existentialDependenceRequiredMissingCosted_cost_le worlds things tables x y fallback
example (worlds things : Array Name) (tables : FactTables) (x y : Nat) :
    (existentialDependenceEvidenceCosted worlds things tables x y).cost ≤ 30 * worlds.size + 28 :=
  existentialDependenceEvidenceCosted_cost_le worlds things tables x y
example (worlds things : Array Name) (tables : FactTables) (x y : Nat) :
    (existentialDependenceEvidenceCosted worlds things tables x y).value.size = 2 :=
  existentialDependenceEvidenceCosted_size worlds things tables x y
example (worlds things : Array Name) (tables : FactTables) (x y : Nat) (fallback : String) :
    (existentialIndependenceRequiredMissingCosted worlds things tables x y fallback).cost ≤ 60 * worlds.size + 33 :=
  existentialIndependenceRequiredMissingCosted_cost_le worlds things tables x y fallback
example (worlds things : Array Name) (tables : FactTables) (x y : Nat) :
    (existentialIndependenceEvidenceCosted worlds things tables x y).cost ≤ 60 * worlds.size + 38 :=
  existentialIndependenceEvidenceCosted_cost_le worlds things tables x y
example (worlds things : Array Name) (tables : FactTables) (x y : Nat) :
    (existentialIndependenceEvidenceCosted worlds things tables x y).value.size = 2 :=
  existentialIndependenceEvidenceCosted_size worlds things tables x y
example {W₁ W₂ T₁ T₂ : Nat} (hw : W₁ ≤ W₂) (ht : T₁ ≤ T₂) (c : Nat) :
    30 * W₁ + T₁ * (60 * W₁ + 40) + c ≤
      30 * W₂ + T₂ * (60 * W₂ + 40) + c := by
  have h := Nat.mul_le_mul ht (show 60 * W₁ + 40 ≤ 60 * W₂ + 40 by omega)
  omega
example {W₁ W₂ : Nat} (h : W₁ ≤ W₂) (c : Nat) :
    30 * W₁ + c ≤ 30 * W₂ + c ∧ 60 * W₁ + c ≤ 60 * W₂ + c := by omega

-- Typehood costs 59 for no possible instance, 21 for the first, and 59
-- for the last. A failed specialization search costs 43 or 84. Reports
-- preserve the typehood-first order and the supplied fallback on success.
example : categorizesRequiredMissingCosted #[`w] #[`a, `b, `c]
    (threeTypeTables #[]) 0 1 0 "fallback" =
    ⟨"`Categorizes(a, b)` requires `a` to be a computed `Type`; missing any possible instance.", 75⟩ := by native_decide
example : categorizesEvidenceCosted #[`w] #[`a, `b, `c]
    (threeTypeTables #[]) 0 1 0 =
    ⟨#["  - User assertion: `Categorizes(a, b)`.",
       "  - Computed Categorizes: false, because `a` is not a computed `Type`."], 80⟩ := by native_decide
example : categorizesRequiredMissingCosted #[`w] #[`a, `b, `c]
    (threeTypeTables #[.binary .inst 0 0 0]) 0 1 0 "fallback" =
    ⟨"`Categorizes(a, b)` requires each category-instance type to specialize `b`; missing `Sub(a, b)`.", 89⟩ := by native_decide
example : categorizesEvidenceCosted #[`w] #[`a, `b, `c]
    (threeTypeTables #[.binary .inst 0 0 0]) 0 1 0 =
    ⟨#["  - User assertion: `Categorizes(a, b)`.",
       "  - Computed Categorizes: false, because `a` instantiates `a` at `w` but `Sub(a, b)` is missing."], 102⟩ := by native_decide
example : categorizesRequiredMissingCosted #[`w] #[`a, `b, `c]
    (threeTypeTables #[.binary .inst 2 0 0]) 0 1 0 "fallback" =
    ⟨"`Categorizes(a, b)` requires each category-instance type to specialize `b`; missing `Sub(c, b)`.", 168⟩ := by native_decide
example : categorizesEvidenceCosted #[`w] #[`a, `b, `c]
    (threeTypeTables #[.binary .inst 2 0 0]) 0 1 0 =
    ⟨#["  - User assertion: `Categorizes(a, b)`.",
       "  - Computed Categorizes: false, because `c` instantiates `a` at `w` but `Sub(c, b)` is missing."], 181⟩ := by native_decide
example : categorizesRequiredMissingCosted #[`w] #[`a, `b, `c]
    (threeTypeTables #[.binary .inst 0 0 0, .binary .sub 0 1 0]) 0 1 0 "fallback" =
    ⟨"fallback", 108⟩ := by native_decide
example : categorizesEvidenceCosted #[`w] #[`a, `b, `c]
    (threeTypeTables #[.binary .inst 0 0 0, .binary .sub 0 1 0]) 0 1 0 =
    ⟨#["  - User assertion: `Categorizes(a, b)`.",
       "  - Computed Categorizes: true; every instance type of `a` specializes `b`."], 129⟩ := by native_decide

-- The three-thing shared-instance search costs 66 with none, 42 for the
-- first, and 83 for the last. Required-missing text adds 13 or 19;
-- evidence adds eighteen or thirty. No typehood scan is added to this report.
example : disjointTypesRequiredMissingCosted #[`w] #[`a, `b, `c]
    (threeTypeTables #[]) 0 1 0 =
    ⟨"`IsDisjointWith(a, b)` requires both arguments to be computed types and have no shared instance; missing typehood for one argument.", 79⟩ := by native_decide
example : disjointTypesEvidenceCosted #[`w] #[`a, `b, `c]
    (threeTypeTables #[]) 0 1 0 =
    ⟨#["  - User assertion: `IsDisjointWith(a, b)`.",
       "  - No shared instance was isolated; inspect typehood and instantiation facts."], 84⟩ := by native_decide
example : disjointTypesRequiredMissingCosted #[`w] #[`a, `b, `c]
    (threeTypeTables #[.binary .inst 0 0 0, .binary .inst 0 1 0]) 0 1 0 =
    ⟨"`IsDisjointWith(a, b)` requires no shared instance; `a` instantiates both types.", 61⟩ := by native_decide
example : disjointTypesEvidenceCosted #[`w] #[`a, `b, `c]
    (threeTypeTables #[.binary .inst 0 0 0, .binary .inst 0 1 0]) 0 1 0 =
    ⟨#["  - User assertion: `IsDisjointWith(a, b)`.",
       "  - Computed IsDisjointWith: false, because `a` instantiates both types at `w`."], 72⟩ := by native_decide
example : disjointTypesRequiredMissingCosted #[`w] #[`a, `b, `c]
    (threeTypeTables #[.binary .inst 2 0 0, .binary .inst 2 1 0]) 0 1 0 =
    ⟨"`IsDisjointWith(a, b)` requires no shared instance; `c` instantiates both types.", 102⟩ := by native_decide
example : disjointTypesEvidenceCosted #[`w] #[`a, `b, `c]
    (threeTypeTables #[.binary .inst 2 0 0, .binary .inst 2 1 0]) 0 1 0 =
    ⟨#["  - User assertion: `IsDisjointWith(a, b)`.",
       "  - Computed IsDisjointWith: false, because `c` instantiates both types at `w`."], 113⟩ := by native_decide

-- Coverage search costs 66 with no instances, 61 for the first failure,
-- and 102 for the last. A first-cover match saves seventeen operations
-- against a second-cover match. The evidence wrapper adds 24 or 38.
example : completeCoverageRequiredMissingCosted #[`w] #[`a, `b, `c]
    (threeTypeTables #[]) 0 1 2 0 "fallback" =
    ⟨"fallback", 67⟩ := by native_decide
example : completeCoverageEvidenceCosted #[`w] #[`a, `b, `c]
    (threeTypeTables #[]) 0 1 2 0 =
    ⟨#["  - User assertion: `IsCompletelyCoveredBy(a, b, c)`.",
       "  - Computed IsCompletelyCoveredBy: true; every current covered instance is assigned to at least one covering type."], 90⟩ := by native_decide
example : completeCoverageRequiredMissingCosted #[`w] #[`a, `b, `c]
    (threeTypeTables #[.binary .inst 0 0 0]) 0 1 2 0 "fallback" =
    ⟨"`IsCompletelyCoveredBy(a, b, c)` requires every `a` instance to instantiate at least one covering type; `a` instantiates neither `b` nor `c`.", 92⟩ := by native_decide
example : completeCoverageEvidenceCosted #[`w] #[`a, `b, `c]
    (threeTypeTables #[.binary .inst 0 0 0]) 0 1 2 0 =
    ⟨#["  - User assertion: `IsCompletelyCoveredBy(a, b, c)`.",
       "  - Computed IsCompletelyCoveredBy: false, because `a` instantiates `a` but instantiates neither covering type at `w`."], 99⟩ := by native_decide
example : completeCoverageRequiredMissingCosted #[`w] #[`a, `b, `c]
    (threeTypeTables #[.binary .inst 2 0 0]) 0 1 2 0 "fallback" =
    ⟨"`IsCompletelyCoveredBy(a, b, c)` requires every `a` instance to instantiate at least one covering type; `c` instantiates neither `b` nor `c`.", 133⟩ := by native_decide
example : completeCoverageEvidenceCosted #[`w] #[`a, `b, `c]
    (threeTypeTables #[.binary .inst 2 0 0]) 0 1 2 0 =
    ⟨#["  - User assertion: `IsCompletelyCoveredBy(a, b, c)`.",
       "  - Computed IsCompletelyCoveredBy: false, because `c` instantiates `a` but instantiates neither covering type at `w`."], 140⟩ := by native_decide
example : completeCoverageRequiredMissingCosted #[`w] #[`a, `b, `c]
    (threeTypeTables #[.binary .inst 0 0 0, .binary .inst 0 1 0]) 0 1 2 0 "fallback" =
    ⟨"fallback", 86⟩ := by native_decide
example : completeCoverageEvidenceCosted #[`w] #[`a, `b, `c]
    (threeTypeTables #[.binary .inst 0 0 0, .binary .inst 0 1 0]) 0 1 2 0 =
    ⟨#["  - User assertion: `IsCompletelyCoveredBy(a, b, c)`.",
       "  - Computed IsCompletelyCoveredBy: true; every current covered instance is assigned to at least one covering type."], 109⟩ := by native_decide
example : completeCoverageRequiredMissingCosted #[`w] #[`a, `b, `c]
    (threeTypeTables #[.binary .inst 0 0 0, .binary .inst 0 2 0]) 0 1 2 0 "fallback" =
    ⟨"fallback", 103⟩ := by native_decide
example : completeCoverageEvidenceCosted #[`w] #[`a, `b, `c]
    (threeTypeTables #[.binary .inst 0 0 0, .binary .inst 0 2 0]) 0 1 2 0 =
    ⟨#["  - User assertion: `IsCompletelyCoveredBy(a, b, c)`.",
       "  - Computed IsCompletelyCoveredBy: true; every current covered instance is assigned to at least one covering type."], 126⟩ := by native_decide

-- Partition reports run coverage first. With no covered instances or shared
-- instances, the two scans cost 66 each. An early coverage failure costs 61
-- and skips the shared-instance scan. Later/shared failures retain their index.
example : partitionRequiredMissingCosted #[`w] #[`a, `b, `c]
    (threeTypeTables #[]) 0 1 2 0 "fallback" =
    ⟨"fallback", 134⟩ := by native_decide
example : partitionEvidenceCosted #[`w] #[`a, `b, `c]
    (threeTypeTables #[]) 0 1 2 0 =
    ⟨#["  - User assertion: `IsPartitionedInto(a, b, c)`.",
       "  - Coverage and disjointness counterexamples were not isolated; inspect typehood and instantiation facts."], 157⟩ := by native_decide
example : partitionRequiredMissingCosted #[`w] #[`a, `b, `c]
    (threeTypeTables #[.binary .inst 0 0 0]) 0 1 2 0 "fallback" =
    ⟨"`IsPartitionedInto(a, b, c)` first requires complete coverage; `a` instantiates the partitioned type but neither part type.", 86⟩ := by native_decide
example : partitionEvidenceCosted #[`w] #[`a, `b, `c]
    (threeTypeTables #[.binary .inst 0 0 0]) 0 1 2 0 =
    ⟨#["  - User assertion: `IsPartitionedInto(a, b, c)`.",
       "  - Computed IsPartitionedInto: false, because coverage fails: `a` instantiates `a` but instantiates neither covering type at `w`."], 99⟩ := by native_decide
example : partitionRequiredMissingCosted #[`w] #[`a, `b, `c]
    (threeTypeTables #[.binary .inst 2 0 0]) 0 1 2 0 "fallback" =
    ⟨"`IsPartitionedInto(a, b, c)` first requires complete coverage; `c` instantiates the partitioned type but neither part type.", 127⟩ := by native_decide
example : partitionEvidenceCosted #[`w] #[`a, `b, `c]
    (threeTypeTables #[.binary .inst 2 0 0]) 0 1 2 0 =
    ⟨#["  - User assertion: `IsPartitionedInto(a, b, c)`.",
       "  - Computed IsPartitionedInto: false, because coverage fails: `c` instantiates `a` but instantiates neither covering type at `w`."], 140⟩ := by native_decide
example : partitionRequiredMissingCosted #[`w] #[`a, `b, `c]
    (threeTypeTables #[.binary .inst 0 0 0, .binary .inst 0 1 0, .binary .inst 0 2 0]) 0 1 2 0 "fallback" =
    ⟨"`IsPartitionedInto(a, b, c)` also requires disjoint parts; `a` instantiates both part types.", 153⟩ := by native_decide
example : partitionEvidenceCosted #[`w] #[`a, `b, `c]
    (threeTypeTables #[.binary .inst 0 0 0, .binary .inst 0 1 0, .binary .inst 0 2 0]) 0 1 2 0 =
    ⟨#["  - User assertion: `IsPartitionedInto(a, b, c)`.",
       "  - Computed IsPartitionedInto: false, because disjointness fails: `a` instantiates both covering types at `w`."], 164⟩ := by native_decide
example : partitionRequiredMissingCosted #[`w] #[`a, `b, `c]
    (threeTypeTables #[.binary .inst 2 0 0, .binary .inst 2 1 0, .binary .inst 2 2 0]) 0 1 2 0 "fallback" =
    ⟨"`IsPartitionedInto(a, b, c)` also requires disjoint parts; `c` instantiates both part types.", 194⟩ := by native_decide
example : partitionEvidenceCosted #[`w] #[`a, `b, `c]
    (threeTypeTables #[.binary .inst 2 0 0, .binary .inst 2 1 0, .binary .inst 2 2 0]) 0 1 2 0 =
    ⟨#["  - User assertion: `IsPartitionedInto(a, b, c)`.",
       "  - Computed IsPartitionedInto: false, because disjointness fails: `c` instantiates both covering types at `w`."], 205⟩ := by native_decide
example : partitionRequiredMissingCosted #[`w] #[`a, `b, `c]
    (threeTypeTables #[.binary .inst 0 0 0, .binary .inst 0 1 0, .binary .inst 1 2 0]) 0 1 2 0 "fallback" =
    ⟨"fallback", 170⟩ := by native_decide
example : partitionEvidenceCosted #[`w] #[`a, `b, `c]
    (threeTypeTables #[.binary .inst 0 0 0, .binary .inst 0 1 0, .binary .inst 1 2 0]) 0 1 2 0 =
    ⟨#["  - User assertion: `IsPartitionedInto(a, b, c)`.",
       "  - Coverage and disjointness counterexamples were not isolated; inspect typehood and instantiation facts."], 193⟩ := by native_decide

-- Empty domains still charge names and emitted rows when a report needs them.
example : (categorizesRequiredMissingCosted #[] #[] {} 7 8 3 "fallback").cost = 16 := by native_decide
example : (categorizesEvidenceCosted #[] #[] {} 7 8 3).cost = 21 := by native_decide
example : (disjointTypesRequiredMissingCosted #[] #[] {} 7 8 3).cost = 13 := by native_decide
example : (disjointTypesEvidenceCosted #[] #[] {} 7 8 3).cost = 18 := by native_decide
example : (completeCoverageRequiredMissingCosted #[] #[] {} 7 8 9 3 "fallback").cost = 1 := by native_decide
example : (completeCoverageEvidenceCosted #[] #[] {} 7 8 9 3).cost = 24 := by native_decide
example : (partitionRequiredMissingCosted #[] #[] {} 7 8 9 3 "fallback").cost = 2 := by native_decide
example : (partitionEvidenceCosted #[] #[] {} 7 8 9 3).cost = 25 := by native_decide

-- Coverage wins even when the parts also overlap at a different instance.
example : partitionEvidenceCosted #[`w] #[`a, `b, `c]
    (threeTypeTables #[.binary .inst 0 0 0, .binary .inst 1 1 0, .binary .inst 1 2 0]) 0 1 2 0 =
    partitionEvidenceCosted #[`w] #[`a, `b, `c]
      (threeTypeTables #[.binary .inst 0 0 0]) 0 1 2 0 := by native_decide
example : partitionRequiredMissingCosted #[`w] #[`a, `b, `c]
    (threeTypeTables #[.binary .inst 0 0 0, .binary .inst 1 1 0, .binary .inst 1 2 0]) 0 1 2 0 "fallback" =
    partitionRequiredMissingCosted #[`w] #[`a, `b, `c]
      (threeTypeTables #[.binary .inst 0 0 0]) 0 1 2 0 "fallback" := by native_decide

-- Reordered duplicates and later counterexamples retain the first coordinate.
example : disjointTypesEvidenceCosted #[`w] #[`a, `b, `c]
    (threeTypeTables #[.binary .inst 2 1 0, .binary .inst 2 0 0,
      .binary .inst 0 1 0, .binary .inst 0 0 0, .binary .inst 0 1 0]) 0 1 0 =
    disjointTypesEvidenceCosted #[`w] #[`a, `b, `c]
      (threeTypeTables #[.binary .inst 0 0 0, .binary .inst 0 1 0]) 0 1 0 := by native_decide
example : completeCoverageEvidenceCosted #[`w] #[`a, `b, `c]
    (threeTypeTables #[.binary .inst 2 0 0, .binary .inst 0 0 0, .binary .inst 0 0 0]) 0 1 2 0 =
    completeCoverageEvidenceCosted #[`w] #[`a, `b, `c]
      (threeTypeTables #[.binary .inst 0 0 0]) 0 1 2 0 := by native_decide
example : categorizesEvidenceCosted #[`w] #[`a, `b, `c]
    (threeTypeTables #[.binary .inst 2 0 0, .binary .inst 0 0 0, .binary .inst 0 0 0]) 0 1 0 =
    categorizesEvidenceCosted #[`w] #[`a, `b, `c]
      (threeTypeTables #[.binary .inst 0 0 0]) 0 1 0 := by native_decide

-- Instantiation direction and field identity matter. These reversed edges and
-- Sub facts create neither a shared instance nor a possible instance of a.
example : disjointTypesEvidenceCosted #[`w] #[`a, `b, `c]
    (threeTypeTables #[.binary .inst 0 2 0, .binary .inst 1 2 0,
      .binary .sub 2 0 0, .binary .sub 2 1 0]) 0 1 0 =
    disjointTypesEvidenceCosted #[`w] #[`a, `b, `c] (threeTypeTables #[]) 0 1 0 := by native_decide
example : categorizesEvidenceCosted #[`w] #[`a, `b, `c]
    (threeTypeTables #[.binary .inst 0 2 0, .binary .sub 2 0 0,
      .binary .sub 2 1 0]) 0 1 0 =
    categorizesEvidenceCosted #[`w] #[`a, `b, `c] (threeTypeTables #[]) 0 1 0 := by native_decide

-- Possible typehood searches all worlds; specialization checks the report
-- world. The later-world instance makes a a type but leaves no current failure.
example : categorizesRequiredMissingCosted #[`first, `last] #[`a, `b]
    (twoWorldModalTables #[.binary .inst 1 0 1]) 0 1 0 "fallback" =
    ⟨"fallback", 127⟩ := by native_decide
example : categorizesEvidenceCosted #[`first, `last] #[`a, `b]
    (twoWorldModalTables #[.binary .inst 1 0 1]) 0 1 0 =
    ⟨#["  - User assertion: `Categorizes(a, b)`.",
       "  - Computed Categorizes: true; every instance type of `a` specializes `b`."], 148⟩ := by native_decide

example (worlds things : Array Name) (tables : FactTables) (x y w : Nat) (fallback : String) :
    (categorizesRequiredMissingCosted worlds things tables x y w fallback).cost ≤ worlds.size * (things.size * 19 + 2) + 40 * things.size + 25 :=
  categorizesRequiredMissingCosted_cost_le worlds things tables x y w fallback

example (worlds things : Array Name) (tables : FactTables) (x y w : Nat) :
    (disjointTypesRequiredMissingCosted worlds things tables x y w).cost ≤ 39 * things.size + 19 :=
  disjointTypesRequiredMissingCosted_cost_le worlds things tables x y w

example (worlds things : Array Name) (tables : FactTables) (x y z w : Nat) (fallback : String) :
    (completeCoverageRequiredMissingCosted worlds things tables x y z w fallback).cost ≤ 58 * things.size + 31 :=
  completeCoverageRequiredMissingCosted_cost_le worlds things tables x y z w fallback

example (worlds things : Array Name) (tables : FactTables) (x y z w : Nat) (fallback : String) :
    (partitionRequiredMissingCosted worlds things tables x y z w fallback).cost ≤ 97 * things.size + 26 :=
  partitionRequiredMissingCosted_cost_le worlds things tables x y z w fallback

example (worlds things : Array Name) (tables : FactTables) (x y w : Nat) :
    (categorizesEvidenceCosted worlds things tables x y w).cost ≤ worlds.size * (things.size * 19 + 2) + 40 * things.size + 38 :=
  categorizesEvidenceCosted_cost_le worlds things tables x y w
example (worlds things : Array Name) (tables : FactTables) (x y w : Nat) :
    (categorizesEvidenceCosted worlds things tables x y w).value.size = 2 :=
  categorizesEvidenceCosted_size worlds things tables x y w

example (worlds things : Array Name) (tables : FactTables) (x y w : Nat) :
    (disjointTypesEvidenceCosted worlds things tables x y w).cost ≤ 39 * things.size + 30 :=
  disjointTypesEvidenceCosted_cost_le worlds things tables x y w
example (worlds things : Array Name) (tables : FactTables) (x y w : Nat) :
    (disjointTypesEvidenceCosted worlds things tables x y w).value.size = 2 :=
  disjointTypesEvidenceCosted_size worlds things tables x y w

example (worlds things : Array Name) (tables : FactTables) (x y z w : Nat) :
    (completeCoverageEvidenceCosted worlds things tables x y z w).cost ≤ 58 * things.size + 38 :=
  completeCoverageEvidenceCosted_cost_le worlds things tables x y z w
example (worlds things : Array Name) (tables : FactTables) (x y z w : Nat) :
    (completeCoverageEvidenceCosted worlds things tables x y z w).value.size = 2 :=
  completeCoverageEvidenceCosted_size worlds things tables x y z w

example (worlds things : Array Name) (tables : FactTables) (x y z w : Nat) :
    (partitionEvidenceCosted worlds things tables x y z w).cost ≤ 97 * things.size + 38 :=
  partitionEvidenceCosted_cost_le worlds things tables x y z w
example (worlds things : Array Name) (tables : FactTables) (x y z w : Nat) :
    (partitionEvidenceCosted worlds things tables x y z w).value.size = 2 :=
  partitionEvidenceCosted_size worlds things tables x y z w

example {W₁ W₂ T₁ T₂ : Nat} (hw : W₁ ≤ W₂) (ht : T₁ ≤ T₂) (c : Nat) :
    W₁ * (T₁ * 19 + 2) + 40 * T₁ + c ≤ W₂ * (T₂ * 19 + 2) + 40 * T₂ + c := by
  have hp := Nat.mul_le_mul hw (show T₁ * 19 + 2 ≤ T₂ * 19 + 2 by omega)
  omega
example {T₁ T₂ : Nat} (h : T₁ ≤ T₂) (c : Nat) :
    39 * T₁ + c ≤ 39 * T₂ + c ∧ 58 * T₁ + c ≤ 58 * T₂ + c ∧
      97 * T₁ + c ≤ 97 * T₂ + c := by omega

-- The public precheck retains each family's required-missing text and witness row.
example : ((derivedAssertionFailure? #[`w] #[`a, `b, `c]
    #[.derived (.binary "Categorizes" "a" "b") .everywhere]
    #[.derived (fun _ => "unused") .everywhere]
    (threeTypeTables #[.binary .inst 2 0 0])).getD #[])[1]? =
    some "Required but missing: `Categorizes(a, b)` requires each category-instance type to specialize `b`; missing `Sub(c, b)`." := by native_decide
example : ((derivedAssertionFailure? #[`w] #[`a, `b, `c]
    #[.derived (.binary "Categorizes" "a" "b") .everywhere]
    #[.derived (fun _ => "unused") .everywhere]
    (threeTypeTables #[.binary .inst 2 0 0])).getD #[])[5]? =
    some "  - Computed Categorizes: false, because `c` instantiates `a` at `w` but `Sub(c, b)` is missing." := by native_decide
example : ((derivedAssertionFailure? #[`w] #[`a, `b, `c]
    #[.derived (.binary "IsDisjointWith" "a" "b") .everywhere]
    #[.derived (fun _ => "unused") .everywhere]
    (threeTypeTables #[.binary .inst 2 0 0, .binary .inst 2 1 0])).getD #[])[1]? =
    some "Required but missing: `IsDisjointWith(a, b)` requires no shared instance; `c` instantiates both types." := by native_decide
example : ((derivedAssertionFailure? #[`w] #[`a, `b, `c]
    #[.derived (.binary "IsDisjointWith" "a" "b") .everywhere]
    #[.derived (fun _ => "unused") .everywhere]
    (threeTypeTables #[.binary .inst 2 0 0, .binary .inst 2 1 0])).getD #[])[5]? =
    some "  - Computed IsDisjointWith: false, because `c` instantiates both types at `w`." := by native_decide
example : ((derivedAssertionFailure? #[`w] #[`a, `b, `c]
    #[.derived (.ternary "IsCompletelyCoveredBy" "a" "b" "c") .everywhere]
    #[.derived (fun _ => "unused") .everywhere]
    (threeTypeTables #[.binary .inst 2 0 0])).getD #[])[1]? =
    some "Required but missing: `IsCompletelyCoveredBy(a, b, c)` requires every `a` instance to instantiate at least one covering type; `c` instantiates neither `b` nor `c`." := by native_decide
example : ((derivedAssertionFailure? #[`w] #[`a, `b, `c]
    #[.derived (.ternary "IsCompletelyCoveredBy" "a" "b" "c") .everywhere]
    #[.derived (fun _ => "unused") .everywhere]
    (threeTypeTables #[.binary .inst 2 0 0])).getD #[])[5]? =
    some "  - Computed IsCompletelyCoveredBy: false, because `c` instantiates `a` but instantiates neither covering type at `w`." := by native_decide
example : ((derivedAssertionFailure? #[`w] #[`a, `b, `c]
    #[.derived (.ternary "IsPartitionedInto" "a" "b" "c") .everywhere]
    #[.derived (fun _ => "unused") .everywhere]
    (threeTypeTables #[.binary .inst 0 0 0, .binary .inst 1 1 0, .binary .inst 1 2 0])).getD #[])[1]? =
    some "Required but missing: `IsPartitionedInto(a, b, c)` first requires complete coverage; `a` instantiates the partitioned type but neither part type." := by native_decide
example : ((derivedAssertionFailure? #[`w] #[`a, `b, `c]
    #[.derived (.ternary "IsPartitionedInto" "a" "b" "c") .everywhere]
    #[.derived (fun _ => "unused") .everywhere]
    (threeTypeTables #[.binary .inst 0 0 0, .binary .inst 1 1 0, .binary .inst 1 2 0])).getD #[])[5]? =
    some "  - Computed IsPartitionedInto: false, because coverage fails: `a` instantiates `a` but instantiates neither covering type at `w`." := by native_decide


-- Four coordinates keep the source, source type, target, and target type
-- distinct. Report checks preserve failure priority and literal output.
private def functionalReportTables (facts : Array CompiledFact) : FactTables :=
  compileExplicitModelAST { worldCount := 1, thingCount := 4, facts }

-- empty.
example : genericFunctionalDependenceRequiredMissingCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[]) 1 3 0 "fallback" =
    ⟨"fallback", 93⟩ := by native_decide

-- firstFunctionFailure.
example : genericFunctionalDependenceRequiredMissingCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 0 1 0, .binary .functionsAs 0 1 0]) 1 3 0 "fallback" =
    ⟨"`GenericFunctionalDependence(A, B)` requires a distinct target-functioning witness for source-functioning `a`; missing such a `B` instance.", 136⟩ := by native_decide

-- lastFunctionFailure.
example : genericFunctionalDependenceRequiredMissingCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 3 1 0, .binary .functionsAs 3 1 0]) 1 3 0 "fallback" =
    ⟨"`GenericFunctionalDependence(A, B)` requires a distinct target-functioning witness for source-functioning `B`; missing such a `B` instance.", 202⟩ := by native_decide

-- sourceNotFunctioning.
example : genericFunctionalDependenceRequiredMissingCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 0 1 0]) 1 3 0 "fallback" =
    ⟨"fallback", 110⟩ := by native_decide

-- selfFunctionTarget.
example : genericFunctionalDependenceRequiredMissingCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 0 1 0, .binary .functionsAs 0 1 0, .binary .inst 0 3 0, .binary .functionsAs 0 3 0]) 1 3 0 "fallback" =
    ⟨"`GenericFunctionalDependence(A, B)` requires a distinct target-functioning witness for source-functioning `a`; missing such a `B` instance.", 136⟩ := by native_decide

-- firstFunctionTarget.
example : genericFunctionalDependenceRequiredMissingCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 0 1 0, .binary .functionsAs 0 1 0, .binary .inst 1 3 0, .binary .functionsAs 1 3 0]) 1 3 0 "fallback" =
    ⟨"fallback", 155⟩ := by native_decide

-- lastFunctionTarget.
example : genericFunctionalDependenceRequiredMissingCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 0 1 0, .binary .functionsAs 0 1 0, .binary .inst 3 3 0, .binary .functionsAs 3 3 0]) 1 3 0 "fallback" =
    ⟨"fallback", 199⟩ := by native_decide

-- empty.
example : individualFunctionalDependenceRequiredMissingCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[]) 0 1 2 3 0 =
    ⟨"`IndividualFunctionalDependence(a, A, b, B)` requires `a :: A`; missing that instantiation.", 137⟩ := by native_decide

-- priorityFailure.
example : individualFunctionalDependenceRequiredMissingCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 3 1 0, .binary .functionsAs 3 1 0]) 0 1 2 3 0 =
    ⟨"`IndividualFunctionalDependence(a, A, b, B)` requires `GenericFunctionalDependence(A, B)`; that computed type-level dependence is false.", 205⟩ := by native_decide

-- sourceNotFunctioning.
example : individualFunctionalDependenceRequiredMissingCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 0 1 0]) 0 1 2 3 0 =
    ⟨"`IndividualFunctionalDependence(a, A, b, B)` requires `b :: B`; missing that instantiation.", 173⟩ := by native_decide

-- bothInstances.
example : individualFunctionalDependenceRequiredMissingCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 0 1 0, .binary .inst 2 3 0]) 0 1 2 3 0 =
    ⟨"`IndividualFunctionalDependence(a, A, b, B)` requires `b` to function as `B` whenever `a` functions as `A`; missing the target `FunctionsAs` fact.", 177⟩ := by native_decide

-- individualFunctionFailure.
example : individualFunctionalDependenceRequiredMissingCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 0 1 0, .binary .functionsAs 0 1 0, .binary .inst 1 3 0, .binary .functionsAs 1 3 0, .binary .inst 2 3 0]) 0 1 2 3 0 =
    ⟨"`IndividualFunctionalDependence(a, A, b, B)` requires `b` to function as `B` whenever `a` functions as `A`; missing the target `FunctionsAs` fact.", 220⟩ := by native_decide

-- empty.
example : componentOfRequiredMissingCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[]) 0 1 2 3 0 =
    ⟨"`ComponentOf(a, A, b, B)` requires `ProperPart(a, b)`; missing that proper-part fact.", 47⟩ := by native_decide

-- emptyWithPart.
example : componentOfRequiredMissingCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .properPart 0 2 0]) 0 1 2 3 0 =
    ⟨"`ComponentOf(a, A, b, B)` also requires computed `IndividualFunctionalDependence`; that dependence is false.", 43⟩ := by native_decide

-- priorityFailure.
example : componentOfRequiredMissingCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 3 1 0, .binary .functionsAs 3 1 0]) 0 1 2 3 0 =
    ⟨"`ComponentOf(a, A, b, B)` requires `ProperPart(a, b)`; missing that proper-part fact.", 47⟩ := by native_decide

-- priorityFailureWithPart.
example : componentOfRequiredMissingCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 3 1 0, .binary .functionsAs 3 1 0, .binary .properPart 0 2 0]) 0 1 2 3 0 =
    ⟨"`ComponentOf(a, A, b, B)` also requires computed `IndividualFunctionalDependence`; that dependence is false.", 43⟩ := by native_decide

-- sourceNotFunctioning.
example : componentOfRequiredMissingCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 0 1 0]) 0 1 2 3 0 =
    ⟨"`ComponentOf(a, A, b, B)` requires `ProperPart(a, b)`; missing that proper-part fact.", 47⟩ := by native_decide

-- sourceNotFunctioningWithPart.
example : componentOfRequiredMissingCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 0 1 0, .binary .properPart 0 2 0]) 0 1 2 3 0 =
    ⟨"`ComponentOf(a, A, b, B)` also requires computed `IndividualFunctionalDependence`; that dependence is false.", 43⟩ := by native_decide

-- bothInstances.
example : componentOfRequiredMissingCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 0 1 0, .binary .inst 2 3 0]) 0 1 2 3 0 =
    ⟨"`ComponentOf(a, A, b, B)` requires `ProperPart(a, b)`; missing that proper-part fact.", 47⟩ := by native_decide

-- bothInstancesWithPart.
example : componentOfRequiredMissingCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 0 1 0, .binary .inst 2 3 0, .binary .properPart 0 2 0]) 0 1 2 3 0 =
    ⟨"`ComponentOf(a, A, b, B)` also requires computed `IndividualFunctionalDependence`; that dependence is false.", 43⟩ := by native_decide

-- individualFunctionFailure.
example : componentOfRequiredMissingCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 0 1 0, .binary .functionsAs 0 1 0, .binary .inst 1 3 0, .binary .functionsAs 1 3 0, .binary .inst 2 3 0]) 0 1 2 3 0 =
    ⟨"`ComponentOf(a, A, b, B)` requires `ProperPart(a, b)`; missing that proper-part fact.", 47⟩ := by native_decide

-- individualFunctionFailureWithPart.
example : componentOfRequiredMissingCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 0 1 0, .binary .functionsAs 0 1 0, .binary .inst 1 3 0, .binary .functionsAs 1 3 0, .binary .inst 2 3 0, .binary .properPart 0 2 0]) 0 1 2 3 0 =
    ⟨"`ComponentOf(a, A, b, B)` also requires computed `IndividualFunctionalDependence`; that dependence is false.", 43⟩ := by native_decide

-- empty.
example : genericConstitutionalDependenceRequiredMissingCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[]) 1 3 0 "fallback" =
    ⟨"fallback", 89⟩ := by native_decide

-- firstConstitutionFailure.
example : genericConstitutionalDependenceRequiredMissingCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 0 1 0]) 1 3 0 "fallback" =
    ⟨"`GenericConstitutionalDependence(A, B)` requires a `B` instance that constitutionally bears source instance `a`; missing such a `ConstitutedBy(a, _)` witness.", 129⟩ := by native_decide

-- lastConstitutionFailure.
example : genericConstitutionalDependenceRequiredMissingCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 3 1 0]) 1 3 0 "fallback" =
    ⟨"`GenericConstitutionalDependence(A, B)` requires a `B` instance that constitutionally bears source instance `B`; missing such a `ConstitutedBy(B, _)` witness.", 192⟩ := by native_decide

-- reverseConstitution.
example : genericConstitutionalDependenceRequiredMissingCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 0 1 0, .binary .inst 2 3 0, .binary .constitutedBy 2 0 0]) 1 3 0 "fallback" =
    ⟨"`GenericConstitutionalDependence(A, B)` requires a `B` instance that constitutionally bears source instance `a`; missing such a `ConstitutedBy(a, _)` witness.", 146⟩ := by native_decide

-- selfConstitution.
example : genericConstitutionalDependenceRequiredMissingCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 0 1 0, .binary .inst 0 3 0, .binary .constitutedBy 0 0 0]) 1 3 0 "fallback" =
    ⟨"fallback", 127⟩ := by native_decide

-- firstConstitutionTarget.
example : genericConstitutionalDependenceRequiredMissingCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 0 1 0, .binary .inst 1 3 0, .binary .constitutedBy 0 1 0]) 1 3 0 "fallback" =
    ⟨"fallback", 147⟩ := by native_decide

-- lastConstitutionTarget.
example : genericConstitutionalDependenceRequiredMissingCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 0 1 0, .binary .inst 3 3 0, .binary .constitutedBy 0 3 0]) 1 3 0 "fallback" =
    ⟨"fallback", 187⟩ := by native_decide

-- empty.
example : constitutionRequiredMissingCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[]) 0 1 2 3 0 =
    ⟨"`Constitution(a, A, b, B)` requires `a :: A`; missing that instantiation.", 47⟩ := by native_decide

-- priorityFailure.
example : constitutionRequiredMissingCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 3 1 0, .binary .functionsAs 3 1 0]) 0 1 2 3 0 =
    ⟨"`Constitution(a, A, b, B)` requires `a :: A`; missing that instantiation.", 47⟩ := by native_decide

-- sourceNotFunctioning.
example : constitutionRequiredMissingCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 0 1 0]) 0 1 2 3 0 =
    ⟨"`Constitution(a, A, b, B)` requires `b :: B`; missing that instantiation.", 66⟩ := by native_decide

-- bothInstances.
example : constitutionRequiredMissingCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 0 1 0, .binary .inst 2 3 0]) 0 1 2 3 0 =
    ⟨"`Constitution(a, A, b, B)` requires computed `GenericConstitutionalDependence(A, B)`; that dependence is false.", 186⟩ := by native_decide

-- reverseConstitution.
example : constitutionRequiredMissingCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 0 1 0, .binary .inst 2 3 0, .binary .constitutedBy 2 0 0]) 0 1 2 3 0 =
    ⟨"`Constitution(a, A, b, B)` requires computed `GenericConstitutionalDependence(A, B)`; that dependence is false.", 186⟩ := by native_decide

-- individualConstitutionFailure.
example : constitutionRequiredMissingCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 0 1 0, .binary .inst 1 3 0, .binary .constitutedBy 0 1 0, .binary .inst 2 3 0]) 0 1 2 3 0 =
    ⟨"`Constitution(a, A, b, B)` requires `ConstitutedBy(a, b)`; missing that fact.", 209⟩ := by native_decide

-- empty.
example : genericFunctionalDependenceEvidenceCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[]) 1 3 0 =
    ⟨#["  - User assertion: `GenericFunctionalDependence(A, B)`.",
      "  - Computed GenericFunctionalDependence: true; every current source-functioning instance has a distinct target-functioning witness."], 110⟩ := by native_decide

-- firstFunctionFailure.
example : genericFunctionalDependenceEvidenceCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 0 1 0, .binary .functionsAs 0 1 0]) 1 3 0 =
    ⟨#["  - User assertion: `GenericFunctionalDependence(A, B)`.",
      "  - Computed GenericFunctionalDependence: false, because `a` instantiates and functions as `A` at `w`, but there is no distinct thing that instantiates and functions as `B`."], 149⟩ := by native_decide

-- lastFunctionFailure.
example : genericFunctionalDependenceEvidenceCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 3 1 0, .binary .functionsAs 3 1 0]) 1 3 0 =
    ⟨#["  - User assertion: `GenericFunctionalDependence(A, B)`.",
      "  - Computed GenericFunctionalDependence: false, because `B` instantiates and functions as `A` at `w`, but there is no distinct thing that instantiates and functions as `B`."], 215⟩ := by native_decide

-- sourceNotFunctioning.
example : genericFunctionalDependenceEvidenceCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 0 1 0]) 1 3 0 =
    ⟨#["  - User assertion: `GenericFunctionalDependence(A, B)`.",
      "  - Computed GenericFunctionalDependence: true; every current source-functioning instance has a distinct target-functioning witness."], 127⟩ := by native_decide

-- selfFunctionTarget.
example : genericFunctionalDependenceEvidenceCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 0 1 0, .binary .functionsAs 0 1 0, .binary .inst 0 3 0, .binary .functionsAs 0 3 0]) 1 3 0 =
    ⟨#["  - User assertion: `GenericFunctionalDependence(A, B)`.",
      "  - Computed GenericFunctionalDependence: false, because `a` instantiates and functions as `A` at `w`, but there is no distinct thing that instantiates and functions as `B`."], 149⟩ := by native_decide

-- firstFunctionTarget.
example : genericFunctionalDependenceEvidenceCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 0 1 0, .binary .functionsAs 0 1 0, .binary .inst 1 3 0, .binary .functionsAs 1 3 0]) 1 3 0 =
    ⟨#["  - User assertion: `GenericFunctionalDependence(A, B)`.",
      "  - Computed GenericFunctionalDependence: true; every current source-functioning instance has a distinct target-functioning witness."], 172⟩ := by native_decide

-- lastFunctionTarget.
example : genericFunctionalDependenceEvidenceCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 0 1 0, .binary .functionsAs 0 1 0, .binary .inst 3 3 0, .binary .functionsAs 3 3 0]) 1 3 0 =
    ⟨#["  - User assertion: `GenericFunctionalDependence(A, B)`.",
      "  - Computed GenericFunctionalDependence: true; every current source-functioning instance has a distinct target-functioning witness."], 216⟩ := by native_decide

-- empty.
example : individualFunctionalDependenceEvidenceCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[]) 0 1 2 3 0 =
    ⟨#["  - User assertion: `IndividualFunctionalDependence(a, A, b, B)`.",
      "  - Computed IndividualFunctionalDependence: false, because `a :: A` is missing at `w`."], 148⟩ := by native_decide

-- priorityFailure.
example : individualFunctionalDependenceEvidenceCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 3 1 0, .binary .functionsAs 3 1 0]) 0 1 2 3 0 =
    ⟨#["  - User assertion: `IndividualFunctionalDependence(a, A, b, B)`.",
      "  - Computed IndividualFunctionalDependence: false, because type-level functional dependence fails for source witness `B`."], 394⟩ := by native_decide

-- sourceNotFunctioning.
example : individualFunctionalDependenceEvidenceCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 0 1 0]) 0 1 2 3 0 =
    ⟨#["  - User assertion: `IndividualFunctionalDependence(a, A, b, B)`.",
      "  - Computed IndividualFunctionalDependence: false, because `b :: B` is missing at `w`."], 184⟩ := by native_decide

-- bothInstances.
example : individualFunctionalDependenceEvidenceCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 0 1 0, .binary .inst 2 3 0]) 0 1 2 3 0 =
    ⟨#["  - User assertion: `IndividualFunctionalDependence(a, A, b, B)`.",
      "  - Computed IndividualFunctionalDependence: false, because `a` functions as `A` but `b` does not function as `B` at `w`."], 188⟩ := by native_decide

-- individualFunctionFailure.
example : individualFunctionalDependenceEvidenceCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 0 1 0, .binary .functionsAs 0 1 0, .binary .inst 1 3 0, .binary .functionsAs 1 3 0, .binary .inst 2 3 0]) 0 1 2 3 0 =
    ⟨#["  - User assertion: `IndividualFunctionalDependence(a, A, b, B)`.",
      "  - Computed IndividualFunctionalDependence: false, because `a` functions as `A` but `b` does not function as `B` at `w`."], 231⟩ := by native_decide

-- empty.
example : componentOfEvidenceCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[]) 0 1 2 3 0 =
    ⟨#["  - User assertion: `ComponentOf(a, A, b, B)`.",
      "  - Computed ComponentOf: false, because `ProperPart(a, b)` is missing at `w`."], 58⟩ := by native_decide

-- emptyWithPart.
example : componentOfEvidenceCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .properPart 0 2 0]) 0 1 2 3 0 =
    ⟨#["  - User assertion: `ComponentOf(a, A, b, B)`.",
      "  - Computed ComponentOf: false, because the required individual functional dependence is false: `a :: A` is missing."], 163⟩ := by native_decide

-- priorityFailure.
example : componentOfEvidenceCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 3 1 0, .binary .functionsAs 3 1 0]) 0 1 2 3 0 =
    ⟨#["  - User assertion: `ComponentOf(a, A, b, B)`.",
      "  - Computed ComponentOf: false, because `ProperPart(a, b)` is missing at `w`."], 58⟩ := by native_decide

-- priorityFailureWithPart.
example : componentOfEvidenceCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 3 1 0, .binary .functionsAs 3 1 0, .binary .properPart 0 2 0]) 0 1 2 3 0 =
    ⟨#["  - User assertion: `ComponentOf(a, A, b, B)`.",
      "  - Computed ComponentOf: false, because the required individual functional dependence is false: type-level functional dependence fails for source witness `B`."], 415⟩ := by native_decide

-- sourceNotFunctioning.
example : componentOfEvidenceCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 0 1 0]) 0 1 2 3 0 =
    ⟨#["  - User assertion: `ComponentOf(a, A, b, B)`.",
      "  - Computed ComponentOf: false, because `ProperPart(a, b)` is missing at `w`."], 58⟩ := by native_decide

-- sourceNotFunctioningWithPart.
example : componentOfEvidenceCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 0 1 0, .binary .properPart 0 2 0]) 0 1 2 3 0 =
    ⟨#["  - User assertion: `ComponentOf(a, A, b, B)`.",
      "  - Computed ComponentOf: false, because the required individual functional dependence is false: `b :: B` is missing."], 199⟩ := by native_decide

-- bothInstances.
example : componentOfEvidenceCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 0 1 0, .binary .inst 2 3 0]) 0 1 2 3 0 =
    ⟨#["  - User assertion: `ComponentOf(a, A, b, B)`.",
      "  - Computed ComponentOf: false, because `ProperPart(a, b)` is missing at `w`."], 58⟩ := by native_decide

-- bothInstancesWithPart.
example : componentOfEvidenceCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 0 1 0, .binary .inst 2 3 0, .binary .properPart 0 2 0]) 0 1 2 3 0 =
    ⟨#["  - User assertion: `ComponentOf(a, A, b, B)`.",
      "  - Computed ComponentOf: false, because the required individual functional dependence is false: `a` functions as `A` but `b` does not function as `B`."], 203⟩ := by native_decide

-- individualFunctionFailure.
example : componentOfEvidenceCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 0 1 0, .binary .functionsAs 0 1 0, .binary .inst 1 3 0, .binary .functionsAs 1 3 0, .binary .inst 2 3 0]) 0 1 2 3 0 =
    ⟨#["  - User assertion: `ComponentOf(a, A, b, B)`.",
      "  - Computed ComponentOf: false, because `ProperPart(a, b)` is missing at `w`."], 58⟩ := by native_decide

-- individualFunctionFailureWithPart.
example : componentOfEvidenceCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 0 1 0, .binary .functionsAs 0 1 0, .binary .inst 1 3 0, .binary .functionsAs 1 3 0, .binary .inst 2 3 0, .binary .properPart 0 2 0]) 0 1 2 3 0 =
    ⟨#["  - User assertion: `ComponentOf(a, A, b, B)`.",
      "  - Computed ComponentOf: false, because the required individual functional dependence is false: `a` functions as `A` but `b` does not function as `B`."], 246⟩ := by native_decide

-- empty.
example : genericConstitutionalDependenceEvidenceCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[]) 1 3 0 =
    ⟨#["  - User assertion: `GenericConstitutionalDependence(A, B)`.",
      "  - Computed GenericConstitutionalDependence: true; every current source instance has a constituting target instance."], 106⟩ := by native_decide

-- firstConstitutionFailure.
example : genericConstitutionalDependenceEvidenceCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 0 1 0]) 1 3 0 =
    ⟨#["  - User assertion: `GenericConstitutionalDependence(A, B)`.",
      "  - Computed GenericConstitutionalDependence: false, because `a` instantiates `A` at `w`, but no `B` instance is related by `ConstitutedBy(a, _)`."], 142⟩ := by native_decide

-- lastConstitutionFailure.
example : genericConstitutionalDependenceEvidenceCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 3 1 0]) 1 3 0 =
    ⟨#["  - User assertion: `GenericConstitutionalDependence(A, B)`.",
      "  - Computed GenericConstitutionalDependence: false, because `B` instantiates `A` at `w`, but no `B` instance is related by `ConstitutedBy(B, _)`."], 205⟩ := by native_decide

-- reverseConstitution.
example : genericConstitutionalDependenceEvidenceCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 0 1 0, .binary .inst 2 3 0, .binary .constitutedBy 2 0 0]) 1 3 0 =
    ⟨#["  - User assertion: `GenericConstitutionalDependence(A, B)`.",
      "  - Computed GenericConstitutionalDependence: false, because `a` instantiates `A` at `w`, but no `B` instance is related by `ConstitutedBy(a, _)`."], 159⟩ := by native_decide

-- selfConstitution.
example : genericConstitutionalDependenceEvidenceCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 0 1 0, .binary .inst 0 3 0, .binary .constitutedBy 0 0 0]) 1 3 0 =
    ⟨#["  - User assertion: `GenericConstitutionalDependence(A, B)`.",
      "  - Computed GenericConstitutionalDependence: true; every current source instance has a constituting target instance."], 144⟩ := by native_decide

-- firstConstitutionTarget.
example : genericConstitutionalDependenceEvidenceCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 0 1 0, .binary .inst 1 3 0, .binary .constitutedBy 0 1 0]) 1 3 0 =
    ⟨#["  - User assertion: `GenericConstitutionalDependence(A, B)`.",
      "  - Computed GenericConstitutionalDependence: true; every current source instance has a constituting target instance."], 164⟩ := by native_decide

-- lastConstitutionTarget.
example : genericConstitutionalDependenceEvidenceCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 0 1 0, .binary .inst 3 3 0, .binary .constitutedBy 0 3 0]) 1 3 0 =
    ⟨#["  - User assertion: `GenericConstitutionalDependence(A, B)`.",
      "  - Computed GenericConstitutionalDependence: true; every current source instance has a constituting target instance."], 204⟩ := by native_decide

-- empty.
example : constitutionEvidenceCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[]) 0 1 2 3 0 =
    ⟨#["  - User assertion: `Constitution(a, A, b, B)`.",
      "  - Computed Constitution: false, because `a :: A` is missing at `w`."], 58⟩ := by native_decide

-- priorityFailure.
example : constitutionEvidenceCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 3 1 0, .binary .functionsAs 3 1 0]) 0 1 2 3 0 =
    ⟨#["  - User assertion: `Constitution(a, A, b, B)`.",
      "  - Computed Constitution: false, because `a :: A` is missing at `w`."], 58⟩ := by native_decide

-- sourceNotFunctioning.
example : constitutionEvidenceCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 0 1 0]) 0 1 2 3 0 =
    ⟨#["  - User assertion: `Constitution(a, A, b, B)`.",
      "  - Computed Constitution: false, because `b :: B` is missing at `w`."], 77⟩ := by native_decide

-- bothInstances.
example : constitutionEvidenceCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 0 1 0, .binary .inst 2 3 0]) 0 1 2 3 0 =
    ⟨#["  - User assertion: `Constitution(a, A, b, B)`.",
      "  - Computed Constitution: false, because generic constitutional dependence fails for source witness `a`."], 317⟩ := by native_decide

-- reverseConstitution.
example : constitutionEvidenceCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 0 1 0, .binary .inst 2 3 0, .binary .constitutedBy 2 0 0]) 0 1 2 3 0 =
    ⟨#["  - User assertion: `Constitution(a, A, b, B)`.",
      "  - Computed Constitution: false, because generic constitutional dependence fails for source witness `a`."], 317⟩ := by native_decide

-- individualConstitutionFailure.
example : constitutionEvidenceCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 0 1 0, .binary .inst 1 3 0, .binary .constitutedBy 0 1 0, .binary .inst 2 3 0]) 0 1 2 3 0 =
    ⟨#["  - User assertion: `Constitution(a, A, b, B)`.",
      "  - Computed Constitution: false, because `ConstitutedBy(a, b)` is missing at `w`."], 220⟩ := by native_decide



-- Empty domains still produce names with the #n fallback spelling. No
-- generic search visits a coordinate; invalid primitive queries cost two.
example : genericFunctionalDependenceRequiredMissingCosted #[] #[]
    (compileExplicitModelAST { worldCount := 0, thingCount := 0, facts := #[] }) 1 3 0 "fallback" =
    ⟨"fallback", 1⟩ := by native_decide

example : individualFunctionalDependenceRequiredMissingCosted #[] #[]
    (compileExplicitModelAST { worldCount := 0, thingCount := 0, facts := #[] }) 0 1 2 3 0 =
    ⟨"`IndividualFunctionalDependence(#0, #1, #2, #3)` requires `#0 :: #1`; missing that instantiation.", 34⟩ := by native_decide

example : componentOfRequiredMissingCosted #[] #[]
    (compileExplicitModelAST { worldCount := 0, thingCount := 0, facts := #[] }) 0 1 2 3 0 =
    ⟨"`ComponentOf(#0, #1, #2, #3)` requires `ProperPart(#0, #2)`; missing that proper-part fact.", 32⟩ := by native_decide

example : genericConstitutionalDependenceRequiredMissingCosted #[] #[]
    (compileExplicitModelAST { worldCount := 0, thingCount := 0, facts := #[] }) 1 3 0 "fallback" =
    ⟨"fallback", 1⟩ := by native_decide

example : constitutionRequiredMissingCosted #[] #[]
    (compileExplicitModelAST { worldCount := 0, thingCount := 0, facts := #[] }) 0 1 2 3 0 =
    ⟨"`Constitution(#0, #1, #2, #3)` requires `#0 :: #1`; missing that instantiation.", 32⟩ := by native_decide

example : genericFunctionalDependenceEvidenceCosted #[] #[]
    (compileExplicitModelAST { worldCount := 0, thingCount := 0, facts := #[] }) 1 3 0 =
    ⟨#["  - User assertion: `GenericFunctionalDependence(#1, #3)`.",
      "  - Computed GenericFunctionalDependence: true; every current source-functioning instance has a distinct target-functioning witness."], 18⟩ := by native_decide

example : individualFunctionalDependenceEvidenceCosted #[] #[]
    (compileExplicitModelAST { worldCount := 0, thingCount := 0, facts := #[] }) 0 1 2 3 0 =
    ⟨#["  - User assertion: `IndividualFunctionalDependence(#0, #1, #2, #3)`.",
      "  - Computed IndividualFunctionalDependence: false, because `#0 :: #1` is missing at `#0`."], 45⟩ := by native_decide

example : componentOfEvidenceCosted #[] #[]
    (compileExplicitModelAST { worldCount := 0, thingCount := 0, facts := #[] }) 0 1 2 3 0 =
    ⟨#["  - User assertion: `ComponentOf(#0, #1, #2, #3)`.",
      "  - Computed ComponentOf: false, because `ProperPart(#0, #2)` is missing at `#0`."], 43⟩ := by native_decide

example : genericConstitutionalDependenceEvidenceCosted #[] #[]
    (compileExplicitModelAST { worldCount := 0, thingCount := 0, facts := #[] }) 1 3 0 =
    ⟨#["  - User assertion: `GenericConstitutionalDependence(#1, #3)`.",
      "  - Computed GenericConstitutionalDependence: true; every current source instance has a constituting target instance."], 18⟩ := by native_decide

example : constitutionEvidenceCosted #[] #[]
    (compileExplicitModelAST { worldCount := 0, thingCount := 0, facts := #[] }) 0 1 2 3 0 =
    ⟨#["  - User assertion: `Constitution(#0, #1, #2, #3)`.",
      "  - Computed Constitution: false, because `#0 :: #1` is missing at `#0`."], 43⟩ := by native_decide

-- Repeated facts and fact-array order do not change indexed queries,
-- selected witnesses, or charges. The source is retained before later failures.
example : genericFunctionalDependenceRequiredMissingCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 0 1 0, .binary .functionsAs 0 1 0]) 1 3 0 "fallback" =
    genericFunctionalDependenceRequiredMissingCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .functionsAs 0 1 0, .binary .inst 0 1 0, .binary .inst 0 1 0, .binary .functionsAs 0 1 0]) 1 3 0 "fallback" := by native_decide

example : individualFunctionalDependenceRequiredMissingCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 3 1 0, .binary .functionsAs 3 1 0]) 0 1 2 3 0 =
    individualFunctionalDependenceRequiredMissingCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .functionsAs 3 1 0, .binary .inst 3 1 0, .binary .inst 3 1 0, .binary .functionsAs 3 1 0]) 0 1 2 3 0 := by native_decide

example : componentOfRequiredMissingCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 3 1 0, .binary .functionsAs 3 1 0]) 0 1 2 3 0 =
    componentOfRequiredMissingCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .functionsAs 3 1 0, .binary .inst 3 1 0, .binary .inst 3 1 0, .binary .functionsAs 3 1 0]) 0 1 2 3 0 := by native_decide

example : genericConstitutionalDependenceRequiredMissingCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 0 1 0]) 1 3 0 "fallback" =
    genericConstitutionalDependenceRequiredMissingCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 0 1 0, .binary .inst 0 1 0]) 1 3 0 "fallback" := by native_decide

example : constitutionRequiredMissingCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 3 1 0, .binary .functionsAs 3 1 0]) 0 1 2 3 0 =
    constitutionRequiredMissingCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .functionsAs 3 1 0, .binary .inst 3 1 0, .binary .inst 3 1 0, .binary .functionsAs 3 1 0]) 0 1 2 3 0 := by native_decide

example : genericFunctionalDependenceEvidenceCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 0 1 0, .binary .functionsAs 0 1 0]) 1 3 0 =
    genericFunctionalDependenceEvidenceCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .functionsAs 0 1 0, .binary .inst 0 1 0, .binary .inst 0 1 0, .binary .functionsAs 0 1 0]) 1 3 0 := by native_decide

example : individualFunctionalDependenceEvidenceCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 3 1 0, .binary .functionsAs 3 1 0]) 0 1 2 3 0 =
    individualFunctionalDependenceEvidenceCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .functionsAs 3 1 0, .binary .inst 3 1 0, .binary .inst 3 1 0, .binary .functionsAs 3 1 0]) 0 1 2 3 0 := by native_decide

example : componentOfEvidenceCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 3 1 0, .binary .functionsAs 3 1 0]) 0 1 2 3 0 =
    componentOfEvidenceCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .functionsAs 3 1 0, .binary .inst 3 1 0, .binary .inst 3 1 0, .binary .functionsAs 3 1 0]) 0 1 2 3 0 := by native_decide

example : genericConstitutionalDependenceEvidenceCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 0 1 0]) 1 3 0 =
    genericConstitutionalDependenceEvidenceCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 0 1 0, .binary .inst 0 1 0]) 1 3 0 := by native_decide

example : constitutionEvidenceCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 3 1 0, .binary .functionsAs 3 1 0]) 0 1 2 3 0 =
    constitutionEvidenceCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .functionsAs 3 1 0, .binary .inst 3 1 0, .binary .inst 3 1 0, .binary .functionsAs 3 1 0]) 0 1 2 3 0 := by native_decide

-- Reversed instantiation and unrelated relation fields cannot create
-- a functioning or constituting source, or satisfy proper parthood.
example : genericFunctionalDependenceRequiredMissingCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 1 0 0, .binary .functionsAs 1 0 0,
      .binary .properPart 2 0 0, .binary .memberOf 0 1 0]) 1 3 0 "fallback" =
    genericFunctionalDependenceRequiredMissingCosted #[`w] #[`a, `A, `b, `B] (functionalReportTables #[]) 1 3 0 "fallback" := by native_decide

example : individualFunctionalDependenceRequiredMissingCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 1 0 0, .binary .functionsAs 1 0 0,
      .binary .properPart 2 0 0, .binary .memberOf 0 1 0]) 0 1 2 3 0 =
    individualFunctionalDependenceRequiredMissingCosted #[`w] #[`a, `A, `b, `B] (functionalReportTables #[]) 0 1 2 3 0 := by native_decide

example : componentOfRequiredMissingCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 1 0 0, .binary .functionsAs 1 0 0,
      .binary .properPart 2 0 0, .binary .memberOf 0 1 0]) 0 1 2 3 0 =
    componentOfRequiredMissingCosted #[`w] #[`a, `A, `b, `B] (functionalReportTables #[]) 0 1 2 3 0 := by native_decide

example : genericConstitutionalDependenceRequiredMissingCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 1 0 0, .binary .functionsAs 1 0 0,
      .binary .properPart 2 0 0, .binary .memberOf 0 1 0]) 1 3 0 "fallback" =
    genericConstitutionalDependenceRequiredMissingCosted #[`w] #[`a, `A, `b, `B] (functionalReportTables #[]) 1 3 0 "fallback" := by native_decide

example : constitutionRequiredMissingCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 1 0 0, .binary .functionsAs 1 0 0,
      .binary .properPart 2 0 0, .binary .memberOf 0 1 0]) 0 1 2 3 0 =
    constitutionRequiredMissingCosted #[`w] #[`a, `A, `b, `B] (functionalReportTables #[]) 0 1 2 3 0 := by native_decide

example : genericFunctionalDependenceEvidenceCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 1 0 0, .binary .functionsAs 1 0 0,
      .binary .properPart 2 0 0, .binary .memberOf 0 1 0]) 1 3 0 =
    genericFunctionalDependenceEvidenceCosted #[`w] #[`a, `A, `b, `B] (functionalReportTables #[]) 1 3 0 := by native_decide

example : individualFunctionalDependenceEvidenceCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 1 0 0, .binary .functionsAs 1 0 0,
      .binary .properPart 2 0 0, .binary .memberOf 0 1 0]) 0 1 2 3 0 =
    individualFunctionalDependenceEvidenceCosted #[`w] #[`a, `A, `b, `B] (functionalReportTables #[]) 0 1 2 3 0 := by native_decide

example : componentOfEvidenceCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 1 0 0, .binary .functionsAs 1 0 0,
      .binary .properPart 2 0 0, .binary .memberOf 0 1 0]) 0 1 2 3 0 =
    componentOfEvidenceCosted #[`w] #[`a, `A, `b, `B] (functionalReportTables #[]) 0 1 2 3 0 := by native_decide

example : genericConstitutionalDependenceEvidenceCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 1 0 0, .binary .functionsAs 1 0 0,
      .binary .properPart 2 0 0, .binary .memberOf 0 1 0]) 1 3 0 =
    genericConstitutionalDependenceEvidenceCosted #[`w] #[`a, `A, `b, `B] (functionalReportTables #[]) 1 3 0 := by native_decide

example : constitutionEvidenceCosted #[`w] #[`a, `A, `b, `B]
    (functionalReportTables #[.binary .inst 1 0 0, .binary .functionsAs 1 0 0,
      .binary .properPart 2 0 0, .binary .memberOf 0 1 0]) 0 1 2 3 0 =
    constitutionEvidenceCosted #[`w] #[`a, `A, `b, `B] (functionalReportTables #[]) 0 1 2 3 0 := by native_decide

-- General bounds and row sizes apply to arbitrary tables and natural
-- coordinates. Sparse-table value correspondence separately requires valid
-- finite coordinates and agreement with the dense tables.
example (worlds things : Array Name) (tables : FactTables) (x y w : Nat) (fallback : String) :
    (genericFunctionalDependenceRequiredMissingCosted worlds things tables x y w fallback).cost ≤ things.size * (39 * things.size + 41) + 21 :=
  genericFunctionalDependenceRequiredMissingCosted_cost_le worlds things tables x y w fallback

example (worlds things : Array Name) (tables : FactTables) (x xType y yType w : Nat) :
    (individualFunctionalDependenceRequiredMissingCosted worlds things tables x xType y yType w).cost ≤ things.size * (39 * things.size + 39) + 72 :=
  individualFunctionalDependenceRequiredMissingCosted_cost_le worlds things tables x xType y yType w

example (worlds things : Array Name) (tables : FactTables) (x xType y yType w : Nat) :
    (componentOfRequiredMissingCosted worlds things tables x xType y yType w).cost ≤ 47 :=
  componentOfRequiredMissingCosted_cost_le worlds things tables x xType y yType w

example (worlds things : Array Name) (tables : FactTables) (x y w : Nat) (fallback : String) :
    (genericConstitutionalDependenceRequiredMissingCosted worlds things tables x y w fallback).cost ≤ things.size * (37 * things.size + 23) + 23 :=
  genericConstitutionalDependenceRequiredMissingCosted_cost_le worlds things tables x y w fallback

example (worlds things : Array Name) (tables : FactTables) (x xType y yType w : Nat) :
    (constitutionRequiredMissingCosted worlds things tables x xType y yType w).cost ≤ things.size * (37 * things.size + 21) + 68 :=
  constitutionRequiredMissingCosted_cost_le worlds things tables x xType y yType w

example (worlds things : Array Name) (tables : FactTables) (x y w : Nat) :
    (genericFunctionalDependenceEvidenceCosted worlds things tables x y w).cost ≤ things.size * (39 * things.size + 41) + 34 :=
  genericFunctionalDependenceEvidenceCosted_cost_le worlds things tables x y w

example (worlds things : Array Name) (tables : FactTables) (x y w : Nat) :
    (genericFunctionalDependenceEvidenceCosted worlds things tables x y w).value.size = 2 :=
  genericFunctionalDependenceEvidenceCosted_size worlds things tables x y w

example (worlds things : Array Name) (tables : FactTables) (x xType y yType w : Nat) :
    (individualFunctionalDependenceEvidenceCosted worlds things tables x xType y yType w).cost ≤ things.size * (39 * things.size + 39) + things.size * (39 * things.size + 41) + 83 :=
  individualFunctionalDependenceEvidenceCosted_cost_le worlds things tables x xType y yType w

example (worlds things : Array Name) (tables : FactTables) (x xType y yType w : Nat) :
    (individualFunctionalDependenceEvidenceCosted worlds things tables x xType y yType w).value.size = 2 :=
  individualFunctionalDependenceEvidenceCosted_size worlds things tables x xType y yType w

example (worlds things : Array Name) (tables : FactTables) (x xType y yType w : Nat) :
    (componentOfEvidenceCosted worlds things tables x xType y yType w).cost ≤ things.size * (39 * things.size + 39) + things.size * (39 * things.size + 41) + 98 :=
  componentOfEvidenceCosted_cost_le worlds things tables x xType y yType w

example (worlds things : Array Name) (tables : FactTables) (x xType y yType w : Nat) :
    (componentOfEvidenceCosted worlds things tables x xType y yType w).value.size = 2 :=
  componentOfEvidenceCosted_size worlds things tables x xType y yType w

example (worlds things : Array Name) (tables : FactTables) (x y w : Nat) :
    (genericConstitutionalDependenceEvidenceCosted worlds things tables x y w).cost ≤ things.size * (37 * things.size + 23) + 36 :=
  genericConstitutionalDependenceEvidenceCosted_cost_le worlds things tables x y w

example (worlds things : Array Name) (tables : FactTables) (x y w : Nat) :
    (genericConstitutionalDependenceEvidenceCosted worlds things tables x y w).value.size = 2 :=
  genericConstitutionalDependenceEvidenceCosted_size worlds things tables x y w

example (worlds things : Array Name) (tables : FactTables) (x xType y yType w : Nat) :
    (constitutionEvidenceCosted worlds things tables x xType y yType w).cost ≤ things.size * (37 * things.size + 21) + things.size * (37 * things.size + 23) + 79 :=
  constitutionEvidenceCosted_cost_le worlds things tables x xType y yType w

example (worlds things : Array Name) (tables : FactTables) (x xType y yType w : Nat) :
    (constitutionEvidenceCosted worlds things tables x xType y yType w).value.size = 2 :=
  constitutionEvidenceCosted_size worlds things tables x xType y yType w

-- Increasing the size parameter cannot lower an upper bound, although
-- an exact execution count can fall when an earlier witness becomes available.
example {T₁ T₂ : Nat} (h : T₁ ≤ T₂) :
    T₁ * (39 * T₁ + 41) + 21 ≤ T₂ * (39 * T₂ + 41) + 21 := by
  have h0 := Nat.mul_le_mul h (show 39 * T₁ + 41 ≤ 39 * T₂ + 41 by omega)
  omega

example {T₁ T₂ : Nat} (h : T₁ ≤ T₂) :
    T₁ * (39 * T₁ + 39) + 72 ≤ T₂ * (39 * T₂ + 39) + 72 := by
  have h0 := Nat.mul_le_mul h (show 39 * T₁ + 39 ≤ 39 * T₂ + 39 by omega)
  omega

example {T₁ T₂ : Nat} (h : T₁ ≤ T₂) :
    T₁ * (37 * T₁ + 23) + 23 ≤ T₂ * (37 * T₂ + 23) + 23 := by
  have h0 := Nat.mul_le_mul h (show 37 * T₁ + 23 ≤ 37 * T₂ + 23 by omega)
  omega

example {T₁ T₂ : Nat} (h : T₁ ≤ T₂) :
    T₁ * (37 * T₁ + 21) + 68 ≤ T₂ * (37 * T₂ + 21) + 68 := by
  have h0 := Nat.mul_le_mul h (show 37 * T₁ + 21 ≤ 37 * T₂ + 21 by omega)
  omega

example {T₁ T₂ : Nat} (h : T₁ ≤ T₂) :
    T₁ * (39 * T₁ + 41) + 34 ≤ T₂ * (39 * T₂ + 41) + 34 := by
  have h0 := Nat.mul_le_mul h (show 39 * T₁ + 41 ≤ 39 * T₂ + 41 by omega)
  omega

example {T₁ T₂ : Nat} (h : T₁ ≤ T₂) :
    T₁ * (39 * T₁ + 39) + T₁ * (39 * T₁ + 41) + 83 ≤ T₂ * (39 * T₂ + 39) + T₂ * (39 * T₂ + 41) + 83 := by
  have h0 := Nat.mul_le_mul h (show 39 * T₁ + 39 ≤ 39 * T₂ + 39 by omega)
  have h1 := Nat.mul_le_mul h (show 39 * T₁ + 41 ≤ 39 * T₂ + 41 by omega)
  omega

example {T₁ T₂ : Nat} (h : T₁ ≤ T₂) :
    T₁ * (39 * T₁ + 39) + T₁ * (39 * T₁ + 41) + 98 ≤ T₂ * (39 * T₂ + 39) + T₂ * (39 * T₂ + 41) + 98 := by
  have h0 := Nat.mul_le_mul h (show 39 * T₁ + 39 ≤ 39 * T₂ + 39 by omega)
  have h1 := Nat.mul_le_mul h (show 39 * T₁ + 41 ≤ 39 * T₂ + 41 by omega)
  omega

example {T₁ T₂ : Nat} (h : T₁ ≤ T₂) :
    T₁ * (37 * T₁ + 23) + 36 ≤ T₂ * (37 * T₂ + 23) + 36 := by
  have h0 := Nat.mul_le_mul h (show 37 * T₁ + 23 ≤ 37 * T₂ + 23 by omega)
  omega

example {T₁ T₂ : Nat} (h : T₁ ≤ T₂) :
    T₁ * (37 * T₁ + 21) + T₁ * (37 * T₁ + 23) + 79 ≤ T₂ * (37 * T₂ + 21) + T₂ * (37 * T₂ + 23) + 79 := by
  have h0 := Nat.mul_le_mul h (show 37 * T₁ + 21 ≤ 37 * T₂ + 21 by omega)
  have h1 := Nat.mul_le_mul h (show 37 * T₁ + 23 ≤ 37 * T₂ + 23 by omega)
  omega

-- The public renderer places required-missing text at row 1 and the
-- family explanation at row 5, after the assertion row. Each fixture fails
-- its actual derived assertion, not just a formatter called in isolation.
example : ((derivedAssertionFailure? #[`w] #[`a, `A, `b, `B]
    #[.derived (.binary "GenericFunctionalDependence" "A" "B") .everywhere]
    #[.derived (fun _ => "unused") .everywhere]
    (functionalReportTables #[.binary .inst 0 1 0, .binary .functionsAs 0 1 0])).getD #[])[1]? =
    some "Required but missing: `GenericFunctionalDependence(A, B)` requires a distinct target-functioning witness for source-functioning `a`; missing such a `B` instance." := by native_decide

example : ((derivedAssertionFailure? #[`w] #[`a, `A, `b, `B]
    #[.derived (.binary "GenericFunctionalDependence" "A" "B") .everywhere]
    #[.derived (fun _ => "unused") .everywhere]
    (functionalReportTables #[.binary .inst 0 1 0, .binary .functionsAs 0 1 0])).getD #[])[5]? =
    some "  - Computed GenericFunctionalDependence: false, because `a` instantiates and functions as `A` at `w`, but there is no distinct thing that instantiates and functions as `B`." := by native_decide

example : ((derivedAssertionFailure? #[`w] #[`a, `A, `b, `B]
    #[.derived (.quaternary "IndividualFunctionalDependence" "a" "A" "b" "B") .everywhere]
    #[.derived (fun _ => "unused") .everywhere]
    (functionalReportTables #[.binary .inst 0 1 0, .binary .functionsAs 0 1 0, .binary .inst 1 3 0, .binary .functionsAs 1 3 0, .binary .inst 2 3 0])).getD #[])[1]? =
    some "Required but missing: `IndividualFunctionalDependence(a, A, b, B)` requires `b` to function as `B` whenever `a` functions as `A`; missing the target `FunctionsAs` fact." := by native_decide

example : ((derivedAssertionFailure? #[`w] #[`a, `A, `b, `B]
    #[.derived (.quaternary "IndividualFunctionalDependence" "a" "A" "b" "B") .everywhere]
    #[.derived (fun _ => "unused") .everywhere]
    (functionalReportTables #[.binary .inst 0 1 0, .binary .functionsAs 0 1 0, .binary .inst 1 3 0, .binary .functionsAs 1 3 0, .binary .inst 2 3 0])).getD #[])[5]? =
    some "  - Computed IndividualFunctionalDependence: false, because `a` functions as `A` but `b` does not function as `B` at `w`." := by native_decide

example : ((derivedAssertionFailure? #[`w] #[`a, `A, `b, `B]
    #[.derived (.quaternary "ComponentOf" "a" "A" "b" "B") .everywhere]
    #[.derived (fun _ => "unused") .everywhere]
    (functionalReportTables #[])).getD #[])[1]? =
    some "Required but missing: `ComponentOf(a, A, b, B)` requires `ProperPart(a, b)`; missing that proper-part fact." := by native_decide

example : ((derivedAssertionFailure? #[`w] #[`a, `A, `b, `B]
    #[.derived (.quaternary "ComponentOf" "a" "A" "b" "B") .everywhere]
    #[.derived (fun _ => "unused") .everywhere]
    (functionalReportTables #[])).getD #[])[5]? =
    some "  - Computed ComponentOf: false, because `ProperPart(a, b)` is missing at `w`." := by native_decide

example : ((derivedAssertionFailure? #[`w] #[`a, `A, `b, `B]
    #[.derived (.binary "GenericConstitutionalDependence" "A" "B") .everywhere]
    #[.derived (fun _ => "unused") .everywhere]
    (functionalReportTables #[.binary .inst 0 1 0])).getD #[])[1]? =
    some "Required but missing: `GenericConstitutionalDependence(A, B)` requires a `B` instance that constitutionally bears source instance `a`; missing such a `ConstitutedBy(a, _)` witness." := by native_decide

example : ((derivedAssertionFailure? #[`w] #[`a, `A, `b, `B]
    #[.derived (.binary "GenericConstitutionalDependence" "A" "B") .everywhere]
    #[.derived (fun _ => "unused") .everywhere]
    (functionalReportTables #[.binary .inst 0 1 0])).getD #[])[5]? =
    some "  - Computed GenericConstitutionalDependence: false, because `a` instantiates `A` at `w`, but no `B` instance is related by `ConstitutedBy(a, _)`." := by native_decide

example : ((derivedAssertionFailure? #[`w] #[`a, `A, `b, `B]
    #[.derived (.quaternary "Constitution" "a" "A" "b" "B") .everywhere]
    #[.derived (fun _ => "unused") .everywhere]
    (functionalReportTables #[.binary .inst 0 1 0, .binary .inst 1 3 0, .binary .constitutedBy 0 1 0, .binary .inst 2 3 0])).getD #[])[1]? =
    some "Required but missing: `Constitution(a, A, b, B)` requires `ConstitutedBy(a, b)`; missing that fact." := by native_decide

example : ((derivedAssertionFailure? #[`w] #[`a, `A, `b, `B]
    #[.derived (.quaternary "Constitution" "a" "A" "b" "B") .everywhere]
    #[.derived (fun _ => "unused") .everywhere]
    (functionalReportTables #[.binary .inst 0 1 0, .binary .inst 1 3 0, .binary .constitutedBy 0 1 0, .binary .inst 2 3 0])).getD #[])[5]? =
    some "  - Computed Constitution: false, because `ConstitutedBy(a, b)` is missing at `w`." := by native_decide


end LeanUfo.Test.Complexity.DerivedAssertions
