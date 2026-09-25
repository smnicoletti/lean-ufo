import LeanUfo.UFO.DSL.Diagnostic.Analysis
import LeanUfo.UFO.DSL.Checker.Axioms
import Batteries.Tactic.OpenPrivate

/-!
# Diagnostic execution regressions

These tests cover relation queries, derived predicates, ordered witness and
assignment searches, and diagnostic text construction. Small examples specify
exact operation counts. Large domains check that early exits avoid eager lists
and that full scans accumulate costs without deferred recursive additions.
Private definitions expose the production implementation to these tests without
adding a public diagnostic API.
-/

namespace LeanUfo.Test.Complexity.Diagnostics

open LeanUfo.UFO.DSL

-- Append traverses the right operand. Input-array construction is outside
-- this call, as is the allocator's treatment of shared left arrays.
example (left right : Array Nat) :
    (Complexity.Costed.appendArray left right).value = left ++ right :=
  Complexity.Costed.appendArray_value left right
example (left right : Array Nat) :
    (Complexity.Costed.appendArray left right).cost = 3 * right.size :=
  Complexity.Costed.appendArray_cost left right
example : Complexity.Costed.appendArray #[1, 2] #[3, 4, 5] = ⟨#[1, 2, 3, 4, 5], 9⟩ := by native_decide
example : Complexity.Costed.appendArray (#[] : Array Nat) #[] = ⟨#[], 0⟩ := by native_decide
example : (Complexity.Costed.appendArray (Array.replicate 100000 1) #[2]).cost = 3 := by native_decide
example : (Complexity.Costed.appendArray #[1] (Array.replicate 100000 2)).cost = 300000 := by native_decide

example (fact : NamedScopedFact) :
    (namedFactSummaryCosted fact).value = namedFactSummarySpec fact :=
  namedFactSummaryCosted_value fact

example (fact : NamedScopedFact) : (namedFactSummaryCosted fact).cost ≤ 15 :=
  namedFactSummaryCosted_cost_le fact

example : namedFactSummaryCosted (.unary .mode "a" .everywhere) =
    ⟨"[everywhere] Mode(a)", 9⟩ := by native_decide
example : namedFactSummaryCosted (.binary .inst "a" "b" (.at "w")) =
    ⟨"[w] a :: b", 8⟩ := by native_decide
example : namedFactSummaryCosted (.binary .sub "a" "b" (.at "w")) =
    ⟨"[w] a ⊑ b", 8⟩ := by native_decide
example : namedFactSummaryCosted (.binary .inheresIn "a" "b" (.at "w")) =
    ⟨"[w] InheresIn(a, b)", 12⟩ := by native_decide
example : namedFactSummaryCosted (.ternary .distance "a" "b" "c" (.at "w")) =
    ⟨"[w] Distance(a, b, c)", 13⟩ := by native_decide
example : namedFactSummaryCosted (.tupleProjection "t" 12 "a" (.at "w")) =
    ⟨"[w] TupleProjection(t, 12, a)", 11⟩ := by native_decide

example : namedDerivedFactSummaryCosted (.unary "P" "a") = ⟨"P(a)", 4⟩ := by native_decide
example : namedDerivedFactSummaryCosted (.binary "P" "a" "b") =
    ⟨"P(a, b)", 6⟩ := by native_decide
example : namedDerivedFactSummaryCosted (.ternary "P" "a" "b" "c") =
    ⟨"P(a, b, c)", 8⟩ := by native_decide
example : namedFactSummaryCosted (.derived (.quaternary "P" "a" "b" "c" "d") (.at "w")) =
    ⟨"[w] [derived assertion] P(a, b, c, d)", 15⟩ := by native_decide

open private unarySourceEvidenceCosted unarySourceEvidenceCosted_cost_le
  unaryEvidenceCosted unaryEvidenceCosted_value unaryEvidenceSpec unaryEvidenceCosted_cost_le
  from LeanUfo.UFO.DSL.Diagnostic.AxiomAnalysis

-- Name mismatch and scope mismatch skip taxonomy traversal and all text.
example : unaryEvidenceCosted #[] #[] #[] 0 0 .mode = ⟨#[], 5⟩ := by native_decide
example : unaryEvidenceCosted #[`w] #[`a]
    #[.unary .mode "b" .everywhere] 0 0 .mode = ⟨#[], 12⟩ := by native_decide
example : unaryEvidenceCosted #[`w] #[`a]
    #[.unary .mode "a" (.at "v")] 0 0 .mode = ⟨#[], 19⟩ := by native_decide
example : unaryEvidenceCosted #[`w] #[`a]
    #[.binary .inst "a" "b" .everywhere] 0 0 .mode = ⟨#[], 9⟩ := by native_decide
example : unaryEvidenceCosted #[`w] #[`a]
    #[.unary .mode "a" .everywhere] 0 0 .object = ⟨#[], 102⟩ := by native_decide
example : unaryEvidenceCosted #[`w] #[`a]
    #[.unary .mode "a" .everywhere] 0 0 .mode =
    ⟨#["[everywhere] Mode(a)"], 99⟩ := by native_decide
example : unaryEvidenceCosted #[`w] #[`a]
    #[.unary .mode "a" .everywhere] 0 0 .moment =
    ⟨#["[everywhere] Mode(a) (taxonomy expansion implies moment)"], 110⟩ := by native_decide
example : unaryEvidenceCosted #[`w] #[`a]
    #[.unary .mode "a" .everywhere, .unary .mode "a" .everywhere] 0 0 .mode =
    ⟨#["[everywhere] Mode(a)", "[everywhere] Mode(a)"], 193⟩ := by native_decide
example : unaryEvidenceCosted #[`w] #[`a]
    (Array.replicate 100000 (.unary .mode "b" .everywhere)) 0 0 .mode =
    ⟨#[], 700005⟩ := by native_decide

example (worldNames thingNames : Array Lean.Name) (facts : Array NamedScopedFact)
    (thingIdx worldIdx : Nat) (field : UnaryField) :
    (unaryEvidenceCosted worldNames thingNames facts thingIdx worldIdx field).value =
      unaryEvidenceSpec worldNames thingNames facts thingIdx worldIdx field :=
  unaryEvidenceCosted_value worldNames thingNames facts thingIdx worldIdx field

example (worldNames thingNames : Array Lean.Name) (facts : Array NamedScopedFact)
    (thingIdx worldIdx : Nat) (field : UnaryField) :
    (unaryEvidenceCosted worldNames thingNames facts thingIdx worldIdx field).cost ≤
      5 + 270 * facts.size :=
  unaryEvidenceCosted_cost_le worldNames thingNames facts thingIdx worldIdx field

open private scopeCoversWorldCosted scopeCoversWorldCosted_value scopeCoversWorldCosted_cost
  unaryFactImpliesCosted unaryFactImpliesCosted_value unaryFactImpliesCosted_cost_le
  from LeanUfo.UFO.DSL.Diagnostic.AxiomAnalysis

example : scopeCoversWorldCosted #[] .everywhere 100 = ⟨true, 1⟩ := by native_decide
example : scopeCoversWorldCosted #[`w] (.at "w") 0 = ⟨true, 6⟩ := by native_decide
example : scopeCoversWorldCosted #[`w] (.at "v") 0 = ⟨false, 6⟩ := by native_decide
example : scopeCoversWorldCosted #[] (.at "#3") 3 = ⟨true, 6⟩ := by native_decide

-- Ancestor construction costs 68 for Mode. The membership scan costs four
-- operations per visited field, including the field that supplies a match.
example : unaryFactImpliesCosted .mode .mode = ⟨true, 72⟩ := by native_decide
example : unaryFactImpliesCosted .mode .concreteIndividual = ⟨true, 88⟩ := by native_decide
example : unaryFactImpliesCosted .mode .object = ⟨false, 88⟩ := by native_decide
example : unaryFactImpliesCosted .ex .ex = ⟨true, 8⟩ := by native_decide

example (source target : UnaryField) : (unaryFactImpliesCosted source target).cost ≤ 234 :=
  unaryFactImpliesCosted_cost_le source target

example (source target : UnaryField) :
    (unaryFactImpliesCosted source target).value =
      (expandUnaryTaxonomyFact source 0 0).any (fun
        | .unary field _ _ => field == target
        | _ => false) := unaryFactImpliesCosted_value source target

open private collectNamedFactEvidenceCosted collectNamedFactEvidenceCosted_value
  collectNamedFactEvidenceCosted_cost collectNamedFactEvidenceCosted_cost_le
  from LeanUfo.UFO.DSL.Diagnostic.AxiomAnalysis

-- The scan costs one initialization, then two loop operations and one Option
-- test per fact. A retained row costs one further array write.
example : collectNamedFactEvidenceCosted #[] (fun _ => .tick (some "row") 7) =
    ⟨#[], 1⟩ := by native_decide

example : collectNamedFactEvidenceCosted
    #[.unary .moment "a" .everywhere, .unary .moment "a" .everywhere]
    (fun _ => .tick (some "row") 7) = ⟨#["row", "row"], 23⟩ := by native_decide

example : collectNamedFactEvidenceCosted
    #[.unary .moment "a" .everywhere, .unary .moment "b" .everywhere]
    (fun _ => .tick none 7) = ⟨#[], 21⟩ := by native_decide

example : collectNamedFactEvidenceCosted
    #[.unary .moment "a" .everywhere, .binary .inst "a" "b" .everywhere,
      .unary .moment "c" .everywhere, .unary .moment "a" .everywhere]
    (fun fact => match fact with
      | .unary _ name _ => .tick (some name) 2
      | _ => .tick none 1) = ⟨#["a", "c", "a"], 23⟩ := by native_decide

example (facts : Array NamedScopedFact)
    (render? : NamedScopedFact → Complexity.Costed (Option String)) :
    (collectNamedFactEvidenceCosted facts render?).value =
      (facts.toList.filterMap fun fact => (render? fact).value).toArray :=
  collectNamedFactEvidenceCosted_value facts render?

example (facts : Array NamedScopedFact)
    (render? : NamedScopedFact → Complexity.Costed (Option String))
    (bound : Nat) (h : ∀ fact ∈ facts, (render? fact).cost ≤ bound) :
    (collectNamedFactEvidenceCosted facts render?).cost ≤ 1 + facts.size * (bound + 4) :=
  collectNamedFactEvidenceCosted_cost_le facts render? bound h

example : collectNamedFactEvidenceCosted
    (Array.replicate 100000 (.unary .moment "a" .everywhere))
    (fun _ => .tick none 1) = ⟨#[], 400001⟩ := by native_decide

open private lookupVarCosted lookupVarCosted_push_same lookupVarCosted_cost
  evalDiagFormulaCosted DiagFormula.eqThing DiagFormula.and
  DiagFormula.eqWorld DiagFormula.atom DiagFormula.not DiagFormula.or DiagFormula.imp DiagFormula.iff
  DiagFormula.forallThing DiagFormula.existsThing DiagFormula.forallWorld
  DiagFormula.existsWorld DiagFormula.box DiagFormula.dia
  assertedDerivedPropLookupCosted assertedDerivedPropLookupCosted_value
  foldDiagDomainCosted foldDiagDomainCosted_value foldDiagDomainCosted_cost_le
  foldDiagEnvsUntilCosted DiagVar.mk DiagVar.name DiagVar.kind DiagVarKind.thing DiagVarKind.world
  DiagFormula DiagFormula.peelForallsCosted DiagFormula.peelForallsCosted_value
  DiagFormula.peelForallsCosted_cost DiagFormula.forallVars DiagFormula.stripForalls
  foldDiagEnvsUntilCosted_eq_list foldDiagVarsCosted
  hasPossibleInstanceCosted
  boxExImpLookupCosted existsWithoutLookupCosted existentialIndependenceLookupCosted
  externallyDependentLookupCosted externallyDependentModeLookupCosted
  externallyDependentLookupCosted_sparse_value
  externallyDependentWitnessesCosted
  declaredExternalCandidatesCosted assertedDerivedBinaryLookupCosted
  firstModeStatusCandidateCosted firstModeStatusCandidateCosted_sparse_value
  findDiagDomainCosted firstExWithoutCosted firstExWithoutCosted_sparse_value
  indexedNameCosted indexedNameCosted_value indexedNameCosted_cost
  firstExternalIndependenceFailureCosted firstExternalBearerFailureCosted
  firstExternalBearerWitnessCosted
  firstExternallyDependentFailureReasonCosted
  joinIndexedNamesCosted joinIndexedNamesCosted_value renderExternallyDependentModeStatusCosted
  renderModeFailureRowsCosted
  ax71AssignmentCosted ax71AssignmentsCosted ax71FailureRowsCosted ax71FoundationAnalysisCosted
  partLookupCosted sameFoundationLookupCosted sameFoundationLookupCosted_iff
  ax73CharacterizedCosted ax73CharacterizationZScanCosted foundationEqCosted
  ax73ConstituentFailureCosted ax73ConstituentFailureCosted_isNone
  Ax73ConstituentFailure Ax73ConstituentFailure.missingMode
  Ax73ConstituentFailure.missingInherence Ax73ConstituentFailure.missingFoundation
  Ax73ConstituentFailure.missingPart
  ax73PrimaryFailureCosted ax73PrimaryFailureCosted_isNone
  ax73PrimaryEvidenceCosted ax73PrimaryZScanCosted
  ax73ReverseEvidenceCosted ax73AssignmentCosted ax73AssignmentsCosted
  ax73AssignmentCosted_isNone ax73AssignmentsCosted_eq_none_iff
  ax73PartCharacterizationAnalysisCosted ax73PartCharacterizationAnalysisCosted_size_le
  ax78EvidenceCosted ax78FoundationPairCosted ax78FoundationScanCosted
  ax78FoundationAnalysisCosted ax78FoundationAnalysisCosted_budget
  properPartCandidatesCosted properPartCandidatesCosted_nodup
  properPartCandidatesCosted_mem properPartCandidatesCosted_sparse_value
  Ax79PairFailure Ax79PairFailure.missingQua Ax79PairFailure.differentFoundation
  Ax79PairFailure.missingFoundation Ax79PairFailure.missingDependence
  ax79PairFailureCosted ax79PairEvidenceCosted ax79PairAnalysisCosted
  ax79PairEvidenceCosted_missingQua_cost ax79PairEvidenceCosted_missingDependence_cost
  ax79PairAnalysisCosted_some_size ax79PartPairsCosted
  ax79PartPairsCosted_value ax79PartPairsCosted_cost_le ax79PartPairsCostBound
  ax79PartPairsCostBound_mono
  ax79MissingPartsEvidenceCosted ax79MissingPartsEvidenceCosted_cost
  ax79RelatorAssignmentCosted ax79RelatorsCosted ax79FoundationAnalysisCosted
  ax79FoundationAnalysisCosted_size_le ax79FoundationAnalysisCostBound
  ax79FoundationAnalysisCostBound_mono
  productFamilyEntryPresentCosted productFamilyEntryPresentCosted_value
  productFamilyEntryPresentCosted_cost_le
  characterizationTargetsCosted ax99FailureEvidenceCosted ax99AssociationCosted
  UltimateBearerCandidate UltimateBearerCandidate.mk UltimateBearerCandidate.bearer UltimateBearerCandidate.path
  renderUltimateBearerCosted renderUltimateBearersCosted ax68FailureRowsCosted
  ax68ClosureAnalysisCostBound ax68ClosureAnalysisCostBound_mono
  ax68ClosureAnalysisCosted_cost_le ax68ClosureAnalysisCosted_size_le
  ultimateBearerCandidateCosted ultimateBearerCandidatesCosted
  ultimateBearerCandidatesCosted_paths_size
  firstMomentWithoutUltimateBearerCosted firstMomentWithMultipleUltimateBearersCosted
  ax68SearchCostBound ax68SearchCostBound_mono
  ax99QualityDomainCosted ax99AssignmentsCosted ax99QualityDomainAnalysisCosted
  ax99QualityDomainAnalysisCostBound ax99QualityDomainAnalysisCostBound_mono
  foundationCandidatesCosted
  foundationCandidatesCosted_nodup uniqueFoundationCosted uniqueFoundationCosted_sparse_value
  renderAmbiguousFoundationsCosted
  renderAmbiguousFoundationsCosted_value renderFoundationStatusCosted
  genericFunctionalDependenceLookupCosted genericConstitutionalDependenceLookupCosted
  individualFunctionalDependenceLookupCosted componentOfLookupCosted
  constitutionLookupCosted quaIndividualLookupCosted
  derivedUnaryLookupCosted derivedBinaryLookupCosted diagFinThingTerm diagFinWorldTerm
  diagFinThingTermCosted diagFinWorldTermCosted appendDiagTermCosted
  evalDiagAtomCosted DiagAtom.unary DiagAtom.binary DiagAtom.ternary DiagAtom.typeSem
  DiagAtom.quaternary DiagAtom.individualSem DiagAtom.derivedUnary DiagAtom.derivedBinary
  renderDiagVariableCosted renderDiagAtomCosted renderDiagAtomCosted_value renderDiagAtomSpec
  suggestionForAtomCosted suggestionForAtomCosted_value suggestionForAtomCosted_cost_le
  suggestionForAtomSpec
  suggestionFromAtomsCosted suggestionFromAtomsCosted_value suggestionFromAtomsCosted_cost_le
  suggestionForFailureCosted suggestionForFailureCosted_value suggestionForFailureSpec
  suggestionForFailureCosted_cost_le DiagFormula.suggestionCostBound
  DiagFormula.evalCostBound DiagFormula.evalCostBound_mono_env
  DiagFormula.failingAtomsCostBound_mono_env DiagFormula.failureDetailCostBound
  minimizeFailureCosted_detailCostBound
  minimizeFailureCosted MinimizedFailure.env MinimizedFailure.formula
  collectAtomsCosted collectAtomsCosted_cost_le collectAtomsIntoCosted
  collectAtomsIntoCosted_value collectAtomsIntoSpec
  collectAtomsIntoCosted_cost_eq_nodes_and_writes
  failingAtomsCosted failingAtomsIntoCosted failingAtomsIntoCosted_value failingAtomsIntoSpec
  failingAtomsIntoCosted_cost_le DiagFormula.failingAtomsCostBound
  failingAtomsIntoCosted_size_le failingAtomsCosted_value failingAtomsSpec
  failingAtomsCosted_cost_le DiagFormula.failingAtomCountBound
  renderDiagAtomCosted_cost_le renderDiagFormulaCosted renderDiagFormulaCosted_value
  renderDiagFormulaCosted_cost_le renderDiagFormulaCostBound_mono renderDiagFormulaSpec DiagFormula.nodeCount DiagAtom
  diagnosticWitnessesInnerCosted diagnosticWitnessesInnerCosted_cost_le
  appendEvidenceLinesCosted appendEvidenceLinesCosted_value appendEvidenceLinesCosted_size_le
  appendEvidenceLinesCosted_cost_eq_emitted
  DiagVar envSummaryCosted envSummarySpec envSummaryCosted_value envSummaryCosted_cost_le
  renderDiagAssignmentCosted renderDiagAssignmentCosted_value renderDiagAssignmentCosted_cost
  envSummaryCostBound_mono appendDiagnosticPreambleCosted appendDiagnosticPreambleCosted_value
  appendDiagnosticPreambleCosted_size_le appendDiagnosticPreambleCosted_cost_le pushDiagnosticIfRoom
  appendDiagnosticPreambleCosted_cost_eq_emitted
  genericDiagnosticVisitCosted
  DiagJunction DiagJunction.conjunction DiagJunction.disjunction
  flattenDiagJunctionCosted flattenDiagJunctionCosted_value flattenDiagJunctionCosted_cost_le
  flattenDiagJunctionSpec flattenDiagJunctionSpec_metrics
  renderDiagnosticRowsCosted renderDiagnosticConditionCosted renderDiagnosticConditionCosted_value
  renderDiagnosticConditionSpec renderDiagnosticConditionCosted_cost_le
  diagnosticConditionLabelCosted diagnosticConditionLabelCosted_value diagnosticConditionLabelSpec
  renderDiagnosticConditionLineCosted renderDiagnosticConditionLineCosted_value
  renderDiagnosticConditionLineSpec renderDiagnosticConditionLineCosted_cost_le
  renderDiagnosticConditionLineCostBound_mono
  formulaBoundVarKindsIntoCosted formulaBoundVarKindsIntoCosted_value formulaBoundVarKindsSpec
  formulaBoundVarKindsIntoCosted_cost_le envVarKindCosted envVarKindCosted_value envVarKind?
  diagnosticEnvVarsCosted diagnosticEnvVarsCosted_value diagnosticEnvVarsIntoSpec
  diagnosticEnvVarsCosted_size_le diagnosticEnvVarsCostBound diagnosticEnvVarsCostBound_mono
  diagnosticEnvVarsCosted_cost_le
  from LeanUfo.UFO.DSL.Diagnostic.AxiomAnalysis

private def mixedUniversalPrefix : DiagFormula :=
  DiagFormula.forallThing "x" (DiagFormula.forallWorld "w"
    (DiagFormula.forallThing "x" (DiagFormula.eqThing "x" "x")))

private def renderEnv : Array (String × Nat) := #[("w", 0), ("x", 0), ("y", 1)]

-- Each name costs 17 operations in this three-entry environment. The remaining
-- cost covers the two truth-value selections, atom/field selection, and joins.
private def suggestionAtoms : Array DiagAtom := #[
  DiagAtom.unary .moment "x" "w",
  DiagAtom.binary .inst "x" "y" "w",
  DiagAtom.binary .sub "x" "y" "w",
  DiagAtom.binary .inheresIn "x" "y" "w",
  DiagAtom.ternary .distance "x" "y" "x" "w",
  DiagAtom.derivedUnary "Custom" "x" "w",
  DiagAtom.derivedBinary "Custom" "x" "y" "w",
  DiagAtom.quaternary "Custom" "x" "y" "x" "y" "w",
  DiagAtom.typeSem "x" "w",
  DiagAtom.individualSem "x" "w"]

example : (suggestionAtoms.map fun atom =>
    (suggestionForAtomCosted #[`w] #[`a, `b] renderEnv atom true).cost) =
    #[46, 63, 63, 66, 84, 45, 64, 102, 23, 23] := by native_decide
example : (suggestionAtoms.map fun atom =>
    (suggestionForAtomCosted #[`w] #[`a, `b] renderEnv atom false).cost) =
    #[46, 63, 63, 66, 84, 45, 64, 102, 23, 23] := by native_decide

example : (suggestionForAtomCosted #[`w] #[`a, `b] renderEnv
    (DiagAtom.binary .inst "x" "y" "w") true).value =
    "Add the missing DSL fact `a :: b` at `w` (or in an appropriate broader scope), or remove/relax the facts shown in this counterexample that make this obligation apply." := by native_decide
example : (suggestionForAtomCosted #[`w] #[`a, `b] renderEnv
    (DiagAtom.binary .sub "x" "y" "w") false).value =
    "Remove or reclassify the DSL fact `a ⊑ b` at `w` (or in an appropriate broader scope), or remove/relax the facts shown in this counterexample that make this combination forbidden." := by native_decide
example : suggestionForAtomCosted #[] #[] #[] (DiagAtom.typeSem "x" "w") true =
    ⟨"Make `#0` behave as a type by adding at least one compatible instantiation, or remove/relax the facts shown in this counterexample that require it to be a type.", 11⟩ := by native_decide
example : suggestionForAtomCosted #[] #[`a, `b] #[("x", 0), ("x", 1)]
    (DiagAtom.individualSem "x" "unused") false =
    ⟨"Add a compatible instantiation for `b` if it should be a type, or remove/relax the facts shown in this counterexample that forbid it from being an individual.", 19⟩ := by native_decide

example (worlds things : Array Lean.Name) (env : Array (String × Nat))
    (atom : DiagAtom) (wanted : Bool) :
    (suggestionForAtomCosted worlds things env atom wanted).value =
      suggestionForAtomSpec worlds things env atom wanted :=
  suggestionForAtomCosted_value worlds things env atom wanted
example (worlds things : Array Lean.Name) (env : Array (String × Nat))
    (atom : DiagAtom) (wanted : Bool) :
    (suggestionForAtomCosted worlds things env atom wanted).cost ≤ 20 * env.size + 42 :=
  suggestionForAtomCosted_cost_le worlds things env atom wanted

private def layoutEquality : DiagFormula := DiagFormula.eqThing "x" "y"

private def atomScanFormula : DiagFormula :=
  DiagFormula.and
    (DiagFormula.imp (DiagFormula.atom (DiagAtom.unary .moment "x" "w"))
      (DiagFormula.eqThing "x" "x"))
    (DiagFormula.forallThing "x" (DiagFormula.existsWorld "v"
      (DiagFormula.box "w" "v"
        (DiagFormula.and (DiagFormula.atom (DiagAtom.binary .inst "x" "y" "w"))
          (DiagFormula.not (DiagFormula.atom (DiagAtom.unary .moment "x" "w")))))))

-- The scan visits eleven nodes and appends three atoms. Initialization costs
-- one more operation. Negation retains its atom, and binders do not add copies.
example : (collectAtomsCosted atomScanFormula).cost = 15 := by native_decide
example : ((collectAtomsCosted atomScanFormula).value.map
    (renderDiagAtomSpec #[`w] #[`a, `b] renderEnv)) =
    #["[w] Moment(a)", "[w] a :: b", "[w] Moment(a)"] := by native_decide
example : (collectAtomsCosted layoutEquality).cost = 2 := by native_decide
example : (collectAtomsCosted layoutEquality).value.size = 0 := by native_decide
example : (collectAtomsIntoCosted #[DiagAtom.typeSem "x" "w"] atomScanFormula).cost = 14 := by
  native_decide
example : (collectAtomsIntoCosted #[DiagAtom.typeSem "x" "w"] atomScanFormula).value.size = 4 := by
  native_decide
example (out : Array DiagAtom) (formula : DiagFormula) :
    (collectAtomsIntoCosted out formula).value = collectAtomsIntoSpec out formula :=
  collectAtomsIntoCosted_value out formula
example (formula : DiagFormula) :
    (collectAtomsCosted formula).cost ≤ 2 * DiagFormula.nodeCount formula + 1 :=
  collectAtomsCosted_cost_le formula
example (out : Array DiagAtom) (formula : DiagFormula) :
    (collectAtomsIntoCosted out formula).cost + out.size =
      DiagFormula.nodeCount formula + (collectAtomsIntoCosted out formula).value.size :=
  collectAtomsIntoCosted_cost_eq_nodes_and_writes out formula

private def atomScanNegations : DiagFormula :=
  (List.range 1000).foldl (fun formula _ => DiagFormula.not formula)
    (DiagFormula.atom (DiagAtom.unary .moment "x" "w"))

-- Input construction is outside the scan count: 1,001 node selections,
-- one atom write, and one initialization give 1,003 operations.
example : (collectAtomsCosted atomScanNegations).cost = 1003 := by native_decide
example : (collectAtomsCosted atomScanNegations).value.size = 1 := by native_decide

private def discoveryFormula : DiagFormula :=
  DiagFormula.and
    (DiagFormula.forallThing "x" (DiagFormula.existsWorld "z" layoutEquality))
    (DiagFormula.box "w" "v" (DiagFormula.forallThing "z" layoutEquality))
private def discoveryOuter : Array DiagVar :=
  #[DiagVar.mk "x" DiagVarKind.world, DiagVar.mk "y" DiagVarKind.thing]
private def discoveryEnv : Array (String × Nat) :=
  #[("z", 99), ("unknown", 0), ("x", 0), ("z", 0), ("v", 0), ("y", 0)]

-- Outer declarations precede formula binders. Duplicate binder names remain
-- in the candidate array, whose first match determines the displayed kind.
example : ((formulaBoundVarKindsIntoCosted discoveryOuter discoveryFormula).value.toList.map DiagVar.name) =
    ["x", "y", "x", "z", "v", "z"] := by native_decide
example : (formulaBoundVarKindsIntoCosted discoveryOuter discoveryFormula).cost = 11 := by native_decide
example : (envVarKindCosted discoveryOuter "x").cost = 11 := by native_decide
example : (envVarKindCosted discoveryOuter "y").cost = 16 := by native_decide
example : (envVarKindCosted discoveryOuter "unknown").cost = 16 := by native_decide
example : (envVarKindCosted #[] "x").cost = 0 := by native_decide
example : (envVarKindCosted discoveryOuter "x").value = some DiagVarKind.world := by rfl

example : ((diagnosticEnvVarsCosted discoveryOuter discoveryFormula discoveryEnv).value.toList.map DiagVar.name) =
    ["z", "x", "v", "y"] := by native_decide
example : (envSummaryCosted #[`W] #[`T]
    (diagnosticEnvVarsCosted discoveryOuter discoveryFormula discoveryEnv).value discoveryEnv).value =
    "z = W, x = W, v = W, y = T" := by native_decide
example : (diagnosticEnvVarsCosted #[] layoutEquality #[]).cost = 2 := by native_decide
example : (diagnosticEnvVarsCosted #[] layoutEquality #[("unknown", 0), ("unknown", 1)]).value.size = 0 := by native_decide
example : (diagnosticEnvVarsCosted #[] layoutEquality #[("unknown", 0), ("unknown", 1)]).cost = 10 := by native_decide
example : (diagnosticEnvVarsCosted
    #[DiagVar.mk "x" DiagVarKind.thing, DiagVar.mk "y" DiagVarKind.thing]
    layoutEquality #[("x", 0), ("y", 1)]).cost = 43 := by native_decide
-- Full scans retain constant stack use in the shared forward array fold.
-- Unknown names do not enlarge the output, and duplicates skip kind lookup.
example : (diagnosticEnvVarsCosted #[] layoutEquality
    (Array.replicate 100000 ("unknown", 0))).cost = 400002 := by native_decide
example : (diagnosticEnvVarsCosted #[DiagVar.mk "x" DiagVarKind.thing] layoutEquality
    (Array.replicate 100000 ("x", 0))).cost = 700008 := by native_decide
example (outer : Array DiagVar) (formula : DiagFormula) (env : Array (String × Nat)) :
    (diagnosticEnvVarsCosted outer formula env).value =
      diagnosticEnvVarsIntoSpec (outer ++ (formulaBoundVarKindsSpec formula).toArray) {} #[] env.toList :=
  diagnosticEnvVarsCosted_value outer formula env
example (outer : Array DiagVar) (formula : DiagFormula) (env : Array (String × Nat)) :
    (diagnosticEnvVarsCosted outer formula env).value.size ≤ env.size := diagnosticEnvVarsCosted_size_le outer formula env
example (outer : Array DiagVar) (formula : DiagFormula) (env : Array (String × Nat)) :
    (diagnosticEnvVarsCosted outer formula env).cost ≤
      diagnosticEnvVarsCostBound (DiagFormula.nodeCount formula) outer.size env.size :=
  diagnosticEnvVarsCosted_cost_le outer formula env
example {F F' V V' E E' : Nat} (hF : F ≤ F') (hV : V ≤ V') (hE : E ≤ E') :
    diagnosticEnvVarsCostBound F V E ≤ diagnosticEnvVarsCostBound F' V' E' :=
  diagnosticEnvVarsCostBound_mono hF hV hE

private def nestedLayout : DiagFormula :=
  DiagFormula.and layoutEquality
    (DiagFormula.and (DiagFormula.not layoutEquality) (DiagFormula.or layoutEquality layoutEquality))

private def thousandConjunctions : DiagFormula := Id.run do
  let mut formula := layoutEquality
  for _ in [:1000] do
    formula := DiagFormula.and formula layoutEquality
  return formula

-- Input construction is outside the measured traversal and layout calls.
example : (flattenDiagJunctionCosted DiagJunction.conjunction thousandConjunctions).cost = 5004 := by native_decide
example : (flattenDiagJunctionCosted DiagJunction.conjunction thousandConjunctions).value.size = 1001 := by native_decide
example : (renderDiagnosticConditionLineCosted #[] #[] #[] thousandConjunctions).cost = 33037 := by native_decide

example : (flattenDiagJunctionCosted DiagJunction.conjunction nestedLayout).cost = 14 := by native_decide
example : ((flattenDiagJunctionCosted DiagJunction.conjunction nestedLayout).value.toList.map
    (renderDiagFormulaSpec #[`w] #[`a, `b] renderEnv)) =
    ["a = b", "not (a = b)", "(a = b) or (a = b)"] := by native_decide
example : (flattenDiagJunctionCosted DiagJunction.disjunction nestedLayout).cost = 4 := by native_decide
example : (flattenDiagJunctionCosted DiagJunction.disjunction nestedLayout).value.size = 1 := by native_decide
example (junction : DiagJunction) (formula : DiagFormula) :
    (flattenDiagJunctionCosted junction formula).value = (flattenDiagJunctionSpec junction formula).toArray :=
  flattenDiagJunctionCosted_value junction formula
example (junction : DiagJunction) (formula : DiagFormula) :
    (flattenDiagJunctionCosted junction formula).cost ≤ 3 * DiagFormula.nodeCount formula + 1 :=
  flattenDiagJunctionCosted_cost_le junction formula

example : renderDiagnosticRowsCosted #[`w] #[`a, `b] renderEnv #[] = ⟨"", 1⟩ := by native_decide
example : renderDiagnosticRowsCosted #[`w] #[`a, `b] renderEnv #[layoutEquality, layoutEquality] =
    ⟨"- a = b\n- a = b", 85⟩ := by native_decide
example : renderDiagnosticConditionCosted #[`w] #[`a, `b] renderEnv
    (DiagFormula.and layoutEquality layoutEquality) = ⟨"- a = b\n- a = b", 95⟩ := by native_decide
example : diagnosticConditionLabelCosted (DiagFormula.and layoutEquality layoutEquality) =
    ⟨"Required together", 19⟩ := by native_decide
example : diagnosticConditionLabelCosted (DiagFormula.and (DiagFormula.not layoutEquality) layoutEquality) =
    ⟨"Missing witness requirements", 16⟩ := by native_decide
example : diagnosticConditionLabelCosted (DiagFormula.and layoutEquality (DiagFormula.not layoutEquality)) =
    ⟨"Missing witness requirements", 20⟩ := by native_decide
example : renderDiagnosticConditionLineCosted #[`w] #[`a, `b] renderEnv layoutEquality =
    ⟨"Required but missing: a = b.", 44⟩ := by native_decide
example : renderDiagnosticConditionLineCosted #[`w] #[`a, `b] renderEnv
    (DiagFormula.and layoutEquality layoutEquality) =
    ⟨"Required together:\n- a = b\n- a = b", 118⟩ := by native_decide
example : renderDiagnosticConditionLineCosted #[`w] #[`a, `b] renderEnv
    (DiagFormula.or layoutEquality layoutEquality) =
    ⟨"Need one of:\n- a = b\n- a = b", 100⟩ := by native_decide
example : renderDiagnosticConditionLineCosted #[`w] #[`a, `b] renderEnv (DiagFormula.not layoutEquality) =
    ⟨"Forbidden condition: not (a = b).", 47⟩ := by native_decide
example : renderDiagnosticConditionLineCosted #[`w] #[`a, `b] renderEnv
    (DiagFormula.existsThing "z" layoutEquality) =
    ⟨"Missing witness requirements: there exists thing z, a = b.", 48⟩ := by native_decide
-- The newline is in the source binder name, not in a generated row separator.
example : renderDiagnosticConditionLineCosted #[`w] #[`a, `b] renderEnv
    (DiagFormula.forallThing "x\nz" layoutEquality) =
    ⟨"Failed condition:\nfor every thing x\nz, a = b", 47⟩ := by native_decide
example (worldNames thingNames : Array Lean.Name) (env : Array (String × Nat)) (formula : DiagFormula) :
    (renderDiagnosticConditionLineCosted worldNames thingNames env formula).value =
      renderDiagnosticConditionLineSpec worldNames thingNames env formula :=
  renderDiagnosticConditionLineCosted_value worldNames thingNames env formula
example (worldNames thingNames : Array Lean.Name) (env : Array (String × Nat)) (formula : DiagFormula) :
    (renderDiagnosticConditionLineCosted worldNames thingNames env formula).cost ≤
      DiagFormula.nodeCount formula * (20 * env.size + 56) + 11 :=
  renderDiagnosticConditionLineCosted_cost_le worldNames thingNames env formula
example {F F' E E' : Nat} (hF : F ≤ F') (hE : E ≤ E') :
    F * (20 * E + 56) + 11 ≤ F' * (20 * E' + 56) + 11 :=
  renderDiagnosticConditionLineCostBound_mono hF hE

-- Assignment rows preserve the supplied order and repeat names when requested.
example : renderDiagAssignmentCosted #[`w] #[`a, `b] renderEnv (DiagVar.mk "y" DiagVarKind.thing) =
    ⟨"y = b", 20⟩ := by native_decide
example : envSummaryCosted #[`w] #[`a, `b] #[] renderEnv = ⟨"", 1⟩ := by native_decide
example : envSummaryCosted #[`w] #[`a, `b] #[DiagVar.mk "y" DiagVarKind.thing] renderEnv =
    ⟨"y = b", 24⟩ := by native_decide
example : envSummaryCosted #[`w] #[`a, `b]
    #[DiagVar.mk "x" DiagVarKind.thing, DiagVar.mk "y" DiagVarKind.thing,
      DiagVar.mk "w" DiagVarKind.world, DiagVar.mk "x" DiagVarKind.thing] renderEnv =
    ⟨"x = a, y = b, w = w, x = a", 99⟩ := by native_decide
example : envSummaryCosted #[`w] #[`a, `b] #[DiagVar.mk "x" DiagVarKind.thing, DiagVar.mk "x" DiagVarKind.thing]
    #[("x", 0), ("x", 1)] = ⟨"x = b, x = b", 41⟩ := by native_decide
example : envSummaryCosted #[] #[] #[DiagVar.mk "x" DiagVarKind.thing, DiagVar.mk "w" DiagVarKind.world] #[] =
    ⟨"x = #0, w = #0", 25⟩ := by native_decide
example (worldNames thingNames : Array Lean.Name) (vars : Array DiagVar)
    (env : Array (String × Nat)) :
    (envSummaryCosted worldNames thingNames vars env).value =
      envSummarySpec worldNames thingNames vars env :=
  envSummaryCosted_value worldNames thingNames vars env
example (worldNames thingNames : Array Lean.Name) (vars : Array DiagVar)
    (env : Array (String × Nat)) :
    (envSummaryCosted worldNames thingNames vars env).cost ≤ vars.size * (4 * env.size + 13) + 1 :=
  envSummaryCosted_cost_le worldNames thingNames vars env

example {V V' E E' : Nat} (hV : V ≤ V') (hE : E ≤ E') :
    V * (4 * E + 13) + 1 ≤ V' * (4 * E' + 13) + 1 :=
  envSummaryCostBound_mono hV hE

-- Already produced text costs 41. Three capacity checks cost six, even at
-- budget zero. Each retained row adds a write and an emission.
example : appendDiagnosticPreambleCosted 0 #[] ⟨"a", 11⟩ ⟨"b", 13⟩ ⟨"c", 17⟩ =
    ⟨#[], 47⟩ := by native_decide
example : appendDiagnosticPreambleCosted 1 #[] ⟨"a", 11⟩ ⟨"b", 13⟩ ⟨"c", 17⟩ =
    ⟨#["a"], 49⟩ := by native_decide
example : appendDiagnosticPreambleCosted 2 #[] ⟨"a", 11⟩ ⟨"b", 13⟩ ⟨"c", 17⟩ =
    ⟨#["a", "b"], 51⟩ := by native_decide
example : appendDiagnosticPreambleCosted 3 #[] ⟨"a", 11⟩ ⟨"b", 13⟩ ⟨"c", 17⟩ =
    ⟨#["a", "b", "c"], 53⟩ := by native_decide
example : appendDiagnosticPreambleCosted 2 #["kept"] (.pure "same") (.pure "same") (.pure "") =
    ⟨#["kept", "same"], 8⟩ := by native_decide
example : appendDiagnosticPreambleCosted 1 #["kept", "oversized"] ⟨"a", 11⟩ ⟨"b", 13⟩ ⟨"c", 17⟩ =
    ⟨#["kept", "oversized"], 47⟩ := by native_decide
example (budget : Nat) (out : Array String) (a b c : Complexity.Costed String) :
    (appendDiagnosticPreambleCosted budget out a b c).value =
      pushDiagnosticIfRoom budget
        (pushDiagnosticIfRoom budget (pushDiagnosticIfRoom budget out a.value) b.value) c.value :=
  appendDiagnosticPreambleCosted_value budget out a b c
example (budget : Nat) (out : Array String) (a b c : Complexity.Costed String)
    (hout : out.size ≤ budget) :
    (appendDiagnosticPreambleCosted budget out a b c).value.size ≤ budget :=
  appendDiagnosticPreambleCosted_size_le budget out a b c hout
example (budget : Nat) (out : Array String) (a b c : Complexity.Costed String) :
    (appendDiagnosticPreambleCosted budget out a b c).cost ≤ a.cost + b.cost + c.cost + 12 :=
  appendDiagnosticPreambleCosted_cost_le budget out a b c

example (budget : Nat) (out : Array String) (a b c : Complexity.Costed String) :
    (appendDiagnosticPreambleCosted budget out a b c).cost = a.cost + b.cost + c.cost + 6 +
      2 * ((appendDiagnosticPreambleCosted budget out a b c).value.size - out.size) :=
  appendDiagnosticPreambleCosted_cost_eq_emitted budget out a b c

-- This caller regression checks composition, not a whole-producer cost claim.
private def mergedFailureFormula : DiagFormula :=
  DiagFormula.or
    (DiagFormula.forallThing "x" (DiagFormula.eqThing "x" "y"))
    (DiagFormula.forallThing "z" (DiagFormula.eqThing "z" "y"))

-- Each failed branch extends the environment. Disjunction retains both
-- environments and rebuilds a smaller formula, so size bounds must cover both.
example : (MinimizedFailure.env
    (minimizeFailureCosted 1 2 {} #[("y", 1)] mergedFailureFormula).value).size = 4 := by native_decide
example : DiagFormula.nodeCount (MinimizedFailure.formula
    (minimizeFailureCosted 1 2 {} #[("y", 1)] mergedFailureFormula).value) = 3 := by native_decide
example : (failingAtomsCosted 1 2 {}
    (MinimizedFailure.env (minimizeFailureCosted 1 2 {} #[("y", 1)] mergedFailureFormula).value)
    (MinimizedFailure.formula (minimizeFailureCosted 1 2 {} #[("y", 1)] mergedFailureFormula).value)).cost =
    79 := by native_decide

-- The counter is 20 for evaluation, two for minimization, 43 for
-- variable discovery, one for the failed branch, 49 for assignment text plus
-- the empty-budget preamble, 36 for the condition line, six for the suggestion
-- line, and two for the final atom scan.
example : genericDiagnosticVisitCosted 0 #[`w] #[`a, `b] #[] {}
    #[DiagVar.mk "x" DiagVarKind.thing, DiagVar.mk "y" DiagVarKind.thing]
    (DiagFormula.eqThing "x" "y") #[] #[("x", 0), ("y", 1)] = ⟨#[], 159⟩ := by native_decide
example : genericDiagnosticVisitCosted 1 #[`w] #[`a, `b] #[] {}
    #[DiagVar.mk "x" DiagVarKind.thing, DiagVar.mk "y" DiagVarKind.thing]
    (DiagFormula.eqThing "x" "y") #[] #[("x", 0), ("y", 1)] =
    ⟨#["Counterexample assignment: x = a, y = b."], 161⟩ := by native_decide

example : Complexity.Costed.appendString ⟨"a", 7⟩ ⟨"b", 11⟩ = ⟨"ab", 19⟩ := by decide
example : Complexity.Costed.appendString (.pure "") (.pure "b") = ⟨"b", 1⟩ := by decide

-- Three bindings cost thirteen to scan and four to render the selected name.
example : renderDiagVariableCosted #[`a, `b] renderEnv "y" = ⟨"b", 17⟩ := by native_decide
example : renderDiagVariableCosted #[`a] #[("x", 7)] "x" = ⟨"#7", 9⟩ := by native_decide
example : renderDiagAtomCosted #[] #[] #[] (DiagAtom.typeSem "x" "w") =
    ⟨"[#0] Type(#0)", 15⟩ := by native_decide
example : renderDiagAtomCosted #[`w] #[`a, `b] #[("w", 0), ("x", 0), ("x", 1)]
    (DiagAtom.typeSem "x" "w") = ⟨"[w] Type(b)", 39⟩ := by native_decide
example : renderDiagAtomCosted #[`w] #[`a, `b] renderEnv (DiagAtom.individualSem "x" "w") =
    ⟨"[w] Individual(a)", 39⟩ := by native_decide
example : renderDiagAtomCosted #[`w] #[`a, `b] renderEnv (DiagAtom.unary .moment "x" "w") =
    ⟨"[w] Moment(a)", 42⟩ := by native_decide
example : renderDiagAtomCosted #[`w] #[`a, `b] renderEnv (DiagAtom.binary .inst "x" "y" "w") =
    ⟨"[w] a :: b", 58⟩ := by native_decide
example : renderDiagAtomCosted #[`w] #[`a, `b] renderEnv (DiagAtom.binary .sub "x" "y" "w") =
    ⟨"[w] a ⊑ b", 58⟩ := by native_decide
example : renderDiagAtomCosted #[`w] #[`a, `b] renderEnv (DiagAtom.binary .inheresIn "x" "y" "w") =
    ⟨"[w] InheresIn(a, b)", 62⟩ := by native_decide
example : renderDiagAtomCosted #[`w] #[`a, `b] renderEnv (DiagAtom.ternary .distance "x" "y" "x" "w") =
    ⟨"[w] Distance(a, b, a)", 80⟩ := by native_decide
example : renderDiagAtomCosted #[`w] #[`a, `b] renderEnv (DiagAtom.derivedUnary "Custom" "x" "w") =
    ⟨"[w] Custom(a)", 41⟩ := by native_decide
example : renderDiagAtomCosted #[`w] #[`a, `b] renderEnv (DiagAtom.derivedBinary "Custom" "x" "y" "w") =
    ⟨"[w] Custom(a, b)", 60⟩ := by native_decide
-- Five name resolutions and twelve concatenations attain the atom bound.
example : renderDiagAtomCosted #[`w] #[`a, `b] renderEnv
    (DiagAtom.quaternary "Custom" "x" "y" "x" "y" "w") =
    ⟨"[w] Custom(a, b, a, b)", 98⟩ := by native_decide

example : renderDiagFormulaCosted #[`w] #[`a, `b] renderEnv (DiagFormula.eqThing "x" "y") =
    ⟨"a = b", 37⟩ := by native_decide
example : renderDiagFormulaCosted #[`w] #[`a, `b] renderEnv
    (DiagFormula.not (DiagFormula.eqThing "x" "y")) = ⟨"not (a = b)", 40⟩ := by native_decide
example : renderDiagFormulaCosted #[`w] #[`a, `b] renderEnv
    (DiagFormula.and (DiagFormula.eqThing "x" "y") (DiagFormula.eqThing "y" "x")) =
    ⟨"(a = b) and (b = a)", 79⟩ := by native_decide
example : renderDiagFormulaCosted #[`w] #[`a, `b] renderEnv
    (DiagFormula.forallThing "z" (DiagFormula.eqThing "x" "y")) =
    ⟨"for every thing z, a = b", 41⟩ := by native_decide
example : renderDiagFormulaCosted #[`w] #[`a, `b] renderEnv
    (DiagFormula.box "w" "v" (DiagFormula.eqThing "x" "y")) =
    ⟨"from world w, in every accessible world v, a = b", 60⟩ := by native_decide

example (worlds things : Array Lean.Name) (env : Array (String × Nat)) (atom : DiagAtom) :
    (renderDiagAtomCosted worlds things env atom).value = renderDiagAtomSpec worlds things env atom :=
  renderDiagAtomCosted_value worlds things env atom
example (worlds things : Array Lean.Name) (env : Array (String × Nat)) (formula : DiagFormula) :
    (renderDiagFormulaCosted worlds things env formula).value = renderDiagFormulaSpec worlds things env formula :=
  renderDiagFormulaCosted_value worlds things env formula
example (worlds things : Array Lean.Name) (env : Array (String × Nat)) (formula : DiagFormula) :
    (renderDiagFormulaCosted worlds things env formula).cost ≤
      DiagFormula.nodeCount formula * (20 * env.size + 39) :=
  renderDiagFormulaCosted_cost_le worlds things env formula
example {F F' E E' : Nat} (hF : F ≤ F') (hE : E ≤ E') :
    F * (20 * E + 39) ≤ F' * (20 * E' + 39) := renderDiagFormulaCostBound_mono hF hE

-- Rendering follows syntax depth, not the sizes of quantified model domains.
private def nestedNegations : DiagFormula := Id.run do
  let mut formula := DiagFormula.eqThing "x" "y"
  for _ in [:1000] do
    formula := DiagFormula.not formula
  return formula

example : (renderDiagFormulaCosted #[`w] #[`a, `b] renderEnv nestedNegations).cost = 3037 := by
  native_decide
example : (renderDiagFormulaCosted #[`w] #[`a, `b] renderEnv nestedNegations).value.length = 6005 := by
  native_decide

example : (DiagFormula.peelForallsCosted mixedUniversalPrefix).cost = 11 := by native_decide
example : (DiagFormula.peelForallsCosted mixedUniversalPrefix).value.1.map DiagVar.name =
    #["x", "w", "x"] := by native_decide
example : (DiagFormula.peelForallsCosted mixedUniversalPrefix).value.1.map DiagVar.kind =
    #[DiagVarKind.thing, DiagVarKind.world, DiagVarKind.thing] := by native_decide
example : (DiagFormula.peelForallsCosted (DiagFormula.existsThing "y" mixedUniversalPrefix)).cost = 2 := by
  native_decide
example : (DiagFormula.peelForallsCosted (DiagFormula.box "w" "v" mixedUniversalPrefix)).value.1.size = 0 := by
  native_decide
example (formula : DiagFormula) :
    (DiagFormula.peelForallsCosted formula).value =
      (DiagFormula.forallVars formula, DiagFormula.stripForalls formula) :=
  DiagFormula.peelForallsCosted_value formula
example (formula : DiagFormula) :
    (DiagFormula.peelForallsCosted formula).cost = 3 * (DiagFormula.forallVars formula).size + 2 :=
  DiagFormula.peelForallsCosted_cost formula

-- Input construction is outside extraction. The cost accumulates before each tail call.
private def longUniversalPrefix : DiagFormula := Id.run do
  let mut formula := DiagFormula.eqThing "x" "x"
  for _ in [:100000] do
    formula := DiagFormula.forallThing "x" formula
  return formula

example : (DiagFormula.peelForallsCosted longUniversalPrefix).cost = 300002 := by native_decide
example : (DiagFormula.peelForallsCosted longUniversalPrefix).value.1.size = 100000 := by native_decide

private def pathNextHops : Array (Option Nat) :=
  #[some 0, some 1, some 1, none, some 1, some 2, none, none, some 2]

-- Path reconstruction stops at the target even with no remaining fuel.
-- A continued hop costs eleven, and target recognition plus its append costs three.
example : FactTables.nextHopPathFromCosted #[] 0 4 4 0 #[8] =
    ⟨some #[8, 4], 3⟩ := by native_decide
example : FactTables.nextHopPathFromCosted #[] 2 0 1 0 = ⟨none, 3⟩ := by native_decide
example : FactTables.nextHopPathFromCosted #[] 2 0 1 2 = ⟨none, 7⟩ := by native_decide
example : FactTables.nextHopPathFromCosted #[none, none] 2 0 1 2 =
    ⟨none, 9⟩ := by native_decide
example : FactTables.nextHopPathFromCosted pathNextHops 3 0 2 3 =
    ⟨some #[0, 1, 2], 25⟩ := by native_decide
example : FactTables.nextHopPathFrom? pathNextHops 3 0 2 3 =
    some #[0, 1, 2] := by native_decide
example : FactTables.nextHopPathFrom? pathNextHops 3 2 0 3 = none := by native_decide
example : FactTables.nextHopPathFromCosted pathNextHops 3 0 2 1 =
    ⟨none, 14⟩ := by native_decide

-- A cyclic raw table consumes fuel without retaining recursive cost additions.
example : FactTables.nextHopPathFromCosted #[none, some 0] 2 0 1 1000000 =
    ⟨none, 11000003⟩ := by native_decide
example : FactTables.momentOfPathCosted {} 3 0 0 2 = ⟨none, 2⟩ := by native_decide
example : FactTables.momentOfPathCosted { inherenceNextHops := #[pathNextHops] } 3 0 0 2 =
    ⟨some #[0, 1, 2], 29⟩ := by native_decide

-- Compiled cyclic and diamond graphs retain deterministic paths to an endpoint.
example : ((compileExplicitModelAST
    { worldCount := 1, thingCount := 3
      facts := #[.binary .inheresIn 0 1 0, .binary .inheresIn 1 0 0,
        .binary .inheresIn 1 2 0, .binary .inheresIn 0 1 0] }).momentOfPathCosted 3 0 0 2) =
    ⟨some #[0, 1, 2], 29⟩ := by native_decide
-- Pivots run from higher coordinates to lower ones. The route through two
-- is therefore stored before the competing route through one.
example : (compileExplicitModelAST
    { worldCount := 1, thingCount := 4
      facts := #[.binary .inheresIn 0 2 0, .binary .inheresIn 2 3 0,
        .binary .inheresIn 0 1 0, .binary .inheresIn 1 3 0] }).momentOfPath? 4 0 0 3 =
    some #[0, 2, 3] := by native_decide
example (tables : FactTables) (T w m b : Nat) (path : Array Nat)
    (h : (tables.momentOfPathCosted T w m b).value = some path) :
    path.size ≤ T + 1 := FactTables.momentOfPathCosted_some_size tables T w m b path h

private def ax68ChainTables := compileExplicitModelAST
  { worldCount := 1, thingCount := 3
    facts := #[.unary .moment 0 0, .unary .moment 1 0,
      .binary .inheresIn 0 1 0, .binary .inheresIn 1 2 0] }

private def ax68MissingTables := compileExplicitModelAST
  { worldCount := 1, thingCount := 2, facts := #[.unary .moment 0 0] }

private def ax68MultipleTables := compileExplicitModelAST
  { worldCount := 1, thingCount := 3
    facts := #[.unary .moment 0 0, .binary .inheresIn 0 1 0, .binary .inheresIn 0 2 0] }

-- Moments skip path reconstruction. A two-hop path to a non-moment costs 43,
-- including its moment query and both result branches.
example : (ultimateBearerCandidateCosted 1 3 ax68ChainTables 0 0 0).cost = 13 := by native_decide
example : (ultimateBearerCandidateCosted 1 3 ax68ChainTables 0 0 2).cost = 43 := by native_decide
example : (ultimateBearerCandidatesCosted 1 3 ax68ChainTables 0 0).value.map
    (fun c => (UltimateBearerCandidate.bearer c, UltimateBearerCandidate.path c)) =
    #[(2, #[0, 1, 2])] := by native_decide
example : (ultimateBearerCandidatesCosted 1 3 ax68ChainTables 0 0).cost = 83 := by native_decide
example : (ultimateBearerCandidatesCosted 1 2 ax68MissingTables 0 0).value.isEmpty = true := by
  native_decide
example : (ultimateBearerCandidatesCosted 1 2 ax68MissingTables 0 0).cost = 49 := by native_decide
example : (ultimateBearerCandidatesCosted 1 3 ax68MultipleTables 0 0).value.map
    (fun c => (UltimateBearerCandidate.bearer c, UltimateBearerCandidate.path c)) =
    #[(1, #[0, 1]), (2, #[0, 2])] := by native_decide
example : (ultimateBearerCandidatesCosted 1 3 ax68MultipleTables 0 0).cost = 92 := by native_decide

example : firstMomentWithoutUltimateBearerCosted 1 2 ax68MissingTables =
    ⟨some (0, 0), 74⟩ := by native_decide
example : firstMomentWithoutUltimateBearerCosted 1 3 ax68MultipleTables =
    ⟨none, 146⟩ := by native_decide
example : (firstMomentWithMultipleUltimateBearersCosted 1 3 ax68MultipleTables).cost = 116 := by
  native_decide

-- The precheck adds an option test and a branch to the 74-operation search.
-- Finding a missing bearer skips the multiple-bearer search entirely.
example : hasAx68ClosureFailureCosted 1 2 ax68MissingTables = ⟨true, 76⟩ := by
  native_decide
-- Both searches run here: 146 + 116, two option tests, and one branch.
example : hasAx68ClosureFailureCosted 1 3 ax68MultipleTables = ⟨true, 265⟩ := by
  native_decide
example : hasAx68ClosureFailureCosted 0 1000000 {} = ⟨false, 4⟩ := by
  native_decide
example : hasAx68ClosureFailure 1 3 ax68ChainTables = false := by native_decide
example (W T : Nat) (tables : FactTables) :
    (hasAx68ClosureFailureCosted W T tables).cost ≤
      2 * (W * (T * (T * (11 * T + 26) + 19) + 3)) + 4 :=
  hasAx68ClosureFailureCosted_cost_le W T tables

-- Missing-bearer priority applies even after an earlier multiple-bearer case.
example : (ax68ClosureAnalysisCosted #[`w] #[`a, `b, `c, `d]
    (compileExplicitModelAST
      { worldCount := 1, thingCount := 4
        facts := #[.unary .moment 0 0, .unary .moment 3 0,
          .binary .inheresIn 0 1 0, .binary .inheresIn 0 2 0] })).value[0]? =
    some "Closure check for ax68: `d` is a moment at `w`, but no non-moment ultimate bearer is reachable through `InheresIn`." := by
  native_decide
example : (firstMomentWithoutUltimateBearerCosted 2 2
    (compileExplicitModelAST
      { worldCount := 2, thingCount := 2
        facts := #[.unary .moment 0 1, .unary .moment 1 0] })).value = some (0, 1) := by
  native_decide

example : firstMomentWithoutUltimateBearerCosted 0 1000000 {} = ⟨none, 1⟩ := by native_decide
example : firstMomentWithoutUltimateBearerCosted 1 1000000 {} =
    ⟨none, 16000004⟩ := by native_decide
example : (ax68ClosureAnalysisCosted #[] #[] {}).value =
    #["Closure check for ax68: every moment in the diagnostic tables has exactly one non-moment endpoint in the stored next-hop paths.",
      "If certification still reports ax68, inspect the correspondence between these paths, the compiled closure, and MomentOf."] := by
  native_decide
example {W W' T T' : Nat} (hW : W ≤ W') (hT : T ≤ T') :
    ax68SearchCostBound W T ≤ ax68SearchCostBound W' T' := ax68SearchCostBound_mono hW hT

-- A two-name path costs 17. Its bearer name and four text joins cost eight.
example : joinIndexedNamesCosted #[`a, `b] #[0, 1] " InheresIn " =
    ⟨"a InheresIn b", 17⟩ := by native_decide
example : joinIndexedNamesCosted #[] #[0, 4] " InheresIn " =
    ⟨"#0 InheresIn #4", 17⟩ := by native_decide
example : renderUltimateBearerCosted #[`a, `b] (UltimateBearerCandidate.mk 1 #[0, 1]) =
    ⟨"`b` via `a InheresIn b`", 25⟩ := by native_decide
example : renderUltimateBearersCosted #[`a, `b, `c]
    #[UltimateBearerCandidate.mk 1 #[0, 1], UltimateBearerCandidate.mk 2 #[0, 2]] =
    ⟨"`b` via `a InheresIn b`, `c` via `a InheresIn c`", 59⟩ := by native_decide
example : renderUltimateBearersCosted #[] #[] = ⟨"", 1⟩ := by native_decide
example : (ax68FailureRowsCosted "a" "w" none).cost = 12 := by native_decide
example : (ax68FailureRowsCosted "a" "w" (some "paths")).cost = 14 := by native_decide

-- Missing: search 74, result branch one, two names eight, and rows twelve.
example : ax68ClosureAnalysisCosted #[`w] #[`a, `b] ax68MissingTables =
    ⟨#["Closure check for ax68: `a` is a moment at `w`, but no non-moment ultimate bearer is reachable through `InheresIn`.",
      "Suggestion: add an inherence chain from `a` to a concrete non-moment bearer, or reclassify the endpoint so it is not a moment."], 95⟩ := by
  native_decide
-- Multiple: searches 146+116, branches two, names eight, paths 59, rows fourteen.
example : ax68ClosureAnalysisCosted #[`w] #[`a, `b, `c] ax68MultipleTables =
    ⟨#["Closure check for ax68: `a` has multiple reachable non-moment bearers at `w`.",
      "Reachable bearers: `b` via `a InheresIn b`, `c` via `a InheresIn c`.",
      "Suggestion: remove the competing inherence branch, or reclassify the unintended endpoint so it is not an ultimate bearer."], 345⟩ := by
  native_decide
example : (ax68ClosureAnalysisCosted #[] #[] {}).cost = 8 := by native_decide
example {W W' T T' : Nat} (hW : W ≤ W') (hT : T ≤ T') :
    ax68ClosureAnalysisCostBound W T ≤ ax68ClosureAnalysisCostBound W' T' :=
  ax68ClosureAnalysisCostBound_mono hW hT
example (worldNames thingNames : Array Lean.Name) (tables : FactTables) :
    (ax68ClosureAnalysisCosted worldNames thingNames tables).cost ≤
      ax68ClosureAnalysisCostBound worldNames.size thingNames.size :=
  ax68ClosureAnalysisCosted_cost_le worldNames thingNames tables
example (worldNames thingNames : Array Lean.Name) (tables : FactTables) :
    (ax68ClosureAnalysisCosted worldNames thingNames tables).value.size ≤ 3 :=
  ax68ClosureAnalysisCosted_size_le worldNames thingNames tables

-- Evidence formatting reads only the prefix that fits after the existing rows.
example : appendEvidenceLinesCosted 2 #["prior"] #["a", "b", "c"] =
    ⟨#["prior", "  - a"], 8⟩ := by native_decide
example : appendEvidenceLinesCosted 5 #["prior"] #["a", "", "a"] =
    ⟨#["prior", "  - a", "  - ", "  - a"], 18⟩ := by native_decide
example : appendEvidenceLinesCosted 0 #[] #["a"] = ⟨#[], 3⟩ := by native_decide
example : appendEvidenceLinesCosted 1 #["prior"] #["a"] = ⟨#["prior"], 3⟩ := by native_decide
example : appendEvidenceLinesCosted 1 #["prior", "retained"] #["a"] =
    ⟨#["prior", "retained"], 3⟩ := by native_decide
example : appendEvidenceLinesCosted 4 #["prior"] #[] = ⟨#["prior"], 3⟩ := by native_decide
example : appendEvidenceLinesCosted 1 #[] (Array.replicate 1000000 "a") =
    ⟨#["  - a"], 8⟩ := by native_decide
example (budget : Nat) (out items : Array String) :
    (appendEvidenceLinesCosted budget out items).value =
      out ++ (items.extract 0 (budget - out.size)).map ("  - " ++ ·) :=
  appendEvidenceLinesCosted_value budget out items
example (budget : Nat) (out items : Array String) (h : out.size ≤ budget) :
    (appendEvidenceLinesCosted budget out items).value.size ≤ budget :=
  appendEvidenceLinesCosted_size_le budget out items h
example (budget : Nat) (out items : Array String) :
    (appendEvidenceLinesCosted budget out items).cost =
      5 * ((appendEvidenceLinesCosted budget out items).value.size - out.size) + 3 :=
  appendEvidenceLinesCosted_cost_eq_emitted budget out items

-- The shared prefix copy visits only retained items, including at budget zero.
example : Complexity.boundedEvidenceCosted 2 #["a", "b", "c"] =
    ⟨⟨#["a", "b"], true⟩, 12⟩ := by native_decide
example : Complexity.boundedEvidenceCosted 4 #["a", "b"] =
    ⟨⟨#["a", "b"], false⟩, 12⟩ := by native_decide
example : Complexity.boundedEvidenceCosted 0 #[1, 2, 3] =
    ⟨⟨#[], true⟩, 4⟩ := by native_decide
example : Complexity.boundedEvidenceCosted 3 (#[] : Array Nat) =
    ⟨⟨#[], false⟩, 4⟩ := by native_decide
example : Complexity.boundedEvidenceCosted 2 #[3, 1, 3] =
    ⟨⟨#[3, 1], true⟩, 12⟩ := by native_decide
example : Complexity.boundedEvidenceCosted 2 #[3, 1] =
    ⟨⟨#[3, 1], false⟩, 12⟩ := by native_decide
example : Complexity.boundedEvidenceCosted 4 #[3, 1] =
    ⟨⟨#[3, 1], false⟩, 12⟩ := by native_decide
example : Complexity.boundedEvidenceCosted 1 (Array.replicate 1000000 7) =
    ⟨⟨#[7], true⟩, 8⟩ := by native_decide

example (budget : Nat) (items : Array Nat) :
    (Complexity.boundedEvidence budget items).items = items.extract 0 budget := by
  rw [Complexity.boundedEvidence_eq_prefix]
example (budget : Nat) (items : Array Nat) :
    (Complexity.boundedEvidence budget (Complexity.boundedEvidence budget items).items).items =
      (Complexity.boundedEvidence budget items).items :=
  Complexity.boundedEvidence_items_idempotent budget items

example : lookupVarCosted #[] "x" = ⟨0, 1⟩ := by native_decide
example : lookupVarCosted #[("x", 7)] "x" = ⟨7, 5⟩ := by native_decide
example : lookupVarCosted #[("x", 7)] "missing" = ⟨0, 5⟩ := by native_decide
example : lookupVarCosted #[("x", 7), ("y", 9), ("x", 3)] "x" =
    ⟨3, 13⟩ := by native_decide
example : lookupVarCosted #[("x", 7), ("x", 0)] "x" = ⟨0, 9⟩ := by native_decide

-- Equality costs one constructor test, two nine-operation lookups, and one comparison.
example : evalDiagFormulaCosted 0 0 {} #[("x", 7), ("y", 9)]
    (DiagFormula.eqThing "x" "y") = ⟨false, 20⟩ := by native_decide

-- A false left operand stops conjunction before the right operand runs.
example : evalDiagFormulaCosted 0 0 {} #[("x", 7), ("y", 9)]
    (DiagFormula.and (DiagFormula.eqThing "x" "y") (DiagFormula.eqThing "x" "x")) =
      ⟨false, 22⟩ := by
  native_decide

-- Empty domains select the quantifier constructor but evaluate no assignments.
example : evalDiagFormulaCosted 0 0 {} #[("x", 7)]
    (DiagFormula.forallThing "y" (DiagFormula.eqThing "x" "y")) =
      ⟨true, 1⟩ := by native_decide
example : evalDiagFormulaCosted 0 0 {} #[("x", 7)]
    (DiagFormula.existsThing "y" (DiagFormula.eqThing "x" "y")) =
      ⟨false, 1⟩ := by native_decide

-- These million-element domains stop at coordinate zero. Each evaluation
-- costs 20 for equality, one environment push, two scan operations, and one
-- outer quantifier-constructor test.
example : evalDiagFormulaCosted 0 1000000 {} #[("x", 7)]
    (DiagFormula.forallThing "y" (DiagFormula.eqThing "x" "y")) =
      ⟨false, 24⟩ := by native_decide
example : evalDiagFormulaCosted 0 1000000 {} #[("x", 7)]
    (DiagFormula.existsThing "y" (DiagFormula.eqThing "y" "y")) =
      ⟨true, 24⟩ := by native_decide
example : evalDiagFormulaCosted 1000000 0 {} #[("x", 7)]
    (DiagFormula.forallWorld "y" (DiagFormula.eqThing "x" "y")) =
      ⟨false, 24⟩ := by native_decide
example : evalDiagFormulaCosted 1000000 0 {} #[("x", 7)]
    (DiagFormula.existsWorld "y" (DiagFormula.eqThing "y" "y")) =
      ⟨true, 24⟩ := by native_decide
example : evalDiagFormulaCosted 1000000 0 {} #[("x", 7)]
    (DiagFormula.box "current" "y" (DiagFormula.eqThing "x" "y")) =
      ⟨false, 24⟩ := by native_decide
example : evalDiagFormulaCosted 1000000 0 {} #[("x", 7)]
    (DiagFormula.dia "current" "y" (DiagFormula.eqThing "y" "y")) =
      ⟨true, 24⟩ := by native_decide

-- The inner quantifier hides the outer x = 7 binding with x = 0.
example : evalDiagFormulaCosted 0 1 {} #[("x", 7)]
    (DiagFormula.existsThing "x" (DiagFormula.eqThing "x" "missing")) =
      ⟨true, 24⟩ := by native_decide

-- Empty-environment equality costs four. Each outer connective adds its own
-- constructor test and evaluates only the operands required by its result.
example : evalDiagFormulaCosted 0 0 {} #[]
    (DiagFormula.not (DiagFormula.eqThing "x" "x")) = ⟨false, 6⟩ := by native_decide
example : evalDiagFormulaCosted 0 0 {} #[]
    (DiagFormula.and (DiagFormula.eqThing "x" "x") (DiagFormula.eqThing "y" "y")) =
      ⟨true, 10⟩ := by native_decide
example : evalDiagFormulaCosted 0 0 {} #[]
    (DiagFormula.or (DiagFormula.eqThing "x" "x") (DiagFormula.eqThing "y" "y")) =
      ⟨true, 6⟩ := by native_decide
example : evalDiagFormulaCosted 0 0 {} #[]
    (DiagFormula.or (DiagFormula.not (DiagFormula.eqThing "x" "x"))
      (DiagFormula.eqThing "y" "y")) = ⟨true, 12⟩ := by native_decide
example : evalDiagFormulaCosted 0 0 {} #[]
    (DiagFormula.imp (DiagFormula.eqThing "x" "x") (DiagFormula.eqThing "y" "y")) =
      ⟨true, 11⟩ := by native_decide
example : evalDiagFormulaCosted 0 0 {} #[]
    (DiagFormula.iff (DiagFormula.not (DiagFormula.eqThing "x" "x"))
      (DiagFormula.eqThing "y" "y")) = ⟨false, 13⟩ := by native_decide

-- Appending an inner binding hides every earlier binding with that name.
example (env : Array (String × Nat)) (name : String) (value : Nat) :
    (lookupVarCosted (env.push (name, value)) name).value = value :=
  lookupVarCosted_push_same env name value

example (env : Array (String × Nat)) (name : String) :
    (lookupVarCosted env name).cost = 4 * env.size + 1 :=
  lookupVarCosted_cost env name

-- A long scan accumulates costs as it goes, without a list copy or a stack
-- of pending cost additions. All bindings must be visited to select the last.
example : lookupVarCosted (Array.replicate 1000000 ("x", 7)) "x" =
    ⟨7, 4000001⟩ := by native_decide

-- Derived assertions stop at the first matching stored string. Duplicates
-- do not alter the result or force the search past that first match.
example : assertedDerivedPropLookupCosted {} "p" = ⟨false, 0⟩ := by native_decide
example : assertedDerivedPropLookupCosted { derivedProps := #["p", "p", "q"] } "p" =
    ⟨true, 4⟩ := by native_decide
example : assertedDerivedPropLookupCosted { derivedProps := #["p", "q", "r"] } "q" =
    ⟨true, 8⟩ := by native_decide
example : assertedDerivedPropLookupCosted { derivedProps := #["p", "q", "r"] } "absent" =
    ⟨false, 12⟩ := by native_decide
example : assertedDerivedPropLookupCosted
    { derivedProps := Array.replicate 1000000 "p" } "absent" =
    ⟨false, 4000000⟩ := by native_decide

-- Both finite loops must also finish when no early exit is available.
example : Complexity.allFinCosted 1000000 (fun _ => .tick true 1) =
    ⟨true, 3000000⟩ := by native_decide
example : Complexity.anyFinCosted 1000000 (fun _ => .tick false 1) =
    ⟨false, 3000000⟩ := by native_decide

example (tables : FactTables) (target : String) :
    (assertedDerivedPropLookupCosted tables target).value =
      tables.derivedProps.any (fun prop => prop == target) :=
  assertedDerivedPropLookupCosted_value tables target

-- Assignment domains return at the first stop test that succeeds. A stopped
-- state does not trigger a visitor or traverse the unused numeric suffix.
example : foldDiagDomainCosted 0 0 0 (fun _ => true)
    (fun state _ => .tick (state + 1) 1) = ⟨0, 0⟩ := by native_decide
example : foldDiagDomainCosted 0 1000000 0 (fun _ => true)
    (fun state _ => .tick (state + 1) 1) = ⟨0, 3⟩ := by native_decide
example : foldDiagDomainCosted 0 1000000 0 (fun state => state == 1)
    (fun state _ => .tick (state + 1) 1) = ⟨1, 7⟩ := by native_decide
example : foldDiagDomainCosted 0 1000000 0 (fun _ => false)
    (fun state _ => .tick (state + 1) 1) = ⟨1000000, 4000000⟩ := by native_decide
example : foldDiagDomainCosted 10 3 (#[] : Array Nat) (fun _ => false)
    (fun state i => .tick (state.push i) 1) = ⟨#[10, 11, 12], 12⟩ := by native_decide
example : foldDiagDomainCosted 0 1000000 (#[] : Array Nat) (fun state => state.size ≥ 2)
    (fun state i => .tick (state.push i) 1) = ⟨#[0, 1], 11⟩ := by native_decide

example (start count : Nat) (state : σ) (stop : σ → Bool)
    (visit : σ → Nat → Complexity.Costed σ) :
    (foldDiagDomainCosted start count state stop visit).value =
      (List.range' start count).foldl
        (fun state i => if stop state then state else (visit state i).value) state :=
  foldDiagDomainCosted_value start count state stop visit

-- World coordinates vary slowest. Truncation preserves the first four
-- assignments of the two-world, three-thing product.
example :
    (foldDiagEnvsUntilCosted 2 3
      #[DiagVar.mk "w" DiagVarKind.world, DiagVar.mk "x" DiagVarKind.thing]
      0 #[] (#[] : Array (Nat × Nat)) (fun out => out.size ≥ 4)
      (fun out env => .tick (out.push (env[0]!.2, env[1]!.2)) 3)).value =
        #[(0, 0), (0, 1), (0, 2), (1, 0)] := by native_decide

-- No variable remains at or beyond the end index. The visitor receives the
-- original environment after four stop/bounds operations.
example : foldDiagEnvsUntilCosted 0 0 #[] 0 #[("x", 7)] 0 (fun _ => false)
    (fun _ env => lookupVarCosted env "x") = ⟨7, 9⟩ := by native_decide
example : foldDiagEnvsUntilCosted 0 0 #[DiagVar.mk "x" DiagVarKind.thing]
    1000000 #[("x", 7)] 0 (fun _ => false)
    (fun _ env => lookupVarCosted env "x") = ⟨7, 9⟩ := by native_decide

-- Neither an already-full budget nor an empty first domain copies the million
-- stored variables. The latter reads just the first variable and its kind.
example : foldDiagEnvsUntilCosted 1 1
    (Array.replicate 1000000 (DiagVar.mk "x" DiagVarKind.thing))
    0 #[] 42 (fun _ => true) (fun state _ => .tick (state + 1) 1) =
      ⟨42, 2⟩ := by native_decide
example : foldDiagEnvsUntilCosted 1 0
    (Array.replicate 1000000 (DiagVar.mk "x" DiagVarKind.thing))
    0 #[] 42 (fun _ => false) (fun state _ => .tick (state + 1) 1) =
      ⟨42, 6⟩ := by native_decide

-- Skipping the first variable preserves the initial world binding. Each of
-- three visits costs 3 for domain control, 2 for descent, 4 for the leaf, and
-- 3 supplied by the visitor: 6 + 3 * 12 = 42.
example : foldDiagEnvsUntilCosted 2 3
    #[DiagVar.mk "ignored" DiagVarKind.world, DiagVar.mk "x" DiagVarKind.thing]
    1 #[("w", 7)] (#[] : Array (Nat × Nat)) (fun _ => false)
    (fun out env => .tick (out.push (env[0]!.2, env[1]!.2)) 3) =
      ⟨#[(7, 0), (7, 1), (7, 2)], 42⟩ := by native_decide

-- One emitted result fills the budget. The next domain check returns without
-- another variable read or visitor call: 6 + 12 + 3 = 21.
example : foldDiagEnvsUntilCosted 0 1000000 #[DiagVar.mk "x" DiagVarKind.thing]
    0 #[] (#[] : Array Nat) (fun out => out.size ≥ 1)
    (fun out env => .tick (out.push env[0]!.2) 3) = ⟨#[0], 21⟩ := by native_decide

-- The inner x shadows the outer x. Both quantified domains retain their order.
example : foldDiagEnvsUntilCosted 0 2
    #[DiagVar.mk "x" DiagVarKind.thing, DiagVar.mk "x" DiagVarKind.thing]
    0 #[] (#[] : Array Nat) (fun _ => false)
    (fun out env => lookupVarCosted env "x" >>= fun x => .tick (out.push x) 1) =
      ⟨#[0, 1, 0, 1], 104⟩ := by native_decide

private def queryAST : ModelAST :=
  { worldCount := 2, thingCount := 2
    facts := #[.unary .mode 1 1, .binary .inst 0 1 0,
      .binary .inst 0 1 0, .ternary .distance 1 0 1 1] }

private def queryTables := compileExplicitModelAST queryAST

private def failingScanEnv : Array (String × Nat) := #[("x", 1), ("w", 1)]
private def failingScanPresent : DiagFormula := DiagFormula.atom (DiagAtom.unary .mode "x" "w")
private def failingScanAbsent : DiagFormula := DiagFormula.atom (DiagAtom.unary .ex "x" "w")

example : suggestionFromAtomsCosted #[`w] #[`a, `b] renderEnv #[] "many" "none" =
    ⟨"none", 2⟩ := by native_decide
example : (suggestionFromAtomsCosted #[`w] #[`a, `b] renderEnv
    #[DiagAtom.unary .moment "x" "w"] "many" "none").cost = 51 := by native_decide
example : suggestionFromAtomsCosted #[`w] #[`a, `b] renderEnv
    #[DiagAtom.typeSem "x" "w", DiagAtom.typeSem "x" "w"] "many" "none" =
    ⟨"many", 5⟩ := by native_decide

-- Conjunction selection includes the complete row expansion. Its predicate
-- scan stops at the first distinctness requirement, before atom discovery.
example : (suggestionForFailureCosted #[`w] #[`a, `b] 1 2 {} renderEnv
    (DiagFormula.and (DiagFormula.not layoutEquality) layoutEquality)).cost = 16 := by native_decide
example : (suggestionForFailureCosted #[`w] #[`a, `b] 1 2 {} renderEnv
    (DiagFormula.and layoutEquality (DiagFormula.not layoutEquality))).cost = 20 := by native_decide
example : (suggestionForFailureCosted #[`w] #[`a, `b] 1 2 {} renderEnv layoutEquality).cost = 5 := by
  native_decide
example : (suggestionForFailureCosted #[`v, `w] #[`a, `b] 2 2 queryTables failingScanEnv
    (DiagFormula.not failingScanPresent)).cost = 72 := by native_decide
example : (suggestionForFailureCosted #[`v, `w] #[`a, `b] 2 2 queryTables failingScanEnv
    (DiagFormula.not failingScanAbsent)).cost = 34 := by native_decide
example : (suggestionForFailureCosted #[`v, `w] #[`a, `b] 2 2 queryTables failingScanEnv
    (DiagFormula.and failingScanPresent failingScanAbsent)).cost = 131 := by native_decide
example : (suggestionForFailureCosted #[`v, `w] #[`a, `b] 2 2 queryTables failingScanEnv
    (DiagFormula.and failingScanAbsent failingScanAbsent)).cost = 94 := by native_decide
example : (suggestionForFailureCosted #[`v, `w] #[`a, `b] 2 2 queryTables failingScanEnv
    (DiagFormula.imp failingScanPresent failingScanAbsent)).cost = 112 := by native_decide
example : (suggestionForFailureCosted #[`v, `w] #[`a, `b] 2 2 queryTables failingScanEnv
    (DiagFormula.forallWorld "w" failingScanPresent)).cost = 137 := by native_decide
example : (suggestionForFailureCosted #[`v, `w] #[`a, `b] 2 2 queryTables failingScanEnv
    (DiagFormula.or failingScanAbsent failingScanAbsent)).cost = 1 := by native_decide

example (worlds things : Array Lean.Name) (W T : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (formula : DiagFormula) :
    (suggestionForFailureCosted worlds things W T tables env formula).value =
      suggestionForFailureSpec worlds things W T tables env formula :=
  suggestionForFailureCosted_value worlds things W T tables env formula
example (worlds things : Array Lean.Name) (W T : Nat) (tables : FactTables) (atomBound : Nat → Nat)
    (hAtom : ∀ (env : Array (String × Nat)) (atom : DiagAtom),
      (evalDiagAtomCosted W T tables env atom).cost ≤ atomBound env.size)
    (env : Array (String × Nat)) (formula : DiagFormula) :
    (suggestionForFailureCosted worlds things W T tables env formula).cost ≤
      DiagFormula.suggestionCostBound W T atomBound env.size formula :=
  suggestionForFailureCosted_cost_le worlds things W T tables atomBound hAtom env formula
example (W T : Nat) (atomBound : Nat → Nat) (hAtom : Monotone atomBound)
    (formula : DiagFormula) (e e' : Nat) (h : e ≤ e') :
    DiagFormula.evalCostBound W T atomBound e formula ≤
      DiagFormula.evalCostBound W T atomBound e' formula :=
  DiagFormula.evalCostBound_mono_env W T atomBound hAtom formula h
example (W T : Nat) (atomBound : Nat → Nat) (hAtom : Monotone atomBound)
    (formula : DiagFormula) (e e' : Nat) (h : e ≤ e') :
    DiagFormula.failingAtomsCostBound W T atomBound e formula ≤
      DiagFormula.failingAtomsCostBound W T atomBound e' formula :=
  DiagFormula.failingAtomsCostBound_mono_env W T atomBound hAtom formula h

-- Each atom evaluation costs 31 here. Discovery adds its node selection,
-- a result branch, and an output write only for a retained atom.
example : (failingAtomsCosted 2 2 queryTables failingScanEnv failingScanPresent).cost = 34 := by native_decide
example : (failingAtomsCosted 2 2 queryTables failingScanEnv failingScanAbsent).cost = 35 := by native_decide
example : (failingAtomsCosted 2 2 queryTables failingScanEnv
    (DiagFormula.and failingScanPresent failingScanAbsent)).cost = 69 := by native_decide
example : (failingAtomsCosted 2 2 queryTables failingScanEnv
    (DiagFormula.or failingScanPresent failingScanAbsent)).cost = 37 := by native_decide
example : (failingAtomsCosted 2 2 queryTables failingScanEnv
    (DiagFormula.or failingScanAbsent failingScanAbsent)).cost = 137 := by native_decide
example : (failingAtomsCosted 2 2 queryTables failingScanEnv
    (DiagFormula.imp failingScanPresent failingScanAbsent)).cost = 106 := by native_decide
example : (failingAtomsCosted 2 2 queryTables failingScanEnv
    (DiagFormula.iff failingScanPresent failingScanAbsent)).cost = 136 := by native_decide
-- A false left operand adds the equivalence evaluator's Boolean negation.
example : (failingAtomsCosted 2 2 queryTables failingScanEnv
    (DiagFormula.iff failingScanAbsent failingScanPresent)).cost = 137 := by native_decide
example : (failingAtomsCosted 2 2 queryTables failingScanEnv
    (DiagFormula.not failingScanPresent)).cost = 39 := by native_decide
example : (failingAtomsCosted 2 2 queryTables failingScanEnv
    (DiagFormula.not failingScanAbsent)).cost = 37 := by native_decide
example : ((failingAtomsCosted 2 2 queryTables failingScanEnv
    (DiagFormula.imp failingScanPresent failingScanAbsent)).value.map
      (renderDiagAtomSpec #[`v, `w] #[`a, `b] failingScanEnv)) =
    #["[w] Mode(b)", "[w] Ex(b)"] := by native_decide
example : (failingAtomsCosted 2 2 queryTables failingScanEnv
    (DiagFormula.or failingScanAbsent failingScanAbsent)).value.size = 2 := by native_decide

-- Quantifier bindings shadow the supplied world binding. Universal discovery
-- scans both worlds. A successful existential stops after its evaluation.
example : (failingAtomsCosted 2 2 queryTables failingScanEnv
    (DiagFormula.forallWorld "w" failingScanPresent)).cost = 93 := by native_decide
example : (failingAtomsCosted 2 2 queryTables failingScanEnv
    (DiagFormula.existsWorld "w" failingScanPresent)).cost = 90 := by native_decide
example : (failingAtomsCosted 2 2 queryTables failingScanEnv
    (DiagFormula.box "w" "w" failingScanPresent)).cost = 136 := by native_decide
example : (failingAtomsCosted 0 0 {} #[]
    (DiagFormula.forallThing "x" failingScanAbsent)).cost = 2 := by native_decide
example : (failingAtomsCosted 0 0 {} #[]
    (DiagFormula.existsThing "x" failingScanAbsent)).cost = 4 := by native_decide
example : (failingAtomsCosted 0 0 {} #[]
    (DiagFormula.dia "w" "v" failingScanAbsent)).cost = 4 := by native_decide

-- The full numeric scan allocates no domain list. Equality nodes contribute
-- no atom: binding, node, and loop work total five operations per assignment.
example : (failingAtomsCosted 0 100000 {} #[]
    (DiagFormula.forallThing "x" (DiagFormula.eqThing "x" "x"))).cost = 500002 := by native_decide
example : (failingAtomsCosted 0 100000 {} #[]
    (DiagFormula.forallThing "x" (DiagFormula.eqThing "x" "x"))).value.size = 0 := by native_decide

example (W T : Nat) (tables : FactTables) (env : Array (String × Nat))
    (out : Array DiagAtom) (formula : DiagFormula) :
    (failingAtomsIntoCosted W T tables env out formula).value =
      failingAtomsIntoSpec W T tables env out formula :=
  failingAtomsIntoCosted_value W T tables env out formula
example (W T : Nat) (tables : FactTables) (atomBound : Nat → Nat)
    (hAtom : ∀ (env : Array (String × Nat)) (atom : DiagAtom),
      (evalDiagAtomCosted W T tables env atom).cost ≤ atomBound env.size)
    (env : Array (String × Nat)) (out : Array DiagAtom) (formula : DiagFormula) :
    (failingAtomsIntoCosted W T tables env out formula).cost ≤
      DiagFormula.failingAtomsCostBound W T atomBound env.size formula :=
  failingAtomsIntoCosted_cost_le W T tables atomBound hAtom env out formula
example (W T : Nat) (tables : FactTables) (env : Array (String × Nat))
    (out : Array DiagAtom) (formula : DiagFormula) :
    (failingAtomsIntoCosted W T tables env out formula).value.size ≤
      out.size + DiagFormula.failingAtomCountBound W T formula :=
  failingAtomsIntoCosted_size_le W T tables env out formula
example (W T : Nat) (tables : FactTables) (env : Array (String × Nat))
    (formula : DiagFormula) :
    (failingAtomsCosted W T tables env formula).value = failingAtomsSpec W T tables env formula :=
  failingAtomsCosted_value W T tables env formula
example (W T : Nat) (tables : FactTables) (atomBound : Nat → Nat)
    (hAtom : ∀ (env : Array (String × Nat)) (atom : DiagAtom),
      (evalDiagAtomCosted W T tables env atom).cost ≤ atomBound env.size)
    (env : Array (String × Nat)) (formula : DiagFormula) :
    (failingAtomsCosted W T tables env formula).cost ≤
      DiagFormula.failingAtomsCostBound W T atomBound env.size formula + 1 :=
  failingAtomsCosted_cost_le W T tables atomBound hAtom env formula

-- Guarded queries include coordinate validation and the dense read itself.
example : Complexity.diagnosticUnaryCosted 2 2 queryTables .mode 1 1 =
    ⟨true, 12⟩ := by native_decide
example : Complexity.diagnosticUnaryCosted 2 2 queryTables .ex 1 1 =
    ⟨false, 12⟩ := by native_decide
example : Complexity.diagnosticBinaryCosted 2 2 queryTables .inst 0 1 0 =
    ⟨true, 17⟩ := by native_decide
example : Complexity.diagnosticTernaryCosted 2 2 queryTables .distance 1 0 1 1 =
    ⟨true, 22⟩ := by native_decide
example : Complexity.diagnosticUnaryCosted 2 2 queryTables .mode 2 0 =
    ⟨false, 2⟩ := by native_decide
example : Complexity.diagnosticUnaryCosted 2 2 queryTables .mode 1 2 =
    ⟨false, 4⟩ := by native_decide
example : Complexity.diagnosticBinaryCosted 2 2 queryTables .inst 0 2 0 =
    ⟨false, 4⟩ := by native_decide
example : Complexity.diagnosticBinaryCosted 2 2 queryTables .inst 0 1 2 =
    ⟨false, 6⟩ := by native_decide
example : Complexity.diagnosticTernaryCosted 2 2 queryTables .distance 1 0 2 1 =
    ⟨false, 6⟩ := by native_decide
example : Complexity.diagnosticTernaryCosted 2 2 queryTables .distance 1 0 1 2 =
    ⟨false, 8⟩ := by native_decide
example : Complexity.diagnosticUnaryCosted 2 2 {} .mode 1 1 =
    ⟨false, 12⟩ := by native_decide

-- The search includes the guarded query and both quantifier loops. Duplicate
-- facts do not add query work after the compiler materializes the dense table.
example : hasPossibleInstanceCosted 2 2 queryTables 1 = ⟨true, 21⟩ := by native_decide
example : hasPossibleInstanceCosted 2 2
    (compileExplicitModelAST { worldCount := 2, thingCount := 2 }) 1 =
      ⟨false, 80⟩ := by native_decide

-- Primitive atom costs include constructor selection, variable resolution,
-- and the guarded query. Binary atoms also inspect their field constructor.
example : evalDiagAtomCosted 2 2 queryTables #[("x", 1), ("w", 1)]
    (DiagAtom.unary .mode "x" "w") = ⟨true, 31⟩ := by native_decide
example : evalDiagAtomCosted 2 2 queryTables #[("x", 0), ("y", 1), ("w", 0)]
    (DiagAtom.binary .inst "x" "y" "w") = ⟨true, 58⟩ := by native_decide
example : evalDiagAtomCosted 2 2 queryTables #[("x", 1), ("y", 0), ("z", 1), ("w", 1)]
    (DiagAtom.ternary .distance "x" "y" "z" "w") = ⟨true, 91⟩ := by native_decide
example : evalDiagAtomCosted 2 2 queryTables #[("t", 1)]
    (DiagAtom.typeSem "t" "unused") = ⟨true, 27⟩ := by native_decide

-- Reflexive part/overlap atoms need no world lookup or relation-table read.
example : evalDiagAtomCosted 2 2 queryTables #[("x", 1)]
    (DiagAtom.binary .part "x" "x" "missing") = ⟨true, 14⟩ := by native_decide
example : evalDiagAtomCosted 2 2 queryTables #[("x", 1)]
    (DiagAtom.binary .overlap "x" "x" "missing") = ⟨true, 14⟩ := by native_decide
example : evalDiagAtomCosted 2 2 queryTables #[("x", 0), ("y", 1), ("w", 0)]
    (DiagAtom.binary .part "x" "y" "w") = ⟨false, 60⟩ := by native_decide

example (ast : ModelAST) (bounded : Complexity.Production.explicitModelWellBounded ast)
    (field : BinaryField) (x y : Fin ast.thingCount) (w : Fin ast.worldCount) :
    (Complexity.diagnosticBinaryCosted ast.worldCount ast.thingCount
      (compileExplicitModelAST ast) field x.val y.val w.val).value =
        (compileExplicitModelAST ast).binaryLookup field.toTableField x.val y.val w.val :=
  Complexity.diagnosticBinaryCosted_compiled ast bounded field x y w

private def modalAST : ModelAST :=
  { worldCount := 3, thingCount := 3
    facts := #[.unary .ex 0 0, .unary .ex 1 0, .unary .ex 1 1,
      .unary .ex 2 0, .unary .ex 2 2, .unary .mode 0 0,
      .binary .inheresIn 0 2 0] }

private def modalTables := compileExplicitModelAST modalAST

-- With no worlds, universal implication is true and existential search is false.
example : boxExImpLookupCosted 0 0 {} 0 0 = ⟨true, 0⟩ := by native_decide
example : existsWithoutLookupCosted 0 0 {} 0 0 = ⟨false, 0⟩ := by native_decide

-- In world zero both things exist (28 operations). In each later world,
-- the absent antecedent skips the second query (16 operations per world).
example : boxExImpLookupCosted 3 3 modalTables 0 1 = ⟨true, 60⟩ := by native_decide
-- Reversing the implication finds its first failure in world one.
example : boxExImpLookupCosted 3 3 modalTables 1 0 = ⟨false, 56⟩ := by native_decide
example : existsWithoutLookupCosted 3 3 modalTables 1 2 = ⟨true, 56⟩ := by native_decide
example : existsWithoutLookupCosted 3 3 modalTables 2 1 = ⟨true, 71⟩ := by native_decide
example : existentialIndependenceLookupCosted 3 3 modalTables 1 2 =
    ⟨true, 131⟩ := by native_decide

-- External dependence checks the modal implication (60), its conjunction (1),
-- two absent inherence edges (21 each), then both separating worlds (149).
example : externallyDependentLookupCosted 3 3 modalTables 0 1 0 =
    ⟨true, 252⟩ := by native_decide
example : externallyDependentModeLookupCosted 3 3 modalTables 0 0 =
    ⟨true, 452⟩ := by native_decide
-- A false mode classification stops before any dependence search.
example : externallyDependentModeLookupCosted 3 3 modalTables 1 0 =
    ⟨false, 13⟩ := by native_decide

private def functionalAST : ModelAST :=
  { worldCount := 1, thingCount := 2
    facts := #[.binary .inst 0 0 0, .binary .functionsAs 0 0 0,
      .binary .inst 1 1 0, .binary .functionsAs 1 1 0,
      .binary .properPart 0 1 0, .binary .constitutedBy 0 1 0,
      .binary .quaIndividualOf 0 1 0] }

private def functionalTables := compileExplicitModelAST functionalAST

-- Functional dependence excludes candidate zero before finding candidate one.
-- Source zero costs 35 + 2 + (4 + 39) + 2 = 82. Source one costs 22.
example : genericFunctionalDependenceLookupCosted 1 2 functionalTables 0 1 0 =
    ⟨true, 104⟩ := by native_decide
-- A source cannot witness its own distinct-target requirement.
example : genericFunctionalDependenceLookupCosted 1 2 functionalTables 0 0 0 =
    ⟨false, 65⟩ := by native_decide
-- Constitutional dependence permits the source coordinate as a candidate.
-- Its two source checks cost 17 + 2 + (20 + 37) + 2 = 78 and 21.
example : genericConstitutionalDependenceLookupCosted 1 2 functionalTables 0 1 0 =
    ⟨true, 99⟩ := by native_decide
example : individualFunctionalDependenceLookupCosted 1 2 functionalTables 0 0 1 1 0 =
    ⟨true, 177⟩ := by native_decide
example : componentOfLookupCosted 1 2 functionalTables 0 0 1 1 0 =
    ⟨true, 195⟩ := by native_decide
example : constitutionLookupCosted 1 2 functionalTables 0 0 1 1 0 =
    ⟨true, 153⟩ := by native_decide
example : quaIndividualLookupCosted 1 2 functionalTables 0 0 =
    ⟨true, 38⟩ := by native_decide
example : quaIndividualLookupCosted 1 2 functionalTables 1 0 =
    ⟨false, 38⟩ := by native_decide

-- A missing leading fact skips all nested dependence searches.
example : componentOfLookupCosted 1 2 functionalTables 1 1 0 0 0 =
    ⟨false, 18⟩ := by native_decide
example : constitutionLookupCosted 1 2 functionalTables 0 1 1 1 0 =
    ⟨false, 18⟩ := by native_decide
example : genericFunctionalDependenceLookupCosted 1 0 {} 0 0 0 =
    ⟨true, 0⟩ := by native_decide
example : genericConstitutionalDependenceLookupCosted 1 0 {} 0 0 0 =
    ⟨true, 0⟩ := by native_decide
example : quaIndividualLookupCosted 1 0 {} 0 0 =
    ⟨false, 0⟩ := by native_decide

-- Dispatch visits two unary names or five binary names at most. Each name
-- adds one comparison and one branch to the selected predicate's exact cost.
example : derivedUnaryLookupCosted 3 3 modalTables "ExternallyDependentMode" 0 0 =
    ⟨true, 454⟩ := by native_decide
example : derivedUnaryLookupCosted 1 2 functionalTables "QuaIndividual" 0 0 =
    ⟨true, 42⟩ := by native_decide
example : derivedBinaryLookupCosted 3 3 modalTables "ExistentialDependence" 0 1 0 =
    ⟨true, 62⟩ := by native_decide
example : derivedBinaryLookupCosted 3 3 modalTables "ExistentialIndependence" 1 2 0 =
    ⟨true, 135⟩ := by native_decide
example : derivedBinaryLookupCosted 3 3 modalTables "ExternallyDependent" 0 1 0 =
    ⟨true, 258⟩ := by native_decide
example : derivedBinaryLookupCosted 1 2 functionalTables "GenericFunctionalDependence" 0 1 0 =
    ⟨true, 112⟩ := by native_decide
example : derivedBinaryLookupCosted 1 2 functionalTables "GenericConstitutionalDependence" 0 1 0 =
    ⟨true, 109⟩ := by native_decide

-- Unknown names build the assertion key after the final comparison. Unary
-- keys cost 11 and binary keys cost 16 before the assertion scan starts.
example : derivedUnaryLookupCosted 0 0 {} "Custom" 0 0 =
    ⟨false, 15⟩ := by native_decide
example : derivedBinaryLookupCosted 0 0 {} "Custom" 0 0 0 =
    ⟨false, 26⟩ := by native_decide
example : derivedUnaryLookupCosted 0 0
    { derivedProps := #[s!"sig.Custom {diagFinThingTerm 0} {diagFinWorldTerm 0}"] }
    "Custom" 0 0 = ⟨true, 19⟩ := by native_decide
example : derivedBinaryLookupCosted 0 0
    { derivedProps := #[s!"sig.Custom {diagFinThingTerm 0} {diagFinThingTerm 1} {diagFinWorldTerm 0}"] }
    "Custom" 0 1 0 = ⟨true, 30⟩ := by native_decide

-- Case changes use the fallback. An assertion cannot override a recognized
-- computed predicate, even if its text matches that predicate's application.
example : derivedUnaryLookupCosted 0 0
    { derivedProps := #[s!"sig.quaIndividual {diagFinThingTerm 0} {diagFinWorldTerm 0}"] }
    "quaIndividual" 0 0 = ⟨true, 19⟩ := by native_decide
example : derivedUnaryLookupCosted 0 0
    { derivedProps := #[s!"sig.QuaIndividual {diagFinThingTerm 0} {diagFinWorldTerm 0}"] }
    "QuaIndividual" 0 0 = ⟨false, 4⟩ := by native_decide

-- Each coordinate makes one decimal-format call and two concatenations.
-- These primitive counts do not measure the characters processed by each call.
example : diagFinThingTermCosted 0 =
    ⟨"(⟨0, by decide⟩ : Fin data.thingCount)", 3⟩ := by native_decide
example : diagFinThingTermCosted 123456 =
    ⟨"(⟨123456, by decide⟩ : Fin data.thingCount)", 3⟩ := by native_decide
example : diagFinWorldTermCosted 42 =
    ⟨"(⟨42, by decide⟩ : Fin data.worldCount)", 3⟩ := by native_decide
example : appendDiagTermCosted "sig.Custom" (diagFinThingTermCosted 12) =
    ⟨"sig.Custom (⟨12, by decide⟩ : Fin data.thingCount)", 5⟩ := by native_decide

-- Literal expected keys independently fix spacing, Unicode, and multi-digit
-- coordinate formatting. Empty field names are not normalized by lookup.
example : derivedUnaryLookupCosted 0 0
    { derivedProps := #["sig. (⟨12, by decide⟩ : Fin data.thingCount) (⟨34, by decide⟩ : Fin data.worldCount)"] }
    "" 12 34 = ⟨true, 19⟩ := by native_decide
example : derivedBinaryLookupCosted 0 0
    { derivedProps := #["sig.α (⟨12, by decide⟩ : Fin data.thingCount) (⟨34, by decide⟩ : Fin data.thingCount) (⟨56, by decide⟩ : Fin data.worldCount)"] }
    "α" 12 34 56 = ⟨true, 30⟩ := by native_decide

-- Five environment lookups cost 5 * 21. The four-thing, one-world key adds
-- 1 + 5 * 5 = 26, and the first matching assertion adds four: total 135.
example : evalDiagAtomCosted 0 0
    { derivedProps := #["sig.Custom (⟨12, by decide⟩ : Fin data.thingCount) (⟨34, by decide⟩ : Fin data.thingCount) (⟨56, by decide⟩ : Fin data.thingCount) (⟨78, by decide⟩ : Fin data.thingCount) (⟨90, by decide⟩ : Fin data.worldCount)"] }
    #[("a", 12), ("b", 34), ("c", 56), ("d", 78), ("w", 90)]
    (DiagAtom.quaternary "Custom" "a" "b" "c" "d" "w") =
      ⟨true, 136⟩ := by native_decide
example : evalDiagAtomCosted 0 0 {} #[]
    (DiagAtom.quaternary "Custom" "a" "b" "c" "d" "w") =
      ⟨false, 32⟩ := by native_decide

-- The collector checks candidates 0, 1, and 2, preserving the sole successful
-- witness. Their predicate costs are 183, 252, and 196. Control and pushes add
-- 4, 5, and 4 respectively. Array initialization adds one, totaling 645.
example : externallyDependentWitnessesCosted #[`actual, `yOnly, `zOnly]
    #[`x, `y, `z] modalTables 0 0 = ⟨#[1], 645⟩ := by native_decide
example : externallyDependentWitnessesCosted #[`actual] #[]
    (compileExplicitModelAST { worldCount := 1, thingCount := 0 }) 0 0 =
      ⟨#[], 1⟩ := by native_decide

-- With no existence or inherence facts, each dependence check is vacuously
-- true. All four candidates are emitted once, in ascending order.
example : externallyDependentWitnessesCosted #[`actual] #[`a, `b, `c, `d]
    (compileExplicitModelAST { worldCount := 1, thingCount := 4 }) 0 0 =
      ⟨#[0, 1, 2, 3], 425⟩ := by native_decide

private def declaredTables : FactTables :=
  { derivedProps := #[
      "sig.ExternallyDependent (⟨0, by decide⟩ : Fin data.thingCount) (⟨2, by decide⟩ : Fin data.thingCount) (⟨0, by decide⟩ : Fin data.worldCount)",
      "sig.ExternallyDependent (⟨0, by decide⟩ : Fin data.thingCount) (⟨0, by decide⟩ : Fin data.thingCount) (⟨0, by decide⟩ : Fin data.worldCount)",
      "sig.ExternallyDependent (⟨0, by decide⟩ : Fin data.thingCount) (⟨2, by decide⟩ : Fin data.thingCount) (⟨0, by decide⟩ : Fin data.worldCount)",
      "unrelated assertion"] }

-- Each key costs 16 before the source-ordered assertion scan. The first
-- matching duplicate ends the scan, and world coordinates remain significant.
example : assertedDerivedBinaryLookupCosted declaredTables "ExternallyDependent" 0 2 0 =
    ⟨true, 20⟩ := by native_decide
example : assertedDerivedBinaryLookupCosted declaredTables "ExternallyDependent" 0 0 0 =
    ⟨true, 24⟩ := by native_decide
example : assertedDerivedBinaryLookupCosted declaredTables "ExternallyDependent" 0 2 1 =
    ⟨false, 32⟩ := by native_decide

-- Candidate order follows coordinates, not assertion order. Candidate costs
-- are 24 + 5, 32 + 4, and 20 + 5, plus one for initialization, totaling 91.
-- Duplicates emit no extra item.
example : declaredExternalCandidatesCosted 3 declaredTables 0 0 =
    ⟨#[0, 2], 91⟩ := by native_decide
example : declaredExternalCandidatesCosted 0 declaredTables 0 0 =
    ⟨#[], 1⟩ := by native_decide
example : declaredExternalCandidatesCosted 3 {} 0 0 =
    ⟨#[], 61⟩ := by native_decide

-- This primitive name cannot be inserted by any explicit AST. The proof
-- covers arbitrary facts and product families, without a coordinate premise.
example (ast : ModelAST) (x y w : Nat) :
    (compileExplicitModelAST ast).binaryLookup "externallyDependent" x y w = false :=
  Complexity.Production.compileExplicitModelAST_binaryLookup_unknown ast "externallyDependent"
    (by intro field; cases field <;> decide) x y w

-- A declared candidate wins before any relation query, including on an empty
-- domain. Otherwise three guarded reads, result branches, and loop steps cost
-- 3 * 21. The outer branch and successful selection add three operations.
example : firstModeStatusCandidateCosted 3 3 modalTables 0 0 #[1, 2] =
    ⟨some 1, 3⟩ := by native_decide
example : firstModeStatusCandidateCosted 0 0 {} 0 0 #[7] =
    ⟨some 7, 3⟩ := by native_decide
example : firstModeStatusCandidateCosted 3 3 modalTables 0 0 #[] =
    ⟨some 2, 66⟩ := by native_decide

-- Without a match, selection falls back to zero only for a nonempty domain.
-- The scan still checks every candidate. An empty scan costs only five.
example : firstModeStatusCandidateCosted 1 3
    (compileExplicitModelAST { worldCount := 1, thingCount := 3 }) 0 0 #[] =
      ⟨some 0, 68⟩ := by native_decide
example : firstModeStatusCandidateCosted 1 0 {} 0 0 #[] =
    ⟨none, 5⟩ := by native_decide

-- Two matches select coordinate zero. The next iteration detects the stopped
-- state (three operations), so no query is made at coordinate one or two.
example : firstModeStatusCandidateCosted 1 3
    (compileExplicitModelAST
      { worldCount := 1, thingCount := 3
        facts := #[.binary .inheresIn 0 2 0, .binary .inheresIn 0 0 0] }) 0 0 #[] =
      ⟨some 0, 27⟩ := by native_decide

-- Sparse/dense agreement is an explicit premise of the general value proof.
example (W T : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (x : Fin T) (w : Fin W) (declared : Array Nat) :
    (firstModeStatusCandidateCosted W T tables x.val w.val declared).value =
      if h : 0 < declared.size then some declared[0] else
        ((List.range T).find? (fun z => tables.binaryLookup "inheresIn" x.val z w.val)).orElse
          (fun _ => if T == 0 then none else some 0) :=
  firstModeStatusCandidateCosted_sparse_value W T tables agreement x w declared

-- First-witness search shares the indexed loop's empty and stopped behavior.
-- A visited predicate adds one result branch and three loop operations.
example : findDiagDomainCosted 0 (fun _ => .tick true 7) =
    ⟨none, 0⟩ := by native_decide
example : findDiagDomainCosted 1000000 (fun _ => .tick true 7) =
    ⟨some 0, 14⟩ := by native_decide
example : findDiagDomainCosted 1000000 (fun _ => .tick false 1) =
    ⟨none, 5000000⟩ := by native_decide

-- At world zero both things exist: two guarded reads (24), conjunction and
-- negation (2), and search control (4). World one is a witness. The following
-- stop test adds three, without looking up existence at world two.
example : firstExWithoutCosted 3 3 modalTables 1 2 =
    ⟨some 1, 63⟩ := by native_decide
-- Reversing the arguments skips the second lookup in world one, then finds
-- the witness at world two: 30 + 17 + 30, with no remaining iteration.
example : firstExWithoutCosted 3 3 modalTables 2 1 =
    ⟨some 2, 77⟩ := by native_decide
example : firstExWithoutCosted 3 3 modalTables 0 1 =
    ⟨none, 64⟩ := by native_decide
example : firstExWithoutCosted 0 0 {} 0 0 =
    ⟨none, 0⟩ := by native_decide

-- An invalid first coordinate stops at its guard in every world. The second
-- coordinate is never queried. Each visit costs 2 + 1 + 4 = 7.
example : firstExWithoutCosted 3 3 modalTables 3 1 =
    ⟨none, 21⟩ := by native_decide
example (W T : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (x y : Fin T) :
    (firstExWithoutCosted W T tables x.val y.val).value =
      (List.range W).find? (fun w =>
        tables.unaryLookup "ex" x.val w && !tables.unaryLookup "ex" y.val w) :=
  firstExWithoutCosted_sparse_value W T tables agreement x y

-- Name rendering counts the guard and either read/render or numeric fallback.
-- The fallback also fixes behavior for malformed coordinates in diagnostics.
example : indexedNameCosted #[`A.B, `«α β»] 0 = ⟨"A.B", 4⟩ := by native_decide
example : indexedNameCosted #[`A.B] 17 = ⟨"#17", 4⟩ := by native_decide
example (names : Array Lean.Name) (i : Nat) :
    (indexedNameCosted names i).value = indexedName names i := indexedNameCosted_value names i
example (names : Array Lean.Name) (i : Nat) :
    (indexedNameCosted names i).cost = 4 := indexedNameCosted_cost names i

-- Both searches run. With both witnesses present, only the two result tests
-- are added: 63 + 77 + 2. Failure adds two name renders and four or eight
-- concatenations, depending on whether one or both directions lack a witness.
example : firstExternalIndependenceFailureCosted #[`actual, `yOnly, `zOnly]
    #[`x, `y, `z] modalTables 1 2 = ⟨none, 142⟩ := by native_decide
example : firstExternalIndependenceFailureCosted #[`actual, `yOnly, `zOnly]
    #[`x, `y, `z] modalTables 0 1 =
      ⟨some "the assertion needs a witness world where Ex(x) holds without Ex(y), but no such world exists in the current `Ex` facts", 141⟩ := by native_decide
example : firstExternalIndependenceFailureCosted #[`actual, `yOnly, `zOnly]
    #[`x, `y, `z] modalTables 1 0 =
      ⟨some "the assertion needs a witness world where Ex(x) holds without Ex(y), but no such world exists in the current `Ex` facts", 141⟩ := by native_decide
example : firstExternalIndependenceFailureCosted #[`actual, `yOnly, `zOnly]
    #[`x, `y, `z] modalTables 0 0 =
      ⟨some "the assertion needs one witness world where Ex(x) holds without Ex(x), and one witness world where Ex(x) holds without Ex(x); neither witness exists in the current `Ex` facts", 146⟩ := by native_decide

-- No bearer triggers an independence search when inherence is absent.
example : firstExternalBearerFailureCosted #[`actual] #[`x, `y, `z]
    (compileExplicitModelAST { worldCount := 1, thingCount := 3 }) 0 1 0 =
      ⟨"no concrete missing `Ex` witness was isolated; inspect the `Ex` and `InheresIn` facts used by external dependence.", 64⟩ := by native_decide
example : firstExternalBearerFailureCosted #[] #[] {} 0 0 0 =
    ⟨"no concrete missing `Ex` witness was isolated; inspect the `Ex` and `InheresIn` facts used by external dependence.", 1⟩ := by native_decide
example : firstExternalBearerFailureCosted #[`actual, `yOnly, `zOnly]
    #[`x, `y, `z] modalTables 0 1 0 =
      ⟨"no concrete missing `Ex` witness was isolated; inspect the `Ex` and `InheresIn` facts used by external dependence.", 207⟩ := by native_decide
example : firstExternalBearerFailureCosted #[`actual, `yOnly, `zOnly]
    #[`x, `y, `z] modalTables 0 2 0 =
      ⟨"`x` inheres in `z` at `actual`, but `z` is not existentially independent from that bearer: the assertion needs one witness world where Ex(z) holds without Ex(z), and one witness world where Ex(z) holds without Ex(z); neither witness exists in the current `Ex` facts.", 263⟩ := by native_decide

-- The later-written edge to coordinate zero wins over the edge to two.
-- Its reason is retained by the search. The next stop test adds three to
-- 17 (query) + 1 (branch) + 146 (reason) + 1 (pair selection) + 3 (loop).
private def multipleBearerTables := compileExplicitModelAST
  { modalAST with facts := modalAST.facts.push (.binary .inheresIn 0 0 0) }
example : (firstExternalBearerWitnessCosted #[`actual, `yOnly, `zOnly]
    #[`x, `y, `z] multipleBearerTables 0 0 0).value.map Prod.fst = some 0 := by native_decide
example : (firstExternalBearerWitnessCosted #[`actual, `yOnly, `zOnly]
    #[`x, `y, `z] multipleBearerTables 0 0 0).cost = 171 := by native_decide
example : (firstExternalBearerFailureCosted #[`actual, `yOnly, `zOnly]
    #[`x, `y, `z] multipleBearerTables 0 0 0).cost = 198 := by native_decide

-- A modal witness takes precedence over bearer search: 63 search operations,
-- three name renders, six concatenations, and one result test total 82.
example : firstExternallyDependentFailureReasonCosted #[`actual, `yOnly, `zOnly]
    #[`x, `y, `z] modalTables 1 0 0 =
      ⟨"`y` exists at `yOnly`, but `x` does not; this breaks existential dependence.", 82⟩ := by native_decide
example : firstExternallyDependentFailureReasonCosted #[] #[] {} 0 0 0 =
    ⟨"no concrete missing `Ex` witness was isolated; inspect the `Ex` and `InheresIn` facts used by external dependence.", 2⟩ := by native_decide

-- Joining reads indices directly, preserves repeats, and uses the numeric
-- fallback for missing names. Costs are 7 for the first item, 9 thereafter,
-- and one final selection. No temporary list of rendered names is built.
example : joinIndexedNamesCosted #[`a, `b] #[] = ⟨"", 1⟩ := by native_decide
example : joinIndexedNamesCosted #[`a, `b] #[1] = ⟨"b", 8⟩ := by native_decide
example : joinIndexedNamesCosted #[`a, `b] #[1, 0, 1, 99] =
    ⟨"b, a, b, #99", 35⟩ := by native_decide
example (names : Array Lean.Name) (indices : Array Nat) :
    (joinIndexedNamesCosted names indices).value =
      String.intercalate ", " (indices.toList.map (indexedName names)) :=
  joinIndexedNamesCosted_value names indices

-- The non-mode path skips all candidate searches: guarded query 12, negation
-- and branch 2, names 8, concatenations 4, empty-array initialization 1,
-- and the emitted row/push 2, totaling 29.
example : renderExternallyDependentModeStatusCosted #[`actual, `yOnly, `zOnly]
    #[`x, `y, `z] modalTables 1 0 =
      ⟨#["  - Computed ExternallyDependentMode: false, because `y` is not a `Mode` at `actual`."], 29⟩ := by native_decide
-- The witness collector costs 645, and joining its one witness costs 8.
-- Mode/empty tests and row construction add another 21 operations.
example : renderExternallyDependentModeStatusCosted #[`actual, `yOnly, `zOnly]
    #[`x, `y, `z] modalTables 0 0 =
      ⟨#["  - Computed ExternallyDependentMode: true, witnessed by y."], 674⟩ := by native_decide

-- Failure rows reuse the computed reason. The optional note preserves the
-- supplied candidate order. Two rows cost 16; the note adds 17 for joining
-- two names, two concatenations, and an emitted-row push, totaling 37.
example : renderModeFailureRowsCosted #[`x, `y, `z] 0 "missing witness" #[] =
    ⟨#["  - Computed ExternallyDependentMode: false. `x` is a `Mode`, but no thing witnesses computed `ExternallyDependent(x, y)`.",
      "  - First candidate check: missing witness"], 16⟩ := by native_decide
example : renderModeFailureRowsCosted #[`x, `y, `z] 0 "missing witness" #[2, 0] =
    ⟨#["  - Computed ExternallyDependentMode: false. `x` is a `Mode`, but no thing witnesses computed `ExternallyDependent(x, y)`.",
      "  - First candidate check: missing witness",
      "  - Note: asserted `ExternallyDependent` facts name candidate(s) z, x, but certification uses the computed external-dependence semantics."], 37⟩ := by native_decide

private def foundedTables := compileExplicitModelAST
  { worldCount := 2, thingCount := 2
    facts := #[.binary .foundedBy 0 1 1, .binary .foundedBy 1 0 0,
      .unary .perdurant 0 0] }

-- Absent FoundedBy needs only its guarded read (17) and branch (1).
-- A founded non-mode also tests Relator and Perdurant: 18+13+13+12+3=59.
example : ax71AssignmentCosted 2 2 foundedTables 0 0 0 =
    ⟨none, 18⟩ := by native_decide
example : ax71AssignmentCosted 2 2 foundedTables 1 0 0 =
    ⟨some (false, true), 59⟩ := by native_decide
example : ax71AssignmentCosted 1 1
    (compileExplicitModelAST
      { worldCount := 1, thingCount := 1
        facts := #[.binary .foundedBy 0 0 0, .unary .relator 0 0,
          .unary .perdurant 0 0] }) 0 0 0 = ⟨none, 59⟩ := by native_decide
example : ax71AssignmentsCosted 0 1000000 {} = ⟨none, 0⟩ := by native_decide
example : ax71AssignmentsCosted 1 0 {} = ⟨none, 3⟩ := by native_decide
-- Four absent pairs cost 4*(18+1+3), plus two left-thing visits and one world.
example : ax71AssignmentsCosted 1 2 {} = ⟨none, 97⟩ := by native_decide
-- Coordinate order, not fact insertion order, selects the failure in world 0.
-- The search visits the empty x=0 row, then stops at y=0 in the x=1 row.
example : ax71AssignmentsCosted 2 2 foundedTables =
    ⟨some (0, 1, 0, false, true), 122⟩ := by native_decide

private def foundedModalTables := compileExplicitModelAST
  { modalAST with facts := modalAST.facts.push (.binary .foundedBy 0 0 0) }

-- Computed mode is true in 452 operations. Classification adds one branch
-- and skips the Relator read: 17+1+452+1+12+3=486.
example : ax71AssignmentCosted 3 3 foundedModalTables 0 0 0 =
    ⟨some (true, false), 486⟩ := by native_decide
-- Mapping the failure costs one. Each of the three loops has one visit and
-- one early-stop check, adding 18; no later assignment is evaluated.
example : ax71AssignmentsCosted 3 3 foundedModalTables =
    ⟨some (0, 0, 0, true, false), 505⟩ := by native_decide

example : ax71FoundationAnalysisCosted #[] #[`x] {} =
    ⟨#["Foundation check for ax71: every `FoundedBy` fact has a computed externally dependent mode or relator on the left and a perdurant on the right."], 4⟩ := by native_decide
example : (ax71FoundationAnalysisCosted #[`first, `second] #[`x, `y]
    foundedTables).cost = 214 := by native_decide
example : (ax71FoundationAnalysisCosted #[`actual, `yOnly, `zOnly] #[`x, `y, `z]
    foundedModalTables).cost = 1244 := by native_decide

-- The six new rows cost 49; copying the two already emitted mode rows adds 6.
example : ax71FailureRowsCosted #[`actual] #[`x, `y] 0 0 1 true true false
    #["mode row one", "mode row two"] =
      ⟨#["Counterexample assignment: x = x, y = y, w = actual.",
        "Triggered by: `FoundedBy(x, y)`.",
        "Required together: the founded thing must be a computed `ExternallyDependentMode` or a `Relator`, and the foundation must be a `Perdurant`.",
        "  - Relator(x): true.", "  - Perdurant(y): false.",
        "mode row one", "mode row two",
        "Suggestion: classify `y` as `Perdurant`, or change the `FoundedBy` target to a perdurant foundation."], 55⟩ := by native_decide
-- Missing names retain the #n fallback. The classification suggestion is
-- constant text, so this branch saves the other suggestion's two concatenations.
example : ax71FailureRowsCosted #[] #[] 4 2 3 false false true #[] =
    ⟨#["Counterexample assignment: x = #2, y = #3, w = #4.",
      "Triggered by: `FoundedBy(#2, #3)`.",
      "Required together: the founded thing must be a computed `ExternallyDependentMode` or a `Relator`, and the foundation must be a `Perdurant`.",
      "  - Relator(#2): false.", "  - Perdurant(#3): true.",
      "Suggestion: add the modal `Ex` variation and `InheresIn` facts needed for computed external dependence, or remove/relax the `FoundedBy` fact if this thing is not a relator or externally dependent mode."], 47⟩ := by native_decide

private def foundationAST : ModelAST :=
  { worldCount := 2, thingCount := 3
    facts := #[.binary .part 1 0 1, .binary .foundedBy 0 2 0,
      .binary .foundedBy 1 2 0, .binary .foundedBy 0 0 0,
      .binary .foundedBy 1 2 0] }

private def foundationTables := compileExplicitModelAST foundationAST

-- Initialization costs one. Each target costs 21 operations when absent,
-- or 22 when its coordinate is pushed. Fact order does not set output order.
example : foundationCandidatesCosted 2 3 foundationTables 0 0 =
    ⟨#[0, 2], 66⟩ := by native_decide
example : foundationCandidatesCosted 2 3 foundationTables 1 0 =
    ⟨#[2], 65⟩ := by native_decide
example : foundationCandidatesCosted 2 3 foundationTables 2 0 =
    ⟨#[], 64⟩ := by native_decide
example : foundationCandidatesCosted 2 3 foundationTables 0 1 =
    ⟨#[], 64⟩ := by native_decide
example : foundationCandidatesCosted 0 0 {} 999 999 = ⟨#[], 1⟩ := by native_decide
example : foundationCandidatesCosted 2 3 foundationTables 3 0 =
    ⟨#[], 19⟩ := by native_decide
example : foundationCandidatesCosted 2 3 foundationTables 0 2 =
    ⟨#[], 31⟩ := by native_decide
example : foundationCandidatesCosted 1 1000000 {} 0 0 =
    ⟨#[], 21000001⟩ := by native_decide

example (W T : Nat) (tables : FactTables) (x w : Nat) :
    (foundationCandidatesCosted W T tables x w).value.toList.Nodup :=
  foundationCandidatesCosted_nodup W T tables x w

example (W T : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (x : Fin T) (w : Fin W) :
    (uniqueFoundationCosted W T tables x.val w.val).value =
      match (List.range T).filter (fun y => tables.binaryLookup "foundedBy" x.val y w.val) with
      | [y] => some y
      | _ => none := uniqueFoundationCosted_sparse_value W T tables agreement x w

example : uniqueFoundationCosted 2 3 foundationTables 0 0 = ⟨none, 68⟩ := by native_decide
example : uniqueFoundationCosted 2 3 foundationTables 1 0 = ⟨some 2, 68⟩ := by native_decide
example : uniqueFoundationCosted 2 3 foundationTables 2 0 = ⟨none, 66⟩ := by native_decide
example : uniqueFoundationCosted 0 0 {} 0 0 = ⟨none, 3⟩ := by native_decide

-- Both searches run, but only visited option branches count. A missing left
-- result skips the right option test, even though its search already ran.
example : foundationEqCosted 2 3 foundationTables 0 1 0 = ⟨none, 137⟩ := by native_decide
example : foundationEqCosted 2 3 foundationTables 1 0 0 = ⟨none, 138⟩ := by native_decide
example : foundationEqCosted 2 3 foundationTables 1 1 0 = ⟨some true, 139⟩ := by native_decide
example : foundationEqCosted 0 0 {} 0 0 0 = ⟨none, 7⟩ := by native_decide

private def distinctFoundationTables := compileExplicitModelAST
  { foundationAST with facts := foundationAST.facts.push (.binary .foundedBy 2 1 0) }
example : foundationEqCosted 2 3 distinctFoundationTables 1 2 0 =
    ⟨some false, 139⟩ := by native_decide

-- The ambiguity renderer preserves repeated supplied indices and uses the
-- indexed-name fallback. The collector separately proves duplicate freedom.
example : renderAmbiguousFoundationsCosted #[] #[] =
    ⟨"ambiguous foundations ", 2⟩ := by native_decide
example : renderAmbiguousFoundationsCosted #[`a] #[0] =
    ⟨"ambiguous foundations `a`", 11⟩ := by native_decide
example : renderAmbiguousFoundationsCosted #[`a] #[0, 3, 0] =
    ⟨"ambiguous foundations `a`; `#3`; `a`", 33⟩ := by native_decide
example (names : Array Lean.Name) (indices : Array Nat) :
    (renderAmbiguousFoundationsCosted names indices).value =
      "ambiguous foundations " ++ String.intercalate "; "
        (indices.toList.map (fun i => "`" ++ indexedName names i ++ "`")) :=
  renderAmbiguousFoundationsCosted_value names indices

example : renderFoundationStatusCosted 2 #[`a, `b, `c] foundationTables 0 0 =
    ⟨"ambiguous foundations `a`; `c`", 92⟩ := by native_decide
example : renderFoundationStatusCosted 2 #[`a, `b, `c] foundationTables 1 0 =
    ⟨"foundation `c`", 76⟩ := by native_decide
example : renderFoundationStatusCosted 2 #[`a, `b, `c] foundationTables 2 0 =
    ⟨"no `FoundedBy` fact", 66⟩ := by native_decide
example : renderFoundationStatusCosted 0 #[] {} 0 0 =
    ⟨"no `FoundedBy` fact", 3⟩ := by native_decide

-- The four proved upper bounds grow with T, even when exact counts decrease.
example (T T' : Nat) (h : T ≤ T') :
    22 * T + 1 ≤ 22 * T' + 1 ∧ 22 * T + 4 ≤ 22 * T' + 4 ∧
    44 * T + 11 ≤ 44 * T' + 11 ∧ 33 * T + 12 ≤ 33 * T' + 12 := by omega

-- Reflexivity costs the equality test and branch, without a table read.
example : partLookupCosted 0 0 {} 999 999 999 = ⟨true, 2⟩ := by native_decide
example : partLookupCosted 2 3 foundationTables 1 0 1 = ⟨true, 19⟩ := by native_decide
example : partLookupCosted 2 3 foundationTables 0 1 1 = ⟨false, 19⟩ := by native_decide
example : partLookupCosted 2 3 foundationTables 0 1 2 = ⟨false, 8⟩ := by native_decide
example : partLookupCosted 2 3 foundationTables 3 0 1 = ⟨false, 4⟩ := by native_decide

-- A visited target costs 20 when the first FoundedBy query is false, and
-- 37 when both queries run. Duplicate facts do not duplicate target visits.
example : sameFoundationLookupCosted 2 3 foundationTables 0 1 0 =
    ⟨true, 94⟩ := by native_decide
example : sameFoundationLookupCosted 2 3 foundationTables 1 0 0 =
    ⟨true, 77⟩ := by native_decide
example : sameFoundationLookupCosted 2 3 foundationTables 0 0 0 =
    ⟨true, 37⟩ := by native_decide
example : sameFoundationLookupCosted 2 3 foundationTables 0 1 1 =
    ⟨false, 60⟩ := by native_decide
example : sameFoundationLookupCosted 1 0 {} 0 0 0 = ⟨false, 0⟩ := by native_decide
example : sameFoundationLookupCosted 1 1000000 {} 0 1 0 =
    ⟨false, 20000000⟩ := by native_decide

private def ambiguousFoundationTables := compileExplicitModelAST
  { foundationAST with facts := foundationAST.facts.push (.binary .foundedBy 1 0 0) }

-- Both things have two foundations. They share a target, but the separate
-- comparison of unique foundations is undefined. These tests must not agree.
example : sameFoundationLookupCosted 2 3 ambiguousFoundationTables 0 1 0 =
    ⟨true, 37⟩ := by native_decide
example : (foundationEqCosted 2 3 ambiguousFoundationTables 0 1 0).value = none := by native_decide

example (W T : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (x y : Fin T) (w : Fin W) :
    (sameFoundationLookupCosted W T tables x.val y.val w.val).value = true ↔
      ∃ foundation : Fin T,
        tables.binaryLookup "foundedBy" x.val foundation.val w.val = true ∧
          tables.binaryLookup "foundedBy" y.val foundation.val w.val = true :=
  sameFoundationLookupCosted_iff W T tables agreement x y w

private def characterizedAST : ModelAST :=
  { modalAST with facts := modalAST.facts ++
      #[.binary .foundedBy 0 1 0, .binary .foundedBy 1 1 0] }

private def characterizedTables := compileExplicitModelAST characterizedAST

-- A false computed-mode test costs 13, followed by one branch. Inherence
-- failure costs 452+1+17+1, without a foundation scan. The successful case
-- adds a 57-operation shared-target search. No string dispatch is needed.
example : ax73CharacterizedCosted 3 3 modalTables 1 0 999 0 =
    ⟨false, 14⟩ := by native_decide
example : ax73CharacterizedCosted 3 3 modalTables 0 1 1 0 =
    ⟨false, 471⟩ := by native_decide
example : ax73CharacterizedCosted 3 3 modalTables 0 1 2 0 =
    ⟨false, 531⟩ := by native_decide
example : ax73CharacterizedCosted 3 3 characterizedTables 0 1 2 0 =
    ⟨true, 528⟩ := by native_decide

-- The universal characterization checks both sides for each visited thing.
-- The first mismatch costs 2+14+1+2=19 even with a million possible things.
example : ax73CharacterizationZScanCosted 0 0 {} 0 0 0 =
    ⟨true, 0⟩ := by native_decide
example : ax73CharacterizationZScanCosted 1 1000000 {} 0 0 0 =
    ⟨false, 19⟩ := by native_decide
example : ax73CharacterizationZScanCosted 3 3 modalTables 0 2 0 =
    ⟨false, 536⟩ := by native_decide
-- z=0 matches in 533 operations; z=1 and z=2 each match in 36.
example : ax73CharacterizationZScanCosted 3 3 characterizedTables 0 2 0 =
    ⟨true, 605⟩ := by native_decide
example : ax73CharacterizationZScanCosted 3 3 characterizedTables 1 2 0 =
    ⟨false, 550⟩ := by native_decide

-- Failure priority does not depend on eagerly evaluating later predicates.
-- A non-mode part skips inherence and foundation queries, even with a bad y.
example : ax73ConstituentFailureCosted 2 3 foundationTables 0 0 999 0 =
    ⟨some Ax73ConstituentFailure.missingMode, 17⟩ := by native_decide
example : ax73ConstituentFailureCosted 2 3 foundationTables 0 1 999 0 =
    ⟨none, 35⟩ := by native_decide
example : ax73ConstituentFailureCosted 3 3 modalTables 0 0 1 0 =
    ⟨some Ax73ConstituentFailure.missingInherence, 474⟩ := by native_decide
example : ax73ConstituentFailureCosted 3 3 modalTables 0 0 2 0 =
    ⟨some Ax73ConstituentFailure.missingFoundation, 535⟩ := by native_decide
example : ax73ConstituentFailureCosted 3 3 characterizedTables 0 1 2 0 =
    ⟨some Ax73ConstituentFailure.missingPart, 549⟩ := by native_decide
example : ax73ConstituentFailureCosted 3 3 characterizedTables 0 0 2 0 =
    ⟨none, 532⟩ := by native_decide
example (W T : Nat) (tables : FactTables) (z x y w : Nat) :
    (ax73ConstituentFailureCosted W T tables z x y w).value.isNone =
      ((partLookupCosted W T tables z x w).value ==
        (ax73CharacterizedCosted W T tables z x y w).value) :=
  ax73ConstituentFailureCosted_isNone W T tables z x y w

-- A first-coordinate result adds its option map, one visit, and the next
-- stop check: seven operations. No remaining coordinate is queried.
example : ax73PrimaryFailureCosted 2 3 foundationTables 0 1 0 =
    ⟨some (0, Ax73ConstituentFailure.missingMode), 24⟩ := by native_decide
example : ax73PrimaryFailureCosted 3 3 modalTables 0 1 0 =
    ⟨some (0, Ax73ConstituentFailure.missingInherence), 481⟩ := by native_decide
example : ax73PrimaryFailureCosted 3 3 modalTables 0 2 0 =
    ⟨some (0, Ax73ConstituentFailure.missingFoundation), 542⟩ := by native_decide
example : ax73PrimaryFailureCosted 3 3 characterizedTables 1 2 0 =
    ⟨some (0, Ax73ConstituentFailure.missingPart), 556⟩ := by native_decide
example : ax73PrimaryFailureCosted 3 3 characterizedTables 0 2 0 =
    ⟨none, 614⟩ := by native_decide

private def orderedConstituentTables := compileExplicitModelAST
  { characterizedAST with facts := characterizedAST.facts ++
      #[.binary .part 2 0 0, .binary .part 1 0 0] }

-- z=0 passes before z=1 fails. Both later things violate the mode condition,
-- and their source facts list z=2 first; coordinate order selects z=1.
example : ax73PrimaryFailureCosted 3 3 orderedConstituentTables 0 2 0 =
    ⟨some (1, Ax73ConstituentFailure.missingMode), 577⟩ := by native_decide
example : ax73PrimaryFailureCosted 0 0 {} 0 0 0 = ⟨none, 0⟩ := by native_decide
example : ax73PrimaryFailureCosted 1 1000000 {} 0 0 0 =
    ⟨some (0, Ax73ConstituentFailure.missingMode), 24⟩ := by native_decide
example (W T : Nat) (tables : FactTables) (x y w : Nat) :
    (ax73PrimaryFailureCosted W T tables x y w).value.isNone =
      (ax73CharacterizationZScanCosted W T tables x y w).value :=
  ax73PrimaryFailureCosted_isNone W T tables x y w

example : ax73PrimaryEvidenceCosted #[`w] #[`x, `y, `z] {} 0 1 2 0 Ax73ConstituentFailure.missingMode =
    ⟨#["Counterexample assignment: x = x, y = y, z = z, w = w.",
      "Required but missing: constituent `z` is a part of qua individual `x` but is not a computed `ExternallyDependentMode`.",
      "Suggestion: supply the mode, modal existence, and inherence facts needed for external dependence, or revise the `Part`/`QuaIndividualOf` assertions."], 36⟩ := by native_decide
example : ax73PrimaryEvidenceCosted #[`w] #[`x, `y, `z] {} 0 1 2 0 Ax73ConstituentFailure.missingInherence =
    ⟨#["Counterexample assignment: x = x, y = y, z = z, w = w.",
      "Required but missing: constituent `z` must `InheresIn(z, y)` because it is a part of `QuaIndividualOf(x, y)`.",
      "Suggestion: add the constituent's inherence in the asserted bearer, or revise the `Part`/`QuaIndividualOf` assertions."], 42⟩ := by native_decide
example : ax73PrimaryEvidenceCosted #[] #[] {} 1 2 3 4 Ax73ConstituentFailure.missingPart =
    ⟨#["Counterexample assignment: x = #1, y = #2, z = #3, w = #4.",
      "Required but missing: `Part(#3, #1)`; the entity is an externally dependent mode that inheres in the asserted bearer and shares the qua individual's foundation.",
      "Suggestion: add the missing constituent part fact, or revise the facts that satisfy the right-hand characterization."], 36⟩ := by native_decide
example : ax73PrimaryEvidenceCosted #[`w0, `w1] #[`a, `b, `c]
    foundationTables 1 2 0 0 Ax73ConstituentFailure.missingFoundation =
    ⟨#["Counterexample assignment: x = b, y = c, z = a, w = w0.",
      "Required but missing: constituent `a` and qua individual `b` must share `FoundationOf`; the tables show missing or ambiguous foundation data.",
      "  - a: ambiguous foundations `a`; `c`", "  - b: foundation `c`",
      "Suggestion: give both constituents exactly one common `FoundedBy` target, or revise the `Part`/`QuaIndividualOf` assertions."], 354⟩ := by native_decide
example : ax73PrimaryEvidenceCosted #[`w0, `w1] #[`a, `b, `c]
    distinctFoundationTables 1 0 2 0 Ax73ConstituentFailure.missingFoundation =
    ⟨#["Counterexample assignment: x = b, y = a, z = c, w = w0.",
      "Required but missing: constituent `c` and qua individual `b` must share `FoundationOf`; the tables show different foundations.",
      "  - c: foundation `b`", "  - b: foundation `c`",
      "Suggestion: give both constituents exactly one common `FoundedBy` target, or revise the `Part`/`QuaIndividualOf` assertions."], 341⟩ := by native_decide

example : ax73PrimaryZScanCosted #[`w] (Array.replicate 1000000 `x) {} false 0 0 0 =
    ⟨none, 1⟩ := by native_decide
example : ax73PrimaryZScanCosted #[] #[] {} true 0 0 0 = ⟨none, 2⟩ := by native_decide
example : ax73PrimaryZScanCosted #[`w0, `w1, `w2] #[`a, `b, `c]
    characterizedTables true 0 2 0 = ⟨none, 616⟩ := by native_decide
example : ax73PrimaryZScanCosted #[`w] #[`x] {} true 0 0 0 =
    ⟨some #["Counterexample assignment: x = x, y = x, z = x, w = w.",
      "Required but missing: constituent `x` is a part of qua individual `x` but is not a computed `ExternallyDependentMode`.",
      "Suggestion: supply the mode, modal existence, and inherence facts needed for external dependence, or revise the `Part`/`QuaIndividualOf` assertions."], 59⟩ := by native_decide

example : ax73ReverseEvidenceCosted #[`w] #[`a, `b] 0 1 0 =
    ⟨#["Counterexample assignment: x = a, y = b, w = w.",
      "Required but missing: `QuaIndividualOf(a, b)`; its complete part characterization holds.",
      "Suggestion: add the missing `QuaIndividualOf` fact, or revise a constituent part, inherence, external-dependence, or foundation fact."], 29⟩ := by native_decide
example : ax73ReverseEvidenceCosted #[] #[] 2 3 4 =
    ⟨#["Counterexample assignment: x = #2, y = #3, w = #4.",
      "Required but missing: `QuaIndividualOf(#2, #3)`; its complete part characterization holds.",
      "Suggestion: add the missing `QuaIndividualOf` fact, or revise a constituent part, inherence, external-dependence, or foundation fact."], 29⟩ := by native_decide

-- A false QuaIndividualOf query costs 17, the skipped primary scan costs
-- one, and the failed characterization costs 19. Three branches complete 40.
example : ax73AssignmentCosted #[`w] #[`a] {} 0 0 0 = ⟨none, 40⟩ := by native_decide
example : ax73AssignmentsCosted #[`w] #[`a] {} = ⟨none, 49⟩ := by native_decide
example : ax73AssignmentsCosted #[`w] #[`a, `b] {} = ⟨none, 253⟩ := by native_decide
example : ax73AssignmentsCosted #[] (Array.replicate 1000000 `a) {} =
    ⟨none, 0⟩ := by native_decide
example : ax73AssignmentsCosted (Array.replicate 1000000 `w) #[] {} =
    ⟨none, 3000000⟩ := by native_decide

private def assertedCharacterizationTables := compileExplicitModelAST
  { characterizedAST with facts := characterizedAST.facts.push (.binary .quaIndividualOf 0 2 0) }

-- An asserted characterization that holds needs no reverse-direction scan.
example : ax73AssignmentCosted #[`w0, `w1, `w2] #[`a, `b, `c]
    assertedCharacterizationTables 0 2 0 = ⟨none, 635⟩ := by native_decide
example : ax73AssignmentCosted #[`w0, `w1, `w2] #[`a, `b, `c]
    characterizedTables 0 2 0 =
    ⟨some #["Counterexample assignment: x = a, y = c, w = w0.",
      "Required but missing: `QuaIndividualOf(a, c)`; its complete part characterization holds.",
      "Suggestion: add the missing `QuaIndividualOf` fact, or revise a constituent part, inherence, external-dependence, or foundation fact."], 655⟩ := by native_decide
example : ax73PartCharacterizationAnalysisCosted #[`w0, `w1, `w2] #[`a, `b, `c]
    characterizedTables =
    ⟨#["Counterexample assignment: x = a, y = c, w = w0.",
      "Required but missing: `QuaIndividualOf(a, c)`; its complete part characterization holds.",
      "Suggestion: add the missing `QuaIndividualOf` fact, or revise a constituent part, inherence, external-dependence, or foundation fact."], 1671⟩ := by native_decide

private def orderedQuaTables := compileExplicitModelAST
  { worldCount := 2, thingCount := 2
    facts := #[.binary .quaIndividualOf 0 0 1, .binary .quaIndividualOf 1 0 0] }

-- World order takes priority over thing order and source-fact order.
example : ax73PartCharacterizationAnalysisCosted #[`w0, `w1] #[`a, `b] orderedQuaTables =
    ⟨#["Counterexample assignment: x = b, y = a, z = b, w = w0.",
      "Required but missing: constituent `b` is a part of qua individual `b` but is not a computed `ExternallyDependentMode`.",
      "Suggestion: supply the mode, modal existence, and inherence facts needed for external dependence, or revise the `Part`/`QuaIndividualOf` assertions."], 221⟩ := by native_decide
example : ax73PartCharacterizationAnalysisCosted #[] #[] {} =
    ⟨#["Part-characterization check for ax73 found no direct mismatch in either direction of the biconditional."], 4⟩ := by native_decide
example : ax73PartCharacterizationAnalysisCosted #[`w] #[] {} =
    ⟨#["Part-characterization check for ax73 found no direct mismatch in either direction of the biconditional."], 7⟩ := by native_decide
example : ax73PartCharacterizationAnalysisCosted #[`w] #[`a, `b] {} =
    ⟨#["Part-characterization check for ax73 found no direct mismatch in either direction of the biconditional."], 257⟩ := by native_decide
example (worldNames thingNames : Array Lean.Name) (tables : FactTables) :
    (ax73PartCharacterizationAnalysisCosted worldNames thingNames tables).value.size ≤ 5 :=
  ax73PartCharacterizationAnalysisCosted_size_le worldNames thingNames tables

example (worldNames thingNames : Array Lean.Name) (tables : FactTables) (x y w : Nat) :
    (ax73AssignmentCosted worldNames thingNames tables x y w).value.isNone =
      ((Complexity.diagnosticBinaryCosted worldNames.size thingNames.size tables
        .quaIndividualOf x y w).value ==
        (ax73CharacterizationZScanCosted worldNames.size thingNames.size tables x y w).value) :=
  ax73AssignmentCosted_isNone worldNames thingNames tables x y w

example (worldNames thingNames : Array Lean.Name) (tables : FactTables) :
    (ax73AssignmentsCosted worldNames thingNames tables).value = none ↔
      ∀ w < worldNames.size, ∀ x < thingNames.size, ∀ y < thingNames.size,
        (Complexity.diagnosticBinaryCosted worldNames.size thingNames.size tables
          .quaIndividualOf x y w).value =
        (ax73CharacterizationZScanCosted worldNames.size thingNames.size tables x y w).value :=
  ax73AssignmentsCosted_eq_none_iff worldNames thingNames tables

private def relatorFoundationAST : ModelAST :=
  { worldCount := 2, thingCount := 2
    facts := #[.unary .relator 0 0, .binary .part 1 0 0,
      .binary .foundedBy 0 0 0, .binary .foundedBy 1 1 0] }

private def relatorFoundationTables := compileExplicitModelAST relatorFoundationAST

private def relatorMismatchRows : Array String := #[
  "Counterexample assignment: x = a, y = b, w = w0.",
  "Required but missing: Relator `a` and its part `b` must share the same `FoundationOf`.",
  "Evidence for FoundationOf(a) = FoundationOf(b):",
  "  - a: foundation `a`", "  - b: foundation `b`"]

-- Three names cost 12, the two status strings cost 55 each, and the
-- concatenations, wording branch, and five push/emissions cost 31.
example : ax78EvidenceCosted #[`w0, `w1] #[`a, `b] relatorFoundationTables true 0 1 0 #[] =
    ⟨relatorMismatchRows, 153⟩ := by native_decide
example : ax78EvidenceCosted #[] #[] {} false 2 3 4 #["prefix"] =
    ⟨#["prefix", "Counterexample assignment: x = #2, y = #3, w = #4.",
      "Missing witness requirements: Relator `#2` and its part `#3` are compared with `FoundationOf`, but the DSL facts do not determine unique foundations.",
      "Evidence for FoundationOf(#2) = FoundationOf(#3):",
      "  - #2: no `FoundedBy` fact", "  - #3: no `FoundedBy` fact"], 49⟩ := by native_decide

example : ax78FoundationPairCosted #[`w0, `w1] #[`a, `b] {} 0 1 0 #["prefix"] =
    ⟨#["prefix"], 13⟩ := by native_decide
example : ax78FoundationPairCosted #[`w0, `w1] #[`a, `b] {} 2 0 0 #[] =
    ⟨#[], 3⟩ := by native_decide
example : ax78FoundationPairCosted #[`w0, `w1] #[`a, `b] relatorFoundationTables 0 0 0 #[] =
    ⟨#[], 115⟩ := by native_decide
example : ax78FoundationPairCosted #[`w0, `w1] #[`a, `b] relatorFoundationTables 0 1 0 #[] =
    ⟨relatorMismatchRows, 285⟩ := by native_decide

-- A five-row group reaches either budget. The remaining loops stop without
-- querying another pair; the public producer truncates to the requested size.
example : ax78FoundationScanCosted 1 #[`w0, `w1] #[`a, `b] relatorFoundationTables #[] =
    ⟨relatorMismatchRows, 418⟩ := by native_decide
example : ax78FoundationScanCosted 5 #[`w0, `w1] #[`a, `b] relatorFoundationTables #[] =
    ⟨relatorMismatchRows, 418⟩ := by native_decide
example : ax78FoundationAnalysisCosted 1 #[`w0, `w1] #[`a, `b] relatorFoundationTables =
    ⟨relatorMismatchRows, 423⟩ := by native_decide
example : diagnosticWitnessesBudgeted 1 #[`w0, `w1] #[`a, `b] #[] relatorFoundationTables "ax78" =
    #["Counterexample assignment: x = a, y = b, w = w0."] := by native_decide
example : ax78FoundationAnalysisCosted 6 #[`w0, `w1] #[`a, `b] relatorFoundationTables =
    ⟨relatorMismatchRows.push
      "Suggestion: align the `FoundedBy` facts for the relator and every relevant part, or remove/relax the `Relator`/`Part` assertions.", 527⟩ := by native_decide

private def missingRelatorFoundations := compileExplicitModelAST
  { worldCount := 2, thingCount := 2
    facts := #[.unary .relator 0 0, .binary .part 1 0 0] }

example : ax78FoundationAnalysisCosted 1 #[`w0, `w1] #[`a, `b] missingRelatorFoundations =
    ⟨#["Counterexample assignment: x = a, y = a, w = w0.",
      "Missing witness requirements: Relator `a` and its part `a` are compared with `FoundationOf`, but the DSL facts do not determine unique foundations.",
      "Evidence for FoundationOf(a) = FoundationOf(a):",
      "  - a: no `FoundedBy` fact", "  - a: no `FoundedBy` fact"], 264⟩ := by native_decide

private def reversedRelatorWorlds := compileExplicitModelAST
  { relatorFoundationAST with facts := #[.unary .relator 0 1] ++ relatorFoundationAST.facts }

-- The first source fact concerns w1, but traversal reports w0 first.
example : ax78FoundationAnalysisCosted 1 #[`w0, `w1] #[`a, `b] reversedRelatorWorlds =
    ⟨relatorMismatchRows, 423⟩ := by native_decide
example : ax78FoundationAnalysisCosted 11 #[`w0, `w1] #[`a, `b] reversedRelatorWorlds =
    ⟨relatorMismatchRows ++ #[
      "Counterexample assignment: x = a, y = a, w = w1.",
      "Missing witness requirements: Relator `a` and its part `a` are compared with `FoundationOf`, but the DSL facts do not determine unique foundations.",
      "Evidence for FoundationOf(a) = FoundationOf(a):",
      "  - a: no `FoundedBy` fact", "  - a: no `FoundedBy` fact",
      "Suggestion: align the `FoundedBy` facts for the relator and every relevant part, or remove/relax the `Relator`/`Part` assertions."], 775⟩ := by native_decide

example : ax78FoundationAnalysisCosted 6 #[`w0, `w1] #[`a, `b]
    (compileExplicitModelAST { relatorFoundationAST with
      facts := relatorFoundationAST.facts ++ relatorFoundationAST.facts }) =
    ax78FoundationAnalysisCosted 6 #[`w0, `w1] #[`a, `b] relatorFoundationTables := by native_decide

private def ax78NoMismatch : Array String := #[
  "Foundation check for ax78: every relator/part pair with unique DSL foundations has matching foundations.",
  "If Lean still reports ax78, inspect relator parts whose foundations are not explicitly determined by `FoundedBy` facts."]

-- A common target is insufficient when the relator also has another target:
-- FoundationOf needs uniqueness, so this remains a missing-witness report.
example : ax78FoundationPairCosted #[`w0, `w1] #[`a, `b, `c]
    (compileExplicitModelAST { foundationAST with facts := foundationAST.facts ++
      #[.unary .relator 0 0, .binary .part 1 0 0] }) 0 1 0 #[] =
    ⟨#["Counterexample assignment: x = a, y = b, w = w0.",
      "Missing witness requirements: Relator `a` and its part `b` are compared with `FoundationOf`, but the DSL facts do not determine unique foundations.",
      "Evidence for FoundationOf(a) = FoundationOf(b):",
      "  - a: ambiguous foundations `a`; `c`", "  - b: foundation `c`"], 382⟩ := by native_decide

private def matchingRelatorFoundations := compileExplicitModelAST
  { relatorFoundationAST with facts := #[.unary .relator 0 0, .binary .part 1 0 0,
      .binary .foundedBy 0 0 0, .binary .foundedBy 1 0 0] }

example : ax78FoundationAnalysisCosted 6 #[`w0, `w1] #[`a, `b] matchingRelatorFoundations =
    ⟨ax78NoMismatch, 379⟩ := by native_decide
example : ax78FoundationAnalysisCosted 0 #[] #[] {} = ⟨#[], 6⟩ := by native_decide
example : ax78FoundationAnalysisCosted 1 #[] #[] {} =
    ⟨ax78NoMismatch.extract 0 1, 10⟩ := by native_decide
example : ax78FoundationAnalysisCosted 2 #[] #[] {} = ⟨ax78NoMismatch, 12⟩ := by native_decide
example : ax78FoundationAnalysisCosted 0 (Array.replicate 1000000 `w) (Array.replicate 1000000 `a) {} =
    ⟨#[], 9⟩ := by native_decide
example : ax78FoundationAnalysisCosted 2 (Array.replicate 1000000 `w) #[] {} =
    ⟨ax78NoMismatch, 3000012⟩ := by native_decide

example (budget : Nat) (worldNames thingNames : Array Lean.Name) (tables : FactTables) :
    (ax78FoundationAnalysisCosted budget worldNames thingNames tables).value.size ≤ budget + 4 :=
  ax78FoundationAnalysisCosted_budget budget worldNames thingNames tables

private def properPartsAST : ModelAST :=
  { worldCount := 2, thingCount := 3
    facts := #[.binary .properPart 2 0 0, .binary .properPart 1 0 0,
      .binary .properPart 2 0 0, .binary .part 0 1 0, .binary .properPart 0 2 1] }

private def properPartsTables := compileExplicitModelAST properPartsAST

-- Valid coordinates cost 21 operations per absent part or 22 per present
-- part, plus one initialization. Source order and duplicate facts do not
-- change the ascending candidate order, and Part does not imply ProperPart.
example : properPartCandidatesCosted 2 3 properPartsTables 0 0 = ⟨#[1, 2], 66⟩ := by native_decide
example : properPartCandidatesCosted 2 3 properPartsTables 1 0 = ⟨#[], 64⟩ := by native_decide
example : properPartCandidatesCosted 2 3 properPartsTables 2 1 = ⟨#[0], 65⟩ := by native_decide
example : properPartCandidatesCosted 2 3 properPartsTables 0 1 = ⟨#[], 64⟩ := by native_decide
example : properPartCandidatesCosted 2 0 {} 0 0 = ⟨#[], 1⟩ := by native_decide

-- The candidate is the query's first coordinate and the whole is its second.
-- An invalid whole therefore reaches the second guard, costing four per query.
example : properPartCandidatesCosted 2 3 properPartsTables 3 0 = ⟨#[], 25⟩ := by native_decide
example : properPartCandidatesCosted 2 3 properPartsTables 0 2 = ⟨#[], 31⟩ := by native_decide
example : properPartCandidatesCosted 1 1000000 {} 0 0 = ⟨#[], 21000001⟩ := by native_decide

example (W T : Nat) (tables : FactTables) (x w : Nat) :
    (properPartCandidatesCosted W T tables x w).value.toList.Nodup :=
  properPartCandidatesCosted_nodup W T tables x w

example (W T : Nat) (tables : FactTables) (x w y : Nat) :
    y ∈ (properPartCandidatesCosted W T tables x w).value.toList ↔
      y < T ∧ (Complexity.diagnosticBinaryCosted W T tables .properPart y x w).value = true :=
  properPartCandidatesCosted_mem W T tables x w y

example (W T : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (x : Fin T) (w : Fin W) :
    (properPartCandidatesCosted W T tables x.val w.val).value =
      ((List.range T).filter (fun y => tables.binaryLookup "properPart" y x.val w.val)).toArray :=
  properPartCandidatesCosted_sparse_value W T tables agreement x w

example {T T' : Nat} (h : T ≤ T') : 22 * T + 1 ≤ 22 * T' + 1 := by omega

-- The public axiom 79 path sees the collector's ascending order, even when
-- the source lists the second proper part first and repeats it.
example : diagnosticWitnessesBudgeted 1 #[`w0, `w1] #[`r, `a, `b] #[]
    (compileExplicitModelAST { properPartsAST with
      facts := properPartsAST.facts.push (.unary .relator 0 0) }) "ax79" =
    #["Counterexample assignment: x = r, y = a, z = a, w = w0."] := by native_decide

example : diagnosticWitnessesBudgeted 3 #[`w] #[`r] #[]
    (compileExplicitModelAST
      { worldCount := 1, thingCount := 1
        facts := #[.unary .relator 0 0] }) "ax79" = #[
      "Counterexample assignment: x = r, w = w.",
      "Missing witness requirements: Relator `r` must have at least one proper part in the finite DSL model.",
      "Suggestion: add `ProperPart(part, relator)` facts and the corresponding qua-individual/dependence/foundation facts, or remove/relax the `Relator` assertion."] := by native_decide

example : diagnosticWitnessesBudgeted 3 #[`w0, `w1] #[`r, `a, `b] #[]
    (compileExplicitModelAST { properPartsAST with
      facts := properPartsAST.facts.push (.unary .relator 0 0) }) "ax79" = #[
      "Counterexample assignment: x = r, y = a, z = a, w = w0.",
      "Required together: proper parts of relator `r` must be qua individuals.",
      "Suggestion: add a `QuaIndividualOf(part, bearer)` fact for each proper part in this world, or revise the `Relator`/`ProperPart` assertions."] := by native_decide

private def ax79QuaAST : ModelAST :=
  { worldCount := 1, thingCount := 2
    facts := #[.binary .quaIndividualOf 0 0 0, .binary .quaIndividualOf 1 0 0] }

private def ax79SameAST : ModelAST :=
  { ax79QuaAST with facts := ax79QuaAST.facts ++
      #[.binary .foundedBy 0 0 0, .binary .foundedBy 1 0 0] }

private def ax79SameTables := compileExplicitModelAST ax79SameAST
private def ax79DifferentTables := compileExplicitModelAST
  { ax79QuaAST with facts := ax79QuaAST.facts ++
      #[.binary .foundedBy 0 0 0, .binary .foundedBy 1 1 0] }
private def ax79YExists := compileExplicitModelAST
  { ax79SameAST with facts := ax79SameAST.facts.push (.unary .ex 0 0) }
private def ax79ZExists := compileExplicitModelAST
  { ax79SameAST with facts := ax79SameAST.facts.push (.unary .ex 1 0) }

-- Failure priority is qua status, unique equal foundations, then dependence
-- in both directions. A missing requirement skips all later queries.
example : ax79PairFailureCosted 1 2 {} 0 1 0 =
    ⟨some Ax79PairFailure.missingQua, 39⟩ := by native_decide
example : ax79PairFailureCosted 1 2
    (compileExplicitModelAST { ax79QuaAST with facts := #[.binary .quaIndividualOf 0 0 0] }) 0 1 0 =
    ⟨some Ax79PairFailure.missingQua, 59⟩ := by native_decide
example : ax79PairFailureCosted 1 2 (compileExplicitModelAST ax79QuaAST) 0 1 0 =
    ⟨some Ax79PairFailure.missingFoundation, 132⟩ := by native_decide
example : ax79PairFailureCosted 1 2 ax79DifferentTables 0 1 0 =
    ⟨some Ax79PairFailure.differentFoundation, 139⟩ := by native_decide
example : ax79PairFailureCosted 1 2 ax79SameTables 0 1 0 = ⟨none, 173⟩ := by native_decide
example : ax79PairFailureCosted 1 2 ax79YExists 0 1 0 =
    ⟨some Ax79PairFailure.missingDependence, 168⟩ := by native_decide
example : ax79PairFailureCosted 1 2 ax79ZExists 0 1 0 =
    ⟨some Ax79PairFailure.missingDependence, 185⟩ := by native_decide
example : ax79PairFailureCosted 1 2 ax79YExists 0 0 0 = ⟨none, 197⟩ := by native_decide

-- Dense membership is idempotent, and computed predicates ignore matching
-- derived assertions. Neither change can repair a missing qua witness.
example : ax79PairFailureCosted 1 2
    (compileExplicitModelAST { ax79SameAST with facts := ax79SameAST.facts ++ ax79SameAST.facts })
    0 1 0 = ⟨none, 173⟩ := by native_decide
example : ax79PairFailureCosted 1 2
    { derivedProps := #[s!"sig.QuaIndividual {diagFinThingTerm 0} {diagFinWorldTerm 0}"] }
    0 1 0 = ⟨some Ax79PairFailure.missingQua, 39⟩ := by native_decide

-- Four name lookups cost 16, assignment assembly costs eight, initialization
-- costs one, and the first push costs two. Dispatch and the two simple rows
-- add seven. Foundation reports also charge both status searches.
example : ax79PairEvidenceCosted #[`w] #[`a, `b] {} 0 0 1 0 Ax79PairFailure.missingQua =
    ⟨#["Counterexample assignment: x = a, y = a, z = b, w = w.",
      "Required together: proper parts of relator `a` must be qua individuals.",
      "Suggestion: add a `QuaIndividualOf(part, bearer)` fact for each proper part in this world, or revise the `Relator`/`ProperPart` assertions."], 34⟩ := by native_decide
example : ax79PairEvidenceCosted #[`w] #[`a, `b] ax79YExists 0 0 1 0
    Ax79PairFailure.missingDependence =
    ⟨#["Counterexample assignment: x = a, y = a, z = b, w = w.",
      "Required together: proper parts of relator `a` must be mutually existentially dependent.",
      "Suggestion: align the parts' `Ex` facts so each exists in every world where the other exists, or revise the `Relator`/`ProperPart` assertions."], 34⟩ := by native_decide
example : ax79PairEvidenceCosted #[`w] #[`a, `b] ax79DifferentTables 0 0 1 0
    Ax79PairFailure.differentFoundation =
    ⟨#["Counterexample assignment: x = a, y = a, z = b, w = w.",
      "Required but missing: proper parts of relator `a` must share a foundation.",
      "Suggestion: align the `FoundedBy` facts for the relator's qua-individual parts.",
      "Evidence for FoundationOf(a) = FoundationOf(b):",
      "  - a: foundation `a`", "  - b: foundation `b`"], 162⟩ := by native_decide
example : ax79PairEvidenceCosted #[] #[] {} 0 0 1 0 Ax79PairFailure.missingFoundation =
    ⟨#["Counterexample assignment: x = #0, y = #0, z = #1, w = #0.",
      "Missing witness requirements: ax79 compares `FoundationOf` for relator parts, but the DSL facts do not determine unique foundations.",
      "Suggestion: give each qua-individual part exactly one `FoundedBy` target.",
      "Evidence for FoundationOf(#0) = FoundationOf(#1):",
      "  - #0: no `FoundedBy` fact", "  - #1: no `FoundedBy` fact"], 56⟩ := by native_decide

example (worldNames thingNames : Array Lean.Name) (tables : FactTables) (x y z w : Nat) :
    (ax79PairEvidenceCosted worldNames thingNames tables x y z w Ax79PairFailure.missingQua).cost = 34 :=
  ax79PairEvidenceCosted_missingQua_cost worldNames thingNames tables x y z w
example (worldNames thingNames : Array Lean.Name) (tables : FactTables) (x y z w : Nat) :
    (ax79PairEvidenceCosted worldNames thingNames tables x y z w Ax79PairFailure.missingDependence).cost = 34 :=
  ax79PairEvidenceCosted_missingDependence_cost worldNames thingNames tables x y z w

example : (ax79PairAnalysisCosted #[`w] #[`a, `b] {} 0 0 1 0).cost = 74 := by native_decide
example : (ax79PairAnalysisCosted #[`w] #[`a, `b]
    (compileExplicitModelAST ax79QuaAST) 0 0 1 0).cost = 273 := by native_decide
example : (ax79PairAnalysisCosted #[`w] #[`a, `b] ax79DifferentTables 0 0 1 0).cost = 302 := by native_decide
example : (ax79PairAnalysisCosted #[`w] #[`a, `b] ax79YExists 0 0 1 0).cost = 203 := by native_decide
example : (ax79PairAnalysisCosted #[`w] #[`a, `b] ax79ZExists 0 0 1 0).cost = 220 := by native_decide
example : ax79PairAnalysisCosted #[`w] #[`a, `b] ax79SameTables 0 0 1 0 =
    ⟨none, 174⟩ := by native_decide

-- The nested array loops preserve input order, including self-pairs. Each
-- visited pair adds four operations, each visited outer entry adds four,
-- and the final two selections cost two even for an empty array.
example : ax79PartPairsCosted #[`w] #[`a, `b] ax79YExists 0 0 #[0, 1] =
    ⟨(ax79PairAnalysisCosted #[`w] #[`a, `b] ax79YExists 0 0 1 0).value, 415⟩ := by native_decide
example : ax79PartPairsCosted #[`w] #[`a, `b] ax79SameTables 0 0 #[0, 1] =
    ⟨none, 722⟩ := by native_decide
example : ax79PartPairsCosted #[`w] #[`a, `b] {} 0 0 #[0, 1] =
    ⟨(ax79PairAnalysisCosted #[`w] #[`a, `b] {} 0 0 0 0).value, 84⟩ := by native_decide
example : ax79PartPairsCosted #[] #[] {} 0 0 #[] = ⟨none, 2⟩ := by native_decide
example : ax79PartPairsCosted #[`w] #[`a, `b] ax79ZExists 0 0 #[1, 0] =
    ⟨(ax79PairAnalysisCosted #[`w] #[`a, `b] ax79ZExists 0 1 0 0).value, 415⟩ := by native_decide
example : ax79PartPairsCosted #[`w] #[`a, `b] ax79YExists 0 0 #[0, 0, 1] =
    ⟨(ax79PairAnalysisCosted #[`w] #[`a, `b] ax79YExists 0 0 1 0).value, 617⟩ := by native_decide

-- Input allocation is outside this call. A failure in the first pair must
-- not allocate the trillion-pair product of a million-entry input array.
example : ax79PartPairsCosted #[`w] #[`a, `b] {} 0 0 (Array.replicate 1000000 0) =
    ⟨(ax79PairAnalysisCosted #[`w] #[`a, `b] {} 0 0 0 0).value, 84⟩ := by native_decide

example (worldNames thingNames : Array Lean.Name) (tables : FactTables)
    (x w : Nat) (parts : Array Nat) :
    (ax79PartPairsCosted worldNames thingNames tables x w parts).value =
      parts.toList.findSome? (fun y => parts.toList.findSome? (fun z =>
        (ax79PairAnalysisCosted worldNames thingNames tables x y z w).value)) :=
  ax79PartPairsCosted_value worldNames thingNames tables x w parts

example (worldNames thingNames : Array Lean.Name) (tables : FactTables)
    (x w : Nat) (parts : Array Nat) :
    (ax79PartPairsCosted worldNames thingNames tables x w parts).cost ≤
      ax79PartPairsCostBound worldNames.size thingNames.size parts.size :=
  ax79PartPairsCosted_cost_le worldNames thingNames tables x w parts

example {W W' T T' P P' : Nat} (hW : W ≤ W') (hT : T ≤ T') (hP : P ≤ P') :
    ax79PartPairsCostBound W T P ≤ ax79PartPairsCostBound W' T' P' :=
  ax79PartPairsCostBound_mono hW hT hP

example (worldNames thingNames : Array Lean.Name) (tables : FactTables)
    (x y z w : Nat) (rows : Array String)
    (found : (ax79PairAnalysisCosted worldNames thingNames tables x y z w).value = some rows) :
    rows.size ≤ 6 := ax79PairAnalysisCosted_some_size worldNames thingNames tables x y z w rows found

private def ax79NoMismatch : Array String := #[
  "Foundation check for ax79: no obvious DSL-level relator/foundation mismatch was found.",
  "If Lean still reports ax79, the remaining issue may involve the full closure direction of the relator definition."]

private def ax79NoPartsTables := compileExplicitModelAST
  { worldCount := 1, thingCount := 1, facts := #[.unary .relator 0 0] }

-- Name fallbacks have the same unit cost as valid names. The three rows cost
-- eight name operations, six concatenations, one initialization, and six
-- push/emission operations.
example : (ax79MissingPartsEvidenceCosted #[`w] #[`r] 0 0).cost = 21 := by native_decide
example : ax79MissingPartsEvidenceCosted #[] #[] 5 7 =
    ⟨#["Counterexample assignment: x = #5, w = #7.",
      "Missing witness requirements: Relator `#5` must have at least one proper part in the finite DSL model.",
      "Suggestion: add `ProperPart(part, relator)` facts and the corresponding qua-individual/dependence/foundation facts, or remove/relax the `Relator` assertion."], 21⟩ := by native_decide
example (worldNames thingNames : Array Lean.Name) (x w : Nat) :
    (ax79MissingPartsEvidenceCosted worldNames thingNames x w).cost = 21 :=
  ax79MissingPartsEvidenceCosted_cost worldNames thingNames x w

example : ax79RelatorAssignmentCosted #[`w] #[`r] {} 0 0 = ⟨none, 13⟩ := by native_decide
example : ax79RelatorAssignmentCosted #[`w] #[`r] {} 1 0 = ⟨none, 3⟩ := by native_decide
example : ax79RelatorAssignmentCosted #[`w] #[`r] ax79NoPartsTables 0 0 =
    ⟨some (ax79MissingPartsEvidenceCosted #[`w] #[`r] 0 0).value, 58⟩ := by native_decide
example : ax79RelatorsCosted #[`w] #[`r] ax79NoPartsTables =
    ⟨some (ax79MissingPartsEvidenceCosted #[`w] #[`r] 0 0).value, 64⟩ := by native_decide
example : ax79FoundationAnalysisCosted #[`w] #[`r] ax79NoPartsTables =
    ⟨(ax79MissingPartsEvidenceCosted #[`w] #[`r] 0 0).value, 65⟩ := by native_decide
example : ax79FoundationAnalysisCosted #[`w] #[`r] {} = ⟨ax79NoMismatch, 25⟩ := by native_decide
example : ax79FoundationAnalysisCosted #[] #[] {} = ⟨ax79NoMismatch, 6⟩ := by native_decide
example : ax79FoundationAnalysisCosted #[] (Array.replicate 1000000 `r) {} =
    ⟨ax79NoMismatch, 6⟩ := by native_decide
example : ax79FoundationAnalysisCosted (Array.replicate 1000000 `w) #[] {} =
    ⟨ax79NoMismatch, 3000006⟩ := by native_decide

private def ax79ProperRelatorTables := compileExplicitModelAST
  { properPartsAST with facts := properPartsAST.facts.push (.unary .relator 0 0) }

example : (ax79RelatorAssignmentCosted #[`w0, `w1] #[`r, `a, `b] ax79ProperRelatorTables 0 0).cost =
    184 := by native_decide
example : ax79FoundationAnalysisCosted #[`w0, `w1] #[`r, `a, `b] ax79ProperRelatorTables =
    ⟨#["Counterexample assignment: x = r, y = a, z = a, w = w0.",
      "Required together: proper parts of relator `r` must be qua individuals.",
      "Suggestion: add a `QuaIndividualOf(part, bearer)` fact for each proper part in this world, or revise the `Relator`/`ProperPart` assertions."], 197⟩ := by native_decide

-- A successful pair search resumes the surrounding relator scan. Source
-- fact order cannot make a later world or thing win the first-report search.
example : ax79FoundationAnalysisCosted #[`w] #[`a, `b]
    (compileExplicitModelAST { ax79SameAST with facts := ax79SameAST.facts ++
      #[.unary .relator 0 0, .binary .properPart 1 0 0] }) =
    ⟨ax79NoMismatch, 271⟩ := by native_decide
example : ax79FoundationAnalysisCosted #[`w0, `w1] #[`a, `b]
    (compileExplicitModelAST
      { worldCount := 2, thingCount := 2
        facts := #[.unary .relator 1 1, .unary .relator 1 0, .unary .relator 0 0] }) =
    ⟨(ax79MissingPartsEvidenceCosted #[`w0, `w1] #[`a, `b] 0 0).value, 92⟩ := by native_decide

example (worldNames thingNames : Array Lean.Name) (tables : FactTables) :
    (ax79FoundationAnalysisCosted worldNames thingNames tables).value.size ≤ 6 :=
  ax79FoundationAnalysisCosted_size_le worldNames thingNames tables
example {W W' T T' : Nat} (hW : W ≤ W') (hT : T ≤ T') :
    ax79FoundationAnalysisCostBound W T ≤ ax79FoundationAnalysisCostBound W' T' :=
  ax79FoundationAnalysisCostBound_mono hW hT

-- Registration scans keys, not witness arrays. A visited entry costs three
-- scan operations, one domain comparison, one branch, and (only for a matching
-- domain) one type comparison. Input-array construction is outside this call.
private def ax99Family : ProductFamilySpec :=
  { domain := 0, qualityType := 1, dimensionThings := #[], typeThings := #[] }

example : productFamilyEntryPresentCosted {} 0 1 = ⟨false, 0⟩ := by native_decide
example : productFamilyEntryPresentCosted { productFamilies := #[ax99Family] } 2 1 =
    ⟨false, 5⟩ := by native_decide
example : productFamilyEntryPresentCosted { productFamilies := #[ax99Family] } 0 2 =
    ⟨false, 6⟩ := by native_decide
example : productFamilyEntryPresentCosted { productFamilies := #[ax99Family] } 0 1 =
    ⟨true, 6⟩ := by native_decide
example : productFamilyEntryPresentCosted
    { productFamilies := #[{ ax99Family with domain := 2 },
        { ax99Family with qualityType := 2 }, ax99Family, ax99Family] } 0 1 =
    ⟨true, 17⟩ := by native_decide
example : productFamilyEntryPresentCosted
    { productFamilies := Array.replicate 1000000 ax99Family } 0 1 =
    ⟨true, 6⟩ := by native_decide
example : productFamilyEntryPresentCosted
    { productFamilies := Array.replicate 1000000 ax99Family } 2 1 =
    ⟨false, 5000000⟩ := by native_decide
example : productFamilyEntryPresentCosted
    { productFamilies := #[{ ax99Family with
        dimensionThings := Array.replicate 1000000 0 }] } 0 1 =
    ⟨true, 6⟩ := by native_decide

example (tables : FactTables) (x t : Nat) :
    (productFamilyEntryPresentCosted tables x t).value =
      tables.productFamilies.any (fun family => family.domain == x && family.qualityType == t) :=
  productFamilyEntryPresentCosted_value tables x t
example (tables : FactTables) (x t : Nat) :
    (productFamilyEntryPresentCosted tables x t).cost ≤ 6 * tables.productFamilies.size :=
  productFamilyEntryPresentCosted_cost_le tables x t

-- With no characterization targets, inferred empty families cannot justify
-- missing registration. This checks the diagnostic and ax99 rejection, not
-- whether the model satisfies the other 112 axioms.
private def ax99MissingFamilyTables := compileExplicitModelAST
  { worldCount := 1, thingCount := 2
    facts := #[.unary .qualityDomain 0 0, .binary .associatedWith 0 1 0] }

example : diagnosticWitnessesBudgeted 1 #[`w] #[`domain, `qualityType] #[]
    ax99MissingFamilyTables "ax99" =
    #["Missing product-family witness data for x = domain, t = qualityType, w = w."] := by
  native_decide
example : Checker.checkAx99WitnessEntriesPresent
    (ax99MissingFamilyTables.toFiniteModel4 1 2 (by decide) (by decide)) = false := by
  native_decide
example : Checker.checkAx99
    (ax99MissingFamilyTables.toFiniteModel4 1 2 (by decide) (by decide)) = false := by
  native_decide

private def ax99DeclaredFamily : ProductFamilySpec :=
  { domain := 0, qualityType := 1, dimensionThings := #[2], typeThings := #[2] }

private def ax99DeclaredAST : ModelAST :=
  { worldCount := 1, thingCount := 3
    facts := #[.unary .qualityDomain 0 0, .binary .associatedWith 0 1 0]
    productFamilies := #[ax99DeclaredFamily] }

private def ax99ValidAST : ModelAST :=
  { ax99DeclaredAST with facts := ax99DeclaredAST.facts ++
      #[.binary .associatedWith 2 2 0, .binary .characterization 1 2 0,
        .binary .memberOf 0 0 0, .tupleProjection 0 0 2 0, .binary .memberOf 2 2 0] }

-- A registered array is not evidence that its relational conditions hold.
-- With no domain members, projection is vacuous, but association still fails.
example : Complexity.productFamilyDiagnosticCosted 1 3
    (compileExplicitModelAST ax99DeclaredAST) 0 1 0 ax99DeclaredFamily =
    ⟨false, 137⟩ := by native_decide
example : diagnosticWitnessesBudgeted 1 #[`w] #[`domain, `qualityType, `dimension] #[]
    (compileExplicitModelAST ax99DeclaredAST) "ax99" =
    #["Product-family witness data is present for x = domain, t = qualityType, w = w, but it does not satisfy ax99."] := by
  native_decide
example : Checker.checkAx99
    ((compileExplicitModelAST ax99DeclaredAST).toFiniteModel4 1 3 (by decide) (by decide)) = false := by
  native_decide

-- The successful count is 22 for keys/shape, 76 for projection membership,
-- 118 for coordinate separation, 39 for associations, 49 for coverage,
-- and three branches between these scans.
example : Complexity.productFamilyDiagnosticCosted 1 3
    (compileExplicitModelAST ax99ValidAST) 0 1 0 ax99DeclaredFamily =
    ⟨true, 307⟩ := by native_decide
example : Checker.checkAx99
    ((compileExplicitModelAST ax99ValidAST).toFiniteModel4 1 3 (by decide) (by decide)) = true := by
  native_decide

-- Invalid coordinates and unequal arrays stop before relation queries.
example : Complexity.productFamilyDiagnosticCosted 1 3 {} 2 1 0 ax99DeclaredFamily =
    ⟨false, 3⟩ := by native_decide
example : Complexity.productFamilyDiagnosticCosted 1 3 {} 0 2 0 ax99DeclaredFamily =
    ⟨false, 4⟩ := by native_decide
example : Complexity.productFamilyDiagnosticCosted 1 0 {} 0 1 0 ax99DeclaredFamily =
    ⟨false, 6⟩ := by native_decide
example : Complexity.productFamilyDiagnosticCosted 1 1 {} 0 1 0 ax99DeclaredFamily =
    ⟨false, 8⟩ := by native_decide
example : Complexity.productFamilyDiagnosticCosted 0 3 {} 0 1 0 ax99DeclaredFamily =
    ⟨false, 10⟩ := by native_decide
example : Complexity.productFamilyDiagnosticCosted 1 3 {} 0 1 0
    { ax99DeclaredFamily with typeThings := #[] } = ⟨false, 12⟩ := by native_decide
example : Complexity.productFamilyDiagnosticCosted 1 3 {} 0 1 0
    { ax99DeclaredFamily with dimensionThings := #[3] } = ⟨false, 17⟩ := by native_decide
example : Complexity.productFamilyDiagnosticCosted 1 3 {} 0 1 0
    { ax99DeclaredFamily with typeThings := #[3] } = ⟨false, 22⟩ := by native_decide

-- The full validator searches all registered alternatives, not just the first
-- matching key. A later valid record can repair an invalid earlier witness.
example : Complexity.productFamiliesDiagnosticCosted 1 3
    { (compileExplicitModelAST ax99ValidAST) with productFamilies :=
      #[{ ax99DeclaredFamily with typeThings := #[] }, ax99DeclaredFamily] } 0 1 0 =
    ⟨true, 325⟩ := by native_decide
example : Complexity.productFamiliesDiagnosticCosted 1 3
    { (compileExplicitModelAST ax99ValidAST) with
      productFamilies := Array.replicate 1000000 ax99DeclaredFamily } 0 1 0 =
    ⟨true, 310⟩ := by native_decide

private def ax99DiagnosticAndChecker (facts : Array CompiledFact)
    (families : Array ProductFamilySpec) : Bool × Bool :=
  let tables := compileExplicitModelAST
    { worldCount := 1, thingCount := 3, facts := facts, productFamilies := families }
  ((Complexity.productFamiliesDiagnosticCosted 1 3 tables 0 1 0).value,
    Checker.checkAx99 (tables.toFiniteModel4 1 3 (by decide) (by decide)))

-- Both members project to 2 in the sole coordinate. Component membership
-- holds, but these distinct members cannot represent the same tuple.
example : ax99DiagnosticAndChecker
    (ax99ValidAST.facts ++ #[.binary .memberOf 1 0 0, .tupleProjection 1 0 2 0])
    #[ax99DeclaredFamily] = (false, false) := by native_decide

-- Giving the second member a different coordinate repairs that collision.
example : ax99DiagnosticAndChecker
    (ax99ValidAST.facts ++ #[.binary .memberOf 1 0 0, .tupleProjection 1 0 1 0,
      .binary .memberOf 1 2 0])
    #[ax99DeclaredFamily] = (true, true) := by native_decide

-- A zero-coordinate product has one tuple. It accepts at most one domain
-- member, even though coordinate membership itself is vacuous.
example : ax99DiagnosticAndChecker
    (ax99DeclaredAST.facts ++ #[.binary .memberOf 0 0 0, .binary .memberOf 1 0 0])
    #[ax99Family] = (false, false) := by native_decide

example : ax99DiagnosticAndChecker
    (ax99ValidAST.facts.filter fun | .binary .characterization 1 2 0 => false | _ => true)
    #[ax99DeclaredFamily] = (false, false) := by native_decide
example : ax99DiagnosticAndChecker
    (ax99ValidAST.facts.filter fun | .binary .memberOf 2 2 0 => false | _ => true)
    #[ax99DeclaredFamily] = (false, false) := by native_decide
example : ax99DiagnosticAndChecker
    (ax99ValidAST.facts.filter fun | .tupleProjection 0 0 2 0 => false | _ => true)
    #[ax99DeclaredFamily] = (false, false) := by native_decide
example : ax99DiagnosticAndChecker
    (ax99ValidAST.facts.push (.binary .characterization 1 0 0))
    #[ax99DeclaredFamily] = (false, false) := by native_decide

-- Missing projection cells return the tuple itself. This is a successful
-- witness when that tuple belongs to the supplied dimension.
example : ax99DiagnosticAndChecker
    ((ax99ValidAST.facts.filter fun | .tupleProjection 0 0 2 0 => false | _ => true).push
      (.binary .memberOf 0 2 0))
    #[ax99DeclaredFamily] = (true, true) := by native_decide
example : ax99DiagnosticAndChecker ax99DeclaredAST.facts #[ax99Family] =
    (true, true) := by native_decide
example : ax99DiagnosticAndChecker ax99ValidAST.facts #[ax99Family] =
    (false, false) := by native_decide
example : ax99DiagnosticAndChecker ax99ValidAST.facts
    #[{ ax99DeclaredFamily with typeThings := #[] }, ax99DeclaredFamily] =
    (true, true) := by native_decide
example : ax99DiagnosticAndChecker ax99ValidAST.facts
    #[{ ax99DeclaredFamily with dimensionThings := #[3] }] =
    (false, false) := by native_decide
example : ax99DiagnosticAndChecker
    (ax99ValidAST.facts.push (.tupleProjection 0 1 2 0))
    #[{ ax99DeclaredFamily with dimensionThings := #[2, 2], typeThings := #[2, 2] }] =
    (true, true) := by native_decide

example : Complexity.productFamilyDiagnosticCosted 1 3 {} 0 1 0
    { ax99DeclaredFamily with
      dimensionThings := Array.replicate 1000000 3
      typeThings := Array.replicate 1000000 2 } = ⟨false, 17⟩ := by native_decide

example (W T : Nat) (tables : FactTables) (x t w : Nat) (family : ProductFamilySpec) :
    (Complexity.productFamilyDiagnosticCosted W T tables x t w family).cost ≤
      Complexity.productFamilyDiagnosticBound T family.dimensionThings.size family.typeThings.size :=
  Complexity.productFamilyDiagnosticCosted_cost_le W T tables x t w family
example {T T' D D' Z Z' : Nat} (hT : T ≤ T') (hD : D ≤ D') (hZ : Z ≤ Z') :
    Complexity.productFamilyDiagnosticBound T D Z ≤ Complexity.productFamilyDiagnosticBound T' D' Z' :=
  Complexity.productFamilyDiagnosticBound_mono hT hD hZ

example {W W' T T' : Nat} {fs gs : Array ProductFamilySpec}
    (hW : W ≤ W') (hT : T ≤ T') (hR : fs.size ≤ gs.size)
    (hD : (fs.toList.map fun f => f.dimensionThings.size).sum ≤
      (gs.toList.map fun f => f.dimensionThings.size).sum)
    (hZ : (fs.toList.map fun f => f.typeThings.size).sum ≤
      (gs.toList.map fun f => f.typeThings.size).sum) :
    ax99QualityDomainAnalysisCostBound W T fs ≤ ax99QualityDomainAnalysisCostBound W' T' gs :=
  ax99QualityDomainAnalysisCostBound_mono hW hT hR hD hZ

-- The report collector visits every candidate type in coordinate order. A
-- successful characterization adds one append operation to the all-absent run.
example : characterizationTargetsCosted 1 0 {} 0 0 = ⟨#[], 1⟩ := by native_decide
example : characterizationTargetsCosted 1 3 (compileExplicitModelAST ax99DeclaredAST) 1 0 =
    ⟨#[], 64⟩ := by native_decide
example : characterizationTargetsCosted 1 3 (compileExplicitModelAST ax99ValidAST) 1 0 =
    ⟨#[2], 65⟩ := by native_decide

-- Both report categories retain their distinct explanations. The count includes
-- target collection, rendering selection, three indexed names, and row output.
example : ax99FailureEvidenceCosted #[`w] #[`domain, `qualityType]
    ax99MissingFamilyTables 0 1 0 false =
    ⟨#["Missing product-family witness data for x = domain, t = qualityType, w = w.",
      "The model says `domain` is a quality domain associated with `qualityType`, so ax99 needs an explicit finite product-family witness for that pair.",
      "Add a block of the form `product_family domain for qualityType:` with one `dimensions` entry and one `types` entry for each component quality type characterizing `qualityType`.",
      "For each listed dimension/type pair, also provide the ordinary facts that make the witness meaningful: `Characterization(t, z)`, `AssociatedWith(y, z)`, `MemberOf(tuple, x)` for domain members, `TupleProjection(tuple, i, component)`, and `MemberOf(component, y)`.",
      "Characterization targets currently found for `qualityType`: none."], 89⟩ := by native_decide
example : ax99FailureEvidenceCosted #[`w] #[`domain, `qualityType, `dimension]
    (compileExplicitModelAST ax99DeclaredAST) 0 1 0 true =
    ⟨#["Product-family witness data is present for x = domain, t = qualityType, w = w, but it does not satisfy ax99.",
      "The witness must list one quality dimension for each characterization of `qualityType` and prove that every member of `domain` projects into the corresponding dimension.",
      "Check the `dimensions` and `types` listed in the `product_family` block, the `Characterization(t, z)` facts, the `AssociatedWith(y, z)` facts for the listed dimensions, and the `TupleProjection(tuple, i, component)` plus `MemberOf(component, y)` facts for every domain member. Distinct domain members must differ in at least one listed coordinate.",
      "Characterization targets found for `qualityType`: none."], 102⟩ := by native_decide

-- A false association skips registration, witness validation, and formatting.
example : ax99AssociationCosted #[`w] #[`domain, `qualityType] {} 0 1 0 =
    ⟨none, 18⟩ := by native_decide
example : ax99AssociationCosted #[`w] (Array.replicate 1000000 `thing) {} 0 0 0 =
    ⟨none, 18⟩ := by native_decide

-- An absent quality-domain fact avoids the type scan. Empty searches retain
-- the fallback rows, while the one-world/one-thing case scans its sole domain.
example : ax99QualityDomainCosted #[`w] #[`x] {} 0 0 = ⟨none, 13⟩ := by native_decide
example : ax99AssignmentsCosted #[] #[] {} = ⟨none, 0⟩ := by native_decide
example : ax99AssignmentsCosted #[`w] #[`x] {} = ⟨none, 19⟩ := by native_decide
example : ax99QualityDomainAnalysisCosted #[] #[] {} =
    ⟨#["Product check for ax99: every asserted quality-domain association has a valid registered product-family witness in the diagnostic tables.",
      "If certification still reports ax99, inspect the conversion from registered product-family records to finite checker witnesses."], 6⟩ := by native_decide
example : ax99QualityDomainAnalysisCosted #[`w] #[`x] {} =
    ⟨#["Product check for ax99: every asserted quality-domain association has a valid registered product-family witness in the diagnostic tables.",
      "If certification still reports ax99, inspect the conversion from registered product-family records to finite checker witnesses."], 25⟩ := by native_decide

-- Numeric type order, rather than source-fact order, selects the first ax99
-- report after a quality-domain query succeeds.
private def ax99FirstAssociationTables := compileExplicitModelAST
  { worldCount := 1, thingCount := 3
    facts := #[.unary .qualityDomain 0 0, .binary .associatedWith 0 2 0,
      .binary .associatedWith 0 1 0] }

example : (ax99QualityDomainAnalysisCosted #[`w] #[`domain, `first, `second]
    ax99FirstAssociationTables).value =
    (ax99FailureEvidenceCosted #[`w] #[`domain, `first, `second]
      ax99FirstAssociationTables 0 1 0 false).value := by native_decide

-- World order takes priority over thing order. Within one world, the lower
-- thing coordinate takes priority even when its fact occurs later in the input.
private def ax99WorldOrderTables := compileExplicitModelAST
  { worldCount := 2, thingCount := 3
    facts := #[.unary .qualityDomain 0 1, .binary .associatedWith 0 1 1,
      .unary .qualityDomain 2 0, .binary .associatedWith 2 1 0] }

example : (ax99QualityDomainAnalysisCosted #[`w0, `w1] #[`a, `t, `b]
    ax99WorldOrderTables).value =
    (ax99FailureEvidenceCosted #[`w0, `w1] #[`a, `t, `b]
      ax99WorldOrderTables 2 1 0 false).value := by native_decide

example : (ax99QualityDomainAnalysisCosted #[`w] #[`a, `t, `b]
    (compileExplicitModelAST
      { worldCount := 1, thingCount := 3
        facts := #[.unary .qualityDomain 2 0, .binary .associatedWith 2 1 0,
          .unary .qualityDomain 0 0, .binary .associatedWith 0 1 0] })).value[0]? =
    some "Missing product-family witness data for x = a, t = t, w = w." := by native_decide

-- The complete analyzer includes nested loop control and result selection.
-- A valid family reaches the fallback only after all assignments pass.
example : (ax99QualityDomainAnalysisCosted #[`w] #[`domain, `qualityType]
    ax99MissingFamilyTables).cost = 155 := by native_decide

-- Six visited comparisons and branches cost twelve. The producer copies one prefix.
example : diagnosticWitnessesBudgetedCosted 1 #[`w] #[`domain, `qualityType] #[]
    ax99MissingFamilyTables "ax99" =
    ⟨#["Missing product-family witness data for x = domain, t = qualityType, w = w."], 175⟩ := by
  native_decide
example : diagnosticWitnessesBudgetedCosted 0 #[`w] #[`domain, `qualityType] #[]
    ax99MissingFamilyTables "ax99" = ⟨#[], 171⟩ := by native_decide

-- Every specialized branch adds its visited comparisons without changing the report.
example (budget : Nat) (worldNames thingNames : Array Lean.Name)
    (facts : Array NamedScopedFact) (tables : FactTables) :
    diagnosticWitnessesInnerCosted budget worldNames thingNames facts tables "ax68" =
      Complexity.Costed.charge 2 (ax68ClosureAnalysisCosted worldNames thingNames tables) ∧
    diagnosticWitnessesInnerCosted budget worldNames thingNames facts tables "ax71" =
      Complexity.Costed.charge 4 (ax71FoundationAnalysisCosted worldNames thingNames tables) ∧
    diagnosticWitnessesInnerCosted budget worldNames thingNames facts tables "ax73" =
      Complexity.Costed.charge 6 (ax73PartCharacterizationAnalysisCosted worldNames thingNames tables) ∧
    diagnosticWitnessesInnerCosted budget worldNames thingNames facts tables "ax78" =
      Complexity.Costed.charge 8 (ax78FoundationAnalysisCosted budget worldNames thingNames tables) ∧
    diagnosticWitnessesInnerCosted budget worldNames thingNames facts tables "ax79" =
      Complexity.Costed.charge 10 (ax79FoundationAnalysisCosted worldNames thingNames tables) ∧
    diagnosticWitnessesInnerCosted budget worldNames thingNames facts tables "ax99" =
      Complexity.Costed.charge 12 (ax99QualityDomainAnalysisCosted worldNames thingNames tables) := by
  simp [diagnosticWitnessesInnerCosted, Complexity.Costed.charge]
  omega

example : diagnosticWitnessesBudgetedCosted 1 #[`w] #[`a, `b] #[] ax68MissingTables "ax68" =
    ⟨#["Closure check for ax68: `a` is a moment at `w`, but no non-moment ultimate bearer is reachable through `InheresIn`."], 105⟩ := by
  native_decide
example : diagnosticWitnessesBudgetedCosted 0 #[`w] #[`a, `b] #[] ax68MissingTables "ax68" =
    ⟨#[], 101⟩ := by native_decide
-- Unrecognized names reach the generic fallback, preserving case-sensitive lookup.
-- The 104-entry registry scan costs 832 before the 18-operation fallback.
example : diagnosticWitnessesInnerCosted 4 #[] #[] #[] {} "AX68" =
    ⟨#["No structured DSL-level witness extractor is registered for AX68 yet."], 850⟩ := by
  native_decide
example : diagnosticWitnessesBudgetedCosted 1 #[] #[] #[] {} "unknown" =
    ⟨#["No structured DSL-level witness extractor is registered for unknown yet."], 858⟩ := by
  native_decide
-- Axiom 1 has two leading universals. Their extraction costs eight even when
-- the domain or output budget prevents assignment enumeration. Registry lookup
-- costs 11: the first entry matches, then the loop stops before the second read.
-- Both cases also initialize the empty environment and output array (two).
example : diagnosticWitnessesInnerCosted 4 #[] #[] #[] {} "ax1" =
    ⟨#["The structured checker did not find a DSL-level witness for ax1."], 47⟩ := by
  native_decide
example : diagnosticWitnessesInnerCosted 0 #[] #[] #[] {} "ax1" =
    ⟨#["The structured checker did not find a DSL-level witness for ax1."], 43⟩ := by
  native_decide

example : (ax99QualityDomainAnalysisCosted #[`w] #[`domain, `qualityType, `dimension]
    (compileExplicitModelAST ax99DeclaredAST)).cost = 318 := by native_decide
example : (ax99QualityDomainAnalysisCosted #[`w] #[`domain, `qualityType, `dimension]
    (compileExplicitModelAST ax99ValidAST)).cost = 438 := by native_decide

-- A nonempty target list uses indexed names instead of the literal "none".
example : ax99FailureEvidenceCosted #[`w] #[`domain, `qualityType, `dimension]
    (compileExplicitModelAST ax99ValidAST) 0 1 0 true =
    ⟨(ax99FailureEvidenceCosted #[`w] #[`domain, `qualityType, `dimension]
      (compileExplicitModelAST ax99DeclaredAST) 0 1 0 true).value.set! 3
      "Characterization targets found for `qualityType`: dimension.", 111⟩ := by native_decide

-- The collector must inspect its whole candidate domain when no target exists.
example : characterizationTargetsCosted 0 1000000 {} 0 0 = ⟨#[], 10000001⟩ := by native_decide

open private atomEvidenceCosted atomEvidenceCosted_value atomEvidenceSpec
  atomEvidenceCostBound atomEvidenceCostBound_mono atomEvidenceCosted_cost_le
  derivedUnarySourceEvidenceCosted binarySourceEvidenceCosted derivedBinarySourceEvidenceCosted
  ternarySourceEvidenceCosted quaternarySourceEvidenceCosted typeSemSourceEvidenceCosted
  from LeanUfo.UFO.DSL.Diagnostic.AxiomAnalysis

private def evidenceEnv : Array (String × Nat) :=
  #[("w", 0), ("x", 0), ("y", 1), ("z", 2), ("u", 3)]

-- Five bindings give lookup cost 21 and name-rendering cost 25. Each retained
-- fact adds its matcher cost and four scan operations, after initialization.
example : atomEvidenceCosted #[`w] #[`a, `b, `c, `d]
    #[.binary .inst "a" "b" (.at "w")] evidenceEnv
    (DiagAtom.binary .inst "x" "y" "w") = ⟨#["[w] a :: b"], 99⟩ := by native_decide
example : atomEvidenceCosted #[`w] #[`a, `b, `c, `d]
    #[.derived (.unary "P" "a") (.at "w")] evidenceEnv
    (DiagAtom.derivedUnary "P" "x" "w") =
    ⟨#["[w] [derived assertion] P(a)"], 74⟩ := by native_decide
example : atomEvidenceCosted #[`w] #[`a, `b, `c, `d]
    #[.derived (.binary "P" "a" "b") (.at "w")] evidenceEnv
    (DiagAtom.derivedBinary "P" "x" "y" "w") =
    ⟨#["[w] [derived assertion] P(a, b)"], 103⟩ := by native_decide
example : atomEvidenceCosted #[`w] #[`a, `b, `c, `d]
    #[.ternary .distance "a" "b" "c" (.at "w")] evidenceEnv
    (DiagAtom.ternary .distance "x" "y" "z" "w") =
    ⟨#["[w] Distance(a, b, c)"], 131⟩ := by native_decide
example : atomEvidenceCosted #[`w] #[`a, `b, `c, `d]
    #[.derived (.quaternary "P" "a" "b" "c" "d") (.at "w")] evidenceEnv
    (DiagAtom.quaternary "P" "x" "y" "z" "u" "w") =
    ⟨#["[w] [derived assertion] P(a, b, c, d)"], 161⟩ := by native_decide
example : atomEvidenceCosted #[`w] #[`a, `b, `c, `d]
    #[.binary .inst "a" "b" (.at "w")] evidenceEnv
    (DiagAtom.typeSem "y" "w") =
    ⟨#["[w] a :: b (makes b a possible type)"], 74⟩ := by native_decide
example : atomEvidenceCosted #[`w] #[`a, `b, `c, `d]
    #[.unary .mode "a" .everywhere] evidenceEnv
    (DiagAtom.unary .mode "x" "w") = ⟨#["[everywhere] Mode(a)"], 142⟩ := by native_decide
example : atomEvidenceCosted #[`w] #[`a, `b, `c, `d]
    #[.unary .mode "a" .everywhere] evidenceEnv
    (DiagAtom.individualSem "x" "w") = ⟨#[], 2⟩ := by native_decide

-- A wrong field skips names and scope. A wrong derived arity needs two
-- constructor tests. Primitive facts do not count as derived assertions.
example : binarySourceEvidenceCosted #[`w] 0 .inst "a" "b"
    (.binary .sub "a" "b" (.at "w")) = ⟨none, 4⟩ := by native_decide
example : derivedUnarySourceEvidenceCosted #[`w] 0 "P" "a"
    (.derived (.binary "P" "a" "b") (.at "w")) = ⟨none, 2⟩ := by native_decide
example : derivedBinarySourceEvidenceCosted #[`w] 0 "inst" "a" "b"
    (.binary .inst "a" "b" (.at "w")) = ⟨none, 1⟩ := by native_decide
example : typeSemSourceEvidenceCosted #[`w] 0 "b"
    (.binary .sub "a" "b" (.at "w")) = ⟨none, 2⟩ := by native_decide
example : atomEvidenceCosted #[`w] #[`a, `b, `c, `d]
    #[.binary .inst "a" "b" (.at "w"), .binary .sub "a" "b" (.at "w"),
      .binary .inst "a" "b" (.at "w")] evidenceEnv
    (DiagAtom.binary .inst "x" "y" "w") =
    ⟨#["[w] a :: b", "[w] a :: b"], 132⟩ := by native_decide

example (worldNames thingNames : Array Lean.Name) (facts : Array NamedScopedFact)
    (env : Array (String × Nat)) (atom : DiagAtom) :
    (atomEvidenceCosted worldNames thingNames facts env atom).value =
      atomEvidenceSpec worldNames thingNames facts env atom :=
  atomEvidenceCosted_value worldNames thingNames facts env atom
example (worldNames thingNames : Array Lean.Name) (facts : Array NamedScopedFact)
    (env : Array (String × Nat)) (atom : DiagAtom) :
    (atomEvidenceCosted worldNames thingNames facts env atom).cost ≤
      atomEvidenceCostBound env.size facts.size :=
  atomEvidenceCosted_cost_le worldNames thingNames facts env atom
example {e e' n n' : Nat} (he : e ≤ e') (hn : n ≤ n') :
    atomEvidenceCostBound e n ≤ atomEvidenceCostBound e' n' :=
  atomEvidenceCostBound_mono he hn

open private appendAtomEvidenceCosted appendFailingAtomEvidenceCosted
  appendFailingAtomEvidenceCosted_value appendFailingAtomEvidenceCosted_size_le
  appendFailingAtomEvidenceCosted_cost_le foldDiagArrayCosted foldDiagArrayCosted_value
  appendFailingAtomEvidenceCostBound_mono
  from LeanUfo.UFO.DSL.Diagnostic.AxiomAnalysis

-- Source evidence costs 99 and its atom label costs 82. The report adds two
-- header joins, two empty-test operations, two header-write operations, eight
-- for the source row, and six for the array visit: 201 in total.
example : appendFailingAtomEvidenceCosted 2 #[`w] #[`a, `b, `c, `d]
    #[.binary .inst "a" "b" (.at "w")] evidenceEnv #[]
    #[DiagAtom.binary .inst "x" "y" "w"] =
    ⟨#["Evidence for [w] a :: b:", "  - [w] a :: b"], 201⟩ := by native_decide

-- A header-only budget still pays for source lookup and header text.
example : appendFailingAtomEvidenceCosted 1 #[`w] #[`a, `b, `c, `d]
    #[.binary .inst "a" "b" (.at "w")] evidenceEnv #[]
    #[DiagAtom.binary .inst "x" "y" "w"] =
    ⟨#["Evidence for [w] a :: b:"], 196⟩ := by native_decide

-- A second atom remains unread after the first one fills the report.
example : appendFailingAtomEvidenceCosted 2 #[`w] #[`a, `b, `c, `d]
    #[.binary .inst "a" "b" (.at "w")] evidenceEnv #[]
    #[DiagAtom.binary .inst "x" "y" "w", DiagAtom.typeSem "y" "w"] =
    ⟨#["Evidence for [w] a :: b:", "  - [w] a :: b"], 204⟩ := by native_decide

example : appendFailingAtomEvidenceCosted 3 #[`w] #[`a, `b, `c, `d]
    #[.binary .inst "a" "b" (.at "w"), .binary .sub "a" "b" (.at "w"),
      .binary .inst "a" "b" (.at "w")] evidenceEnv #[]
    #[DiagAtom.binary .inst "x" "y" "w"] =
    ⟨#["Evidence for [w] a :: b:", "  - [w] a :: b", "  - [w] a :: b"], 239⟩ := by native_decide

example : appendFailingAtomEvidenceCosted 0 #[] #[] #[] #[] #["kept"]
    (Array.replicate 100000 (DiagAtom.individualSem "x" "w")) =
    ⟨#["kept"], 3⟩ := by native_decide

example : appendFailingAtomEvidenceCosted 1 #[] #[] #[] #[] #[]
    (Array.replicate 100000 (DiagAtom.individualSem "x" "w")) =
    ⟨#[], 1000000⟩ := by native_decide

example : appendFailingAtomEvidenceCosted 0 #[] #[] #[] #[] #["kept"] #[] =
    ⟨#["kept"], 0⟩ := by native_decide

example (budget : Nat) (worlds things : Array Lean.Name) (facts : Array NamedScopedFact)
    (env : Array (String × Nat)) (out : Array String) (atoms : Array DiagAtom)
    (hout : out.size ≤ budget) :
    (appendFailingAtomEvidenceCosted budget worlds things facts env out atoms).value.size ≤ budget :=
  appendFailingAtomEvidenceCosted_size_le budget worlds things facts env out atoms hout

example (budget : Nat) (worlds things : Array Lean.Name) (facts : Array NamedScopedFact)
    (env : Array (String × Nat)) (out : Array String) (atoms : Array DiagAtom) :
    (appendFailingAtomEvidenceCosted budget worlds things facts env out atoms).cost ≤
      atoms.size * (40 * env.size + 76 + 275 * facts.size) :=
  appendFailingAtomEvidenceCosted_cost_le budget worlds things facts env out atoms

example (items : Array Nat) (state : Nat) (stop : Nat → Bool)
    (visit : Nat → Nat → Complexity.Costed Nat) :
    (foldDiagArrayCosted items state stop visit).value =
      items.toList.foldl (fun state item => if stop state then state else (visit state item).value) state :=
  foldDiagArrayCosted_value items state stop visit

example {k k' e e' n n' : Nat} (hk : k ≤ k') (he : e ≤ e') (hn : n ≤ n') :
    k * (40 * e + 76 + 275 * n) ≤ k' * (40 * e' + 76 + 275 * n') :=
  appendFailingAtomEvidenceCostBound_mono hk he hn

open private appendContextAtomCosted appendContextAtomSpec appendContextAtomCosted_value
  appendContextAtomCosted_cost_le appendEvidenceForFormulaCosted appendEvidenceForFormulaSpec
  appendEvidenceForFormulaCosted_value appendEvidenceForFormulaCosted_size_le
  appendEvidenceForFormulaCosted_cost_le diagAtomCostBound
  appendEvidenceForFormulaCostBound_mono
  from LeanUfo.UFO.DSL.Diagnostic.AxiomAnalysis

-- A source match costs 99, the empty test costs two, and the retained row
-- costs eight. Source evidence takes priority even when the model is empty.
example : appendContextAtomCosted 1 #[`w] #[`a, `b, `c, `d]
    #[.binary .inst "a" "b" (.at "w")] 0 0 {} evidenceEnv #[]
    (DiagAtom.binary .inst "x" "y" "w") =
    ⟨#["  - [w] a :: b"], 109⟩ := by native_decide

-- Without source rows, lookup costs 73 and the model check costs 82.
-- A true result adds an 82-operation label, two joins, and a write/emission.
example : appendContextAtomCosted 1 #[`w] #[`a, `b, `c, `d]
    #[] 2 2 queryTables evidenceEnv #[] (DiagAtom.binary .inst "x" "y" "w") =
    ⟨#["  - [w] a :: b (present in generated finite model)"], 244⟩ := by native_decide
example : appendContextAtomCosted 1 #[`w] #[`a, `b, `c, `d]
    #[] 2 2 {} evidenceEnv #[] (DiagAtom.binary .inst "x" "y" "w") =
    ⟨#[], 158⟩ := by native_decide

-- The formula header costs 89. Atom collection costs three, the indexed
-- visit costs 115, and the final size comparison and branch cost two.
example : appendEvidenceForFormulaCosted 2 #[`w] #[`a, `b, `c, `d]
    #[.binary .inst "a" "b" (.at "w")] 2 2 queryTables #[] evidenceEnv
    (DiagFormula.atom (DiagAtom.binary .inst "x" "y" "w")) =
    ⟨#["Evidence for [w] a :: b:", "  - [w] a :: b"], 209⟩ := by native_decide

example : appendEvidenceForFormulaCosted 2 #[`w] #[`a, `b, `c, `d]
    #[] 2 2 queryTables #[] evidenceEnv
    (DiagFormula.atom (DiagAtom.binary .inst "x" "y" "w")) =
    ⟨#["Evidence for [w] a :: b:", "  - [w] a :: b (present in generated finite model)"], 344⟩ :=
  by native_decide

-- A formula fallback reuses the header label. It does not render it twice.
example : appendEvidenceForFormulaCosted 2 #[`w] #[`a, `b, `c, `d]
    #[] 2 2 {} #[] evidenceEnv
    (DiagFormula.not (DiagFormula.atom (DiagAtom.binary .inst "x" "y" "w"))) =
    ⟨#["Evidence for not ([w] a :: b):",
      "  - not ([w] a :: b) (true in generated finite model)"], 268⟩ :=
  by native_decide
example : appendEvidenceForFormulaCosted 2 #[`w] #[`a, `b, `c, `d]
    #[] 2 2 {} #[] evidenceEnv (DiagFormula.eqThing "x" "x") =
    ⟨#["Evidence for a = a:", "  - a = a (true in generated finite model)"], 69⟩ := by native_decide

-- Header text and atom collection precede the stop test even at budget zero.
example : appendEvidenceForFormulaCosted 0 #[`w] #[`a, `b, `c, `d]
    #[] 2 2 queryTables #[] evidenceEnv
    (DiagFormula.atom (DiagAtom.binary .inst "x" "y" "w")) =
    ⟨#[], 99⟩ := by native_decide
example : appendEvidenceForFormulaCosted 1 #[`w] #[`a, `b, `c, `d]
    #[] 2 2 queryTables #[] evidenceEnv
    (DiagFormula.atom (DiagAtom.binary .inst "x" "y" "w")) =
    ⟨#["Evidence for [w] a :: b:"], 101⟩ := by native_decide

example : appendEvidenceForFormulaCosted 3 #[`w] #[`a, `b, `c, `d]
    #[.binary .inst "a" "b" (.at "w"), .binary .sub "a" "b" (.at "w"),
      .binary .inst "a" "b" (.at "w")] 2 2 queryTables #[] evidenceEnv
    (DiagFormula.atom (DiagAtom.binary .inst "x" "y" "w")) =
    ⟨#["Evidence for [w] a :: b:", "  - [w] a :: b", "  - [w] a :: b"], 247⟩ := by native_decide

example : appendEvidenceForFormulaCosted 0 #[`w] #[`a, `b, `c, `d]
    #[] 2 2 queryTables #["kept"] evidenceEnv
    (DiagFormula.atom (DiagAtom.binary .inst "x" "y" "w")) =
    ⟨#["kept"], 99⟩ := by native_decide

example (budget W T : Nat) (worlds things : Array Lean.Name) (facts : Array NamedScopedFact)
    (tables : FactTables) (out : Array String) (env : Array (String × Nat)) (atom : DiagAtom) :
    (appendContextAtomCosted budget worlds things facts W T tables env out atom).value =
      appendContextAtomSpec budget worlds things facts W T tables env out atom :=
  appendContextAtomCosted_value budget worlds things facts W T tables env out atom

example (budget W T : Nat) (worlds things : Array Lean.Name) (facts : Array NamedScopedFact)
    (tables : FactTables) (out : Array String) (env : Array (String × Nat)) (formula : DiagFormula) :
    (appendEvidenceForFormulaCosted budget worlds things facts W T tables out env formula).value =
      appendEvidenceForFormulaSpec budget worlds things facts W T tables out env formula :=
  appendEvidenceForFormulaCosted_value budget worlds things facts W T tables out env formula

example (budget W T : Nat) (worlds things : Array Lean.Name) (facts : Array NamedScopedFact)
    (tables : FactTables) (out : Array String) (env : Array (String × Nat)) (formula : DiagFormula)
    (hout : out.size ≤ budget) :
    (appendEvidenceForFormulaCosted budget worlds things facts W T tables out env formula).value.size ≤ budget :=
  appendEvidenceForFormulaCosted_size_le budget worlds things facts W T tables out env formula hout

example (budget W T : Nat) (worlds things : Array Lean.Name) (facts : Array NamedScopedFact)
    (tables : FactTables) (out : Array String) (env : Array (String × Nat)) (formula : DiagFormula) :
    (appendEvidenceForFormulaCosted budget worlds things facts W T tables out env formula).cost ≤
      DiagFormula.nodeCount formula * (diagAtomCostBound W T tables env.size +
        60 * env.size + 115 + 275 * facts.size) + 15 :=
  appendEvidenceForFormulaCosted_cost_le budget worlds things facts W T tables out env formula

example {f f' e e' n n' q q' : Nat}
    (hf : f ≤ f') (he : e ≤ e') (hn : n ≤ n') (hq : q ≤ q') :
    f * (q + 60 * e + 115 + 275 * n) + 15 ≤
      f' * (q' + 60 * e' + 115 + 275 * n') + 15 :=
  appendEvidenceForFormulaCostBound_mono hf he hn hq

open private successTracesCosted successTracesCosted_trace_bounds
  successTracesIntoCosted successTracesIntoCosted_trace_bounds DiagTrace DiagTrace.mk
  successTracesIntoCosted_value successTracesIntoSpec successTracesCosted_value successTracesSpec
  successTracesCosted_cost_le DiagFormula.successTraceCostBound
  MinimizedFailure.context
  from LeanUfo.UFO.DSL.Diagnostic.AxiomAnalysis

example (W T : Nat) (tables : FactTables) (env : Array (String × Nat))
    (out : Array DiagTrace) (formula : DiagFormula) :
    (successTracesIntoCosted W T tables env out formula).value =
      successTracesIntoSpec W T tables env out formula :=
  successTracesIntoCosted_value W T tables env out formula

example (W T : Nat) (tables : FactTables) (env : Array (String × Nat)) (formula : DiagFormula) :
    (successTracesCosted W T tables env formula).value =
      successTracesSpec W T tables env formula :=
  successTracesCosted_value W T tables env formula

example (W T : Nat) (tables : FactTables) (env : Array (String × Nat)) (formula : DiagFormula) :
    (successTracesCosted W T tables env formula).cost ≤
      DiagFormula.successTraceCostBound W T tables env.size formula + 1 :=
  successTracesCosted_cost_le W T tables env formula

-- Equality in an empty environment costs four. A successful leaf adds four
-- operations, and the wrapper adds one for the empty trace array.
example : (successTracesCosted 0 0 {} #[] (DiagFormula.eqThing "x" "x")).cost = 9 :=
  by native_decide
example : (successTracesCosted 0 0 {} #[] (DiagFormula.eqWorld "w" "w")).cost = 9 :=
  by native_decide

-- A false equality at two bindings costs 20. The collector adds only the
-- initial two tests and the empty array. It retains no trace.
example : (successTracesCosted 0 2 {} #[("x", 0), ("y", 1)]
    (DiagFormula.eqThing "x" "y")).cost = 23 := by native_decide
example : (successTracesCosted 0 2 {} #[("x", 0), ("y", 1)]
    (DiagFormula.eqThing "x" "y")).value.size = 0 := by native_decide

example : (successTracesCosted 0 0 {} #[]
    (DiagFormula.and (DiagFormula.eqThing "x" "x") (DiagFormula.eqThing "y" "y"))).cost = 30 :=
  by native_decide
example : (successTracesCosted 0 0 {} #[]
    (DiagFormula.or (DiagFormula.eqThing "x" "x") (DiagFormula.eqThing "y" "y"))).cost = 23 :=
  by native_decide
example : (successTracesCosted 0 2 {} #[("x", 0), ("y", 1)]
    (DiagFormula.or (DiagFormula.eqThing "x" "y") (DiagFormula.eqThing "y" "y"))).cost = 91 :=
  by native_decide
example : (successTracesCosted 0 0 {} #[]
    (DiagFormula.imp (DiagFormula.eqThing "x" "x") (DiagFormula.eqThing "y" "y"))).cost = 28 :=
  by native_decide
example : (successTracesCosted 0 2 {} #[("x", 0), ("y", 1)]
    (DiagFormula.imp (DiagFormula.eqThing "x" "y") (DiagFormula.eqThing "y" "y"))).cost = 49 :=
  by native_decide

-- An empty existential domain returns false before witness search.
example : (successTracesCosted 0 0 {} #[]
    (DiagFormula.existsThing "x" (DiagFormula.eqThing "x" "x"))).cost = 4 := by native_decide
example : (successTracesCosted 0 1 {} #[]
    (DiagFormula.existsThing "x" (DiagFormula.eqThing "x" "x"))).cost = 56 := by native_decide
example : (successTracesCosted 1 0 {} #[]
    (DiagFormula.existsWorld "w" (DiagFormula.eqWorld "w" "w"))).cost = 56 := by native_decide
example : (successTracesCosted 1 0 {} #[]
    (DiagFormula.dia "v" "w" (DiagFormula.eqWorld "w" "w"))).cost = 56 := by native_decide

example (W T : Nat) (tables : FactTables) (env : Array (String × Nat)) (formula : DiagFormula)
    (trace : DiagTrace) (ht : trace ∈ (successTracesCosted W T tables env formula).value) :
    DiagFormula.nodeCount (DiagTrace.formula trace) ≤ DiagFormula.nodeCount formula ∧
      (DiagTrace.env trace).size ≤ env.size + DiagFormula.nodeCount formula :=
  successTracesCosted_trace_bounds W T tables env formula trace ht

-- The second successful subformula adds another binding. Trace environments
-- retain their own witness assignments in the same order as the conjunction.
example : ((successTracesCosted 0 1 {} #[]
    (DiagFormula.existsThing "x" (DiagFormula.and (DiagFormula.eqThing "x" "x")
      (DiagFormula.existsThing "y" (DiagFormula.eqThing "y" "y"))))).value.map
      (fun trace => (DiagFormula.nodeCount (DiagTrace.formula trace), (DiagTrace.env trace).size))) =
    #[(1, 1), (1, 2)] := by native_decide

private def deepContextFormula : DiagFormula :=
  DiagFormula.imp
    (DiagFormula.existsThing "x" (DiagFormula.existsThing "y"
      (DiagFormula.existsThing "z" (DiagFormula.existsThing "u"
        (DiagFormula.eqThing "u" "u")))))
    (DiagFormula.eqThing "a" "b")

-- The successful antecedent adds four witnesses. Its six-binding trace
-- must not be bounded by the failed consequent's two-binding environment.
example : (MinimizedFailure.context (minimizeFailureCosted 0 2 {}
    #[("a", 0), ("b", 1)] deepContextFormula).value).map
      (fun trace => (DiagTrace.env trace).size) = #[6] := by native_decide
example : (MinimizedFailure.env (minimizeFailureCosted 0 2 {}
    #[("a", 0), ("b", 1)] deepContextFormula).value).size = 2 := by native_decide

open private minimizeFailureCosted_trace_bounds appendContextEvidenceCosted
  appendContextEvidenceCosted_value appendContextEvidenceCosted_size_le appendContextEvidenceCosted_cost_le
  from LeanUfo.UFO.DSL.Diagnostic.AxiomAnalysis

example (W T : Nat) (tables : FactTables) (env : Array (String × Nat)) (formula : DiagFormula)
    (trace : DiagTrace)
    (ht : trace ∈ MinimizedFailure.context (minimizeFailureCosted W T tables env formula).value) :
    DiagFormula.nodeCount (DiagTrace.formula trace) ≤ DiagFormula.nodeCount formula ∧
      (DiagTrace.env trace).size ≤ env.size + DiagFormula.nodeCount formula :=
  minimizeFailureCosted_trace_bounds W T tables env formula trace ht

private def equalityTrace : DiagTrace := DiagTrace.mk (DiagFormula.eqThing "x" "x") #[]

-- The formula report costs 29. The trace visit adds six. A remaining trace
-- after a full two-row report adds only the three-operation stop test.
example : appendContextEvidenceCosted 2 #[] #[`a] #[] {} #[] #[equalityTrace] =
    ⟨#["Evidence for a = a:", "  - a = a (true in generated finite model)"], 35⟩ := by native_decide
example : appendContextEvidenceCosted 2 #[] #[`a] #[] {} #[] #[equalityTrace, equalityTrace] =
    ⟨#["Evidence for a = a:", "  - a = a (true in generated finite model)"], 38⟩ := by native_decide
example : appendContextEvidenceCosted 1 #[] #[`a] #[] {} #[] #[equalityTrace] =
    ⟨#["Evidence for a = a:"], 33⟩ := by native_decide
example : appendContextEvidenceCosted 0 #[] #[`a] #[] {} #["kept"]
    (Array.replicate 100000 equalityTrace) = ⟨#["kept"], 3⟩ := by native_decide

example (budget : Nat) (worlds things : Array Lean.Name) (facts : Array NamedScopedFact)
    (tables : FactTables) (out : Array String) (traces : Array DiagTrace) (hout : out.size ≤ budget) :
    (appendContextEvidenceCosted budget worlds things facts tables out traces).value.size ≤ budget :=
  appendContextEvidenceCosted_size_le budget worlds things facts tables out traces hout

example (budget F E : Nat) (worlds things : Array Lean.Name) (facts : Array NamedScopedFact)
    (tables : FactTables) (out : Array String) (traces : Array DiagTrace)
    (ht : ∀ trace ∈ traces,
      DiagFormula.nodeCount (DiagTrace.formula trace) ≤ F ∧ (DiagTrace.env trace).size ≤ E) :
    (appendContextEvidenceCosted budget worlds things facts tables out traces).cost ≤
      traces.size * (F * (diagAtomCostBound worlds.size things.size tables E +
        60 * E + 115 + 275 * facts.size) + 21) :=
  appendContextEvidenceCosted_cost_le budget worlds things facts tables out traces F E ht

open private firstMatchingEnvCosted firstMatchingEnvCosted_value
  firstMatchingEnvCosted_cost_le firstMatchingEnvCosted_some_size
  firstSuccessEnvCosted firstFailureEnvCosted evalDiagFormula
  from LeanUfo.UFO.DSL.Diagnostic.AxiomAnalysis

example (W T count : Nat) (tables : FactTables) (env : Array (String × Nat))
    (name : String) (body : DiagFormula) (wanted : Bool) :
    (firstMatchingEnvCosted W T tables env name body wanted count).value =
      (List.range count).findSome? (fun i =>
        let extended := env.push (name, i)
        if evalDiagFormula W T tables extended body == wanted then some extended else none) :=
  firstMatchingEnvCosted_value W T tables env name body wanted count

example (W T count : Nat) (tables : FactTables) (env : Array (String × Nat))
    (name : String) (body : DiagFormula) (wanted : Bool) :
    (firstMatchingEnvCosted W T tables env name body wanted count).cost ≤
      count * (DiagFormula.evalCostBound W T (diagAtomCostBound W T tables)
        (env.size + 1) body + 6) :=
  firstMatchingEnvCosted_cost_le W T tables env name body wanted count

-- Domain selection costs one. A visited equality at one binding costs 12,
-- followed by six traversal operations. A remaining coordinate adds stop cost three.
example : firstSuccessEnvCosted 0 0 {} #[] DiagVarKind.thing "x"
    (DiagFormula.eqThing "x" "x") = ⟨none, 1⟩ := by native_decide
example : firstSuccessEnvCosted 0 1 {} #[] DiagVarKind.thing "x"
    (DiagFormula.eqThing "x" "x") = ⟨some #[("x", 0)], 19⟩ := by native_decide
example : firstSuccessEnvCosted 0 1000000 {} #[] DiagVarKind.thing "x"
    (DiagFormula.eqThing "x" "x") = ⟨some #[("x", 0)], 22⟩ := by native_decide
example : firstSuccessEnvCosted 1000000 0 {} #[] DiagVarKind.world "w"
    (DiagFormula.eqWorld "w" "w") = ⟨some #[("w", 0)], 22⟩ := by native_decide

-- At two bindings each equality costs 20, so a visit costs 26. The first
-- mismatch is coordinate one. A later match at two costs three visits.
example : firstFailureEnvCosted 0 3 {} #[("x", 0)] DiagVarKind.thing "y"
    (DiagFormula.eqThing "x" "y") = ⟨some #[("x", 0), ("y", 1)], 56⟩ := by native_decide
example : firstSuccessEnvCosted 0 4 {} #[("x", 2)] DiagVarKind.thing "y"
    (DiagFormula.eqThing "x" "y") = ⟨some #[("x", 2), ("y", 2)], 82⟩ := by native_decide
example : firstSuccessEnvCosted 0 4 {} #[("x", 7)] DiagVarKind.thing "y"
    (DiagFormula.eqThing "x" "y") = ⟨none, 105⟩ := by native_decide
example : firstSuccessEnvCosted 0 1 {} #[("x", 7)] DiagVarKind.thing "x"
    (DiagFormula.eqThing "x" "x") = ⟨some #[("x", 7), ("x", 0)], 27⟩ := by native_decide
example : firstFailureEnvCosted 0 100000 {} #[] DiagVarKind.thing "x"
    (DiagFormula.eqThing "x" "x") = ⟨none, 1800001⟩ := by native_decide

open private lookupDiagnosticFormulaCosted lookupDiagnosticFormulaCosted_value
  lookupDiagnosticFormulaCosted_cost_le diagnosticFormulaRegistry diagnosticFormulaCosted
  from LeanUfo.UFO.DSL.Diagnostic.AxiomAnalysis

example (registry : Array (String × DiagFormula)) (field : String) :
    (lookupDiagnosticFormulaCosted registry field).value =
      registry.toList.foldl (fun selected entry =>
        if selected.isSome then selected
        else if entry.1 == field then some entry.2 else none) none :=
  lookupDiagnosticFormulaCosted_value registry field

example (registry : Array (String × DiagFormula)) (field : String) :
    (lookupDiagnosticFormulaCosted registry field).cost ≤ 8 * registry.size :=
  lookupDiagnosticFormulaCosted_cost_le registry field

example {smaller larger : Nat} (h : smaller ≤ larger) : 8 * smaller ≤ 8 * larger :=
  Nat.mul_le_mul_left 8 h

private def tinyFormulaRegistry : Array (String × DiagFormula) :=
  #[("first", DiagFormula.eqThing "x" "x"), ("last", DiagFormula.eqThing "x" "y")]

example : lookupDiagnosticFormulaCosted #[] "missing" = ⟨none, 0⟩ := by rfl
example : lookupDiagnosticFormulaCosted tinyFormulaRegistry "first" =
    ⟨some (DiagFormula.eqThing "x" "x"), 11⟩ := by rfl
example : lookupDiagnosticFormulaCosted tinyFormulaRegistry "last" =
    ⟨some (DiagFormula.eqThing "x" "y"), 16⟩ := by rfl
example : lookupDiagnosticFormulaCosted tinyFormulaRegistry "LAST" = ⟨none, 16⟩ := by rfl
example : lookupDiagnosticFormulaCosted tinyFormulaRegistry "missing" = ⟨none, 16⟩ := by rfl
example : lookupDiagnosticFormulaCosted
    #[("same", DiagFormula.eqThing "x" "x"), ("same", DiagFormula.eqThing "x" "y")] "same" =
    ⟨some (DiagFormula.eqThing "x" "x"), 11⟩ := by rfl
example : (lookupDiagnosticFormulaCosted
    (Array.replicate 100000 ("same", DiagFormula.eqThing "x" "x")) "same").cost = 11 :=
  by native_decide

example : diagnosticFormulaRegistry.size = 104 := by rfl
example : (diagnosticFormulaCosted "ax1").cost = 11 := by native_decide
example : (diagnosticFormulaCosted "ax104").cost = 832 := by native_decide
example : (diagnosticFormulaCosted "unknown").cost = 832 := by native_decide

open private minimizeFailureSpec minimizeFailureCosted_spec minimizeFailureCosted_cost_le
  DiagFormula.failureMinimizeCostBound withContextCosted withContextCosted_value
  withContextCosted_cost withContext MinimizedFailure
  from LeanUfo.UFO.DSL.Diagnostic.AxiomAnalysis

example (W T : Nat) (tables : FactTables) (env : Array (String × Nat)) (formula : DiagFormula) :
    (minimizeFailureCosted W T tables env formula).value =
      minimizeFailureSpec W T tables env formula :=
  minimizeFailureCosted_spec W T tables env formula

example (W T : Nat) (tables : FactTables) (env : Array (String × Nat)) (formula : DiagFormula) :
    (minimizeFailureCosted W T tables env formula).cost ≤
      DiagFormula.failureMinimizeCostBound W T tables env.size formula :=
  minimizeFailureCosted_cost_le W T tables env formula

example (context : Array DiagTrace) (failure : MinimizedFailure) :
    (withContextCosted context failure).value = withContext context failure :=
  withContextCosted_value context failure

example (context : Array DiagTrace) (failure : MinimizedFailure) :
    (withContextCosted context failure).cost = 3 * (MinimizedFailure.context failure).size :=
  withContextCosted_cost context failure

private def minimizeEnv : Array (String × Nat) := #[("x", 0), ("y", 1)]
private def minimizeTrue : DiagFormula := DiagFormula.eqThing "x" "x"
private def minimizeFalse : DiagFormula := DiagFormula.eqThing "x" "y"

-- A leaf selects its constructor and initializes its empty context.
example : (minimizeFailureCosted 1 1 {} minimizeEnv minimizeFalse).cost = 2 := by native_decide
example : (minimizeFailureCosted 1 1 {} minimizeEnv
    (DiagFormula.eqWorld "x" "y")).cost = 2 := by native_decide
example : (minimizeFailureCosted 1 1 {} minimizeEnv
    (DiagFormula.atom (DiagAtom.unary .moment "x" "w"))).cost = 2 := by native_decide

-- Each equality costs 20 at two bindings. Negation adds two evaluation
-- operations. Minimization adds its own constructor and branch tests.
example : (minimizeFailureCosted 1 1 {} minimizeEnv
    (DiagFormula.not minimizeFalse)).cost = 25 := by native_decide
example : (minimizeFailureCosted 1 1 {} minimizeEnv
    (DiagFormula.not minimizeTrue)).cost = 26 := by native_decide
example : (minimizeFailureCosted 1 1 {} minimizeEnv
    (DiagFormula.not (DiagFormula.not minimizeFalse))).cost = 29 := by native_decide

-- The first failed conjunct skips the right side. A true left side adds a
-- second evaluation and, when the right side fails, a 25-operation trace.
example : (minimizeFailureCosted 1 1 {} minimizeEnv
    (DiagFormula.and minimizeFalse minimizeTrue)).cost = 25 := by native_decide
example : (minimizeFailureCosted 1 1 {} minimizeEnv
    (DiagFormula.and minimizeTrue minimizeFalse)).cost = 72 := by native_decide
example : (minimizeFailureCosted 1 1 {} minimizeEnv
    (DiagFormula.and minimizeTrue minimizeTrue)).cost = 46 := by native_decide
example : (minimizeFailureCosted 1 1 {} minimizeEnv
    (DiagFormula.or minimizeTrue minimizeFalse)).cost = 25 := by native_decide
example : (minimizeFailureCosted 1 1 {} minimizeEnv
    (DiagFormula.or minimizeFalse minimizeFalse)).cost = 54 := by native_decide
example : (minimizeFailureCosted 1 1 {} minimizeEnv
    (DiagFormula.imp minimizeTrue minimizeFalse)).cost = 72 := by native_decide
example : (minimizeFailureCosted 1 1 {} minimizeEnv
    (DiagFormula.imp minimizeFalse minimizeTrue)).cost = 26 := by native_decide
example : (minimizeFailureCosted 1 1 {} minimizeEnv
    (DiagFormula.iff minimizeTrue minimizeFalse)).cost = 92 := by native_decide
example : (minimizeFailureCosted 1 1 {} minimizeEnv
    (DiagFormula.iff minimizeFalse minimizeTrue)).cost = 114 := by native_decide
example : (minimizeFailureCosted 1 1 {} minimizeEnv
    (DiagFormula.iff minimizeTrue minimizeTrue)).cost = 45 := by native_decide
example : (minimizeFailureCosted 1 1 {} minimizeEnv
    (DiagFormula.iff minimizeFalse minimizeFalse)).cost = 46 := by native_decide

-- Empty domains do no body work. The witness selector or formula evaluator
-- costs one, and the minimizer adds its two tests and empty context.
example : (minimizeFailureCosted 0 0 {} minimizeEnv
    (DiagFormula.forallThing "z" minimizeFalse)).cost = 4 := by native_decide
example : (minimizeFailureCosted 0 0 {} minimizeEnv
    (DiagFormula.forallWorld "z" minimizeFalse)).cost = 4 := by native_decide
example : (minimizeFailureCosted 0 0 {} minimizeEnv
    (DiagFormula.existsThing "z" minimizeFalse)).cost = 4 := by native_decide
example : (minimizeFailureCosted 0 0 {} minimizeEnv
    (DiagFormula.existsWorld "z" minimizeFalse)).cost = 4 := by native_decide
example : (minimizeFailureCosted 0 0 {} minimizeEnv
    (DiagFormula.box "w" "z" minimizeFalse)).cost = 4 := by native_decide
example : (minimizeFailureCosted 0 0 {} minimizeEnv
    (DiagFormula.dia "w" "z" minimizeFalse)).cost = 4 := by native_decide

-- A one-element domain extends the environment to three bindings. Equality
-- then costs 28, quantified evaluation costs 32, and witness search costs 35.
example : (minimizeFailureCosted 1 1 {} minimizeEnv
    (DiagFormula.forallThing "z" minimizeFalse)).cost = 39 := by native_decide
example : (minimizeFailureCosted 1 1 {} minimizeEnv
    (DiagFormula.forallWorld "z" minimizeTrue)).cost = 38 := by native_decide
example : (minimizeFailureCosted 1 1 {} minimizeEnv
    (DiagFormula.existsThing "z" minimizeTrue)).cost = 72 := by native_decide
example : (minimizeFailureCosted 1 1 {} minimizeEnv
    (DiagFormula.existsWorld "z" minimizeFalse)).cost = 35 := by native_decide
example : (minimizeFailureCosted 1 1 {} minimizeEnv
    (DiagFormula.box "w" "z" minimizeFalse)).cost = 39 := by native_decide
example : (minimizeFailureCosted 1 1 {} minimizeEnv
    (DiagFormula.dia "w" "z" minimizeTrue)).cost = 72 := by native_decide
example : (minimizeFailureCosted 1 1 {} minimizeEnv
    (DiagFormula.not (DiagFormula.forallThing "z" minimizeTrue))).cost = 74 := by native_decide
example : (minimizeFailureCosted 1 1 {} minimizeEnv
    (DiagFormula.not (DiagFormula.forallWorld "z" minimizeFalse))).cost = 37 := by native_decide
example : (minimizeFailureCosted 1 1 {} minimizeEnv
    (DiagFormula.not (DiagFormula.existsThing "z" minimizeTrue))).cost = 75 := by native_decide
example : (minimizeFailureCosted 1 1 {} minimizeEnv
    (DiagFormula.not (DiagFormula.existsWorld "z" minimizeFalse))).cost = 37 := by native_decide
example : (minimizeFailureCosted 1 1 {} minimizeEnv
    (DiagFormula.not (DiagFormula.box "w" "z" minimizeTrue))).cost = 74 := by native_decide
example : (minimizeFailureCosted 1 1 {} minimizeEnv
    (DiagFormula.not (DiagFormula.dia "w" "z" minimizeTrue))).cost = 75 := by native_decide

-- The inner implication contributes one context trace. Prepending the outer
-- antecedent copies that right-hand trace at cost three.
example : (minimizeFailureCosted 1 1 {} minimizeEnv
    (DiagFormula.imp minimizeTrue (DiagFormula.imp minimizeTrue minimizeFalse))).cost = 168 :=
  by native_decide

-- Both disjunctions copy a two-binding right environment. Only the first
-- copies a right context trace, so its count is three larger.
example : (minimizeFailureCosted 1 1 {} minimizeEnv
    (DiagFormula.or minimizeFalse (DiagFormula.imp minimizeTrue minimizeFalse))).cost = 150 :=
  by native_decide
example : (minimizeFailureCosted 1 1 {} minimizeEnv
    (DiagFormula.or (DiagFormula.imp minimizeTrue minimizeFalse) minimizeFalse)).cost = 147 :=
  by native_decide

end LeanUfo.Test.Complexity.Diagnostics
