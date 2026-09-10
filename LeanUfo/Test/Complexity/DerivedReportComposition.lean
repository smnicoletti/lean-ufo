import LeanUfo.UFO.DSL.Complexity

/-!
# Complete derived-report regressions

These tests separate name resolution, field selection, complete report
construction, and the final output cap. Exact counts use the primitive-call
model, including work done before a later row is discarded.
-/

namespace LeanUfo.Test.Complexity.DerivedReportComposition

open Lean LeanUfo.UFO.DSL
open private resolveReport1Costed resolveReport2Costed resolveReport3Costed resolveReport4Costed
  derivedAssertionRequiredMissingCosted derivedAssertionEvidenceCosted
  derivedAssertionRequiredMissingCosted_value derivedAssertionEvidenceCosted_value
  derivedAssertionRequiredMissingSpec derivedAssertionEvidenceSpec
  renderDerivedAssertionFailureCosted renderDerivedAssertionFailureCosted_value
  renderDerivedAssertionFailureSpec FailedDerivedAssertion FailedDerivedAssertion.mk
  firstDerivedAssertionFailureCosted
  from LeanUfo.UFO.DSL.Diagnostic.DerivedAssertions

private def emptyTables : FactTables :=
  compileExplicitModelAST { worldCount := 1, thingCount := 2, facts := #[] }

-- Name "a" costs 12 to find, "b" costs 18, and an absent name costs 18.
-- Every requested lookup runs before the first result match. The fallback
-- costs seven; the successful continuation costs five.
example : resolveReport1Costed #[`a, `b] "a"
    (fun _ => .tick (99 : Nat) 7) (fun i => .tick i 5) = ⟨0, 18⟩ := by native_decide
example : resolveReport1Costed #[`a, `b] "missing"
    (fun _ => .tick (99 : Nat) 7) (fun i => .tick i 5) = ⟨99, 26⟩ := by native_decide
example : resolveReport2Costed #[`a, `b] "missing" "b"
    (fun _ => .tick (99 : Nat) 7) (fun i j => .tick (i + j) 5) = ⟨99, 44⟩ := by native_decide
example : resolveReport2Costed #[`a, `b] "a" "missing"
    (fun _ => .tick (99 : Nat) 7) (fun i j => .tick (i + j) 5) = ⟨99, 39⟩ := by native_decide
example : resolveReport2Costed #[`a, `b] "a" "b"
    (fun _ => .tick (99 : Nat) 7) (fun i j => .tick (i + j) 5) = ⟨1, 37⟩ := by native_decide
example : resolveReport3Costed #[`a, `b] "missing" "a" "b"
    (fun _ => .tick (99 : Nat) 7) (fun i j k => .tick (i + j + k) 5) = ⟨99, 56⟩ := by native_decide
example : resolveReport4Costed #[`a, `b] "missing" "a" "b" "a"
    (fun _ => .tick (99 : Nat) 7) (fun i j k l => .tick (i + j + k + l) 5) = ⟨99, 68⟩ := by native_decide
example : resolveReport4Costed #[`a, `b] "a" "b" "a" "b"
    (fun _ => .tick (99 : Nat) 7) (fun i j k l => .tick (i + j + k + l) 5) = ⟨2, 69⟩ := by native_decide

-- An unsupported field does not search its names. Required-missing text
-- still charges the fallback that was constructed before field selection.
example : (derivedAssertionRequiredMissingCosted #[`w] (Array.replicate 1000 `a) emptyTables
    (.unary "Unknown" "missing") 0).cost = 31 := by native_decide
example : (derivedAssertionRequiredMissingCosted #[`w] (Array.replicate 1000 `a) emptyTables
    (.binary "Unknown" "missing" "missing") 0).cost = 37 := by native_decide
example : (derivedAssertionRequiredMissingCosted #[`w] (Array.replicate 1000 `a) emptyTables
    (.ternary "Unknown" "missing" "missing" "missing") 0).cost = 21 := by native_decide
example : (derivedAssertionRequiredMissingCosted #[`w] (Array.replicate 1000 `a) emptyTables
    (.quaternary "Unknown" "missing" "missing" "missing" "missing") 0).cost = 25 := by native_decide
example : (derivedAssertionEvidenceCosted #[`w] (Array.replicate 1000 `a) emptyTables
    (.unary "Unknown" "missing") 0).cost = 20 := by native_decide
example : (derivedAssertionEvidenceCosted #[`w] (Array.replicate 1000 `a) emptyTables
    (.binary "Unknown" "missing" "missing") 0).cost = 24 := by native_decide
example : (derivedAssertionEvidenceCosted #[`w] (Array.replicate 1000 `a) emptyTables
    (.ternary "Unknown" "missing" "missing" "missing") 0).cost = 6 := by native_decide
example : (derivedAssertionEvidenceCosted #[`w] (Array.replicate 1000 `a) emptyTables
    (.quaternary "Unknown" "missing" "missing" "missing" "missing") 0).cost = 8 := by native_decide

-- Check all 25 recognized fields in each dispatcher. A missing first name
-- skips the component but not the other argument-name lookups. These tests
-- also lock the field-comparison order, which differs between the dispatchers.
example : (derivedAssertionRequiredMissingCosted #[`w] #[`a, `b] emptyTables
    (.unary "Quality" "missing") 0).cost = 34 := by native_decide
example : (derivedAssertionRequiredMissingCosted #[`w] #[`a, `b] emptyTables
    (.unary "ExternallyDependentMode" "missing") 0).cost = 36 := by native_decide
example : (derivedAssertionRequiredMissingCosted #[`w] #[`a, `b] emptyTables
    (.unary "NonEmptySet" "missing") 0).cost = 38 := by native_decide
example : (derivedAssertionRequiredMissingCosted #[`w] #[`a, `b] emptyTables
    (.unary "QualityStructure" "missing") 0).cost = 40 := by native_decide
example : (derivedAssertionRequiredMissingCosted #[`w] #[`a, `b] emptyTables
    (.unary "SimpleQuality" "missing") 0).cost = 42 := by native_decide
example : (derivedAssertionRequiredMissingCosted #[`w] #[`a, `b] emptyTables
    (.unary "ComplexQuality" "missing") 0).cost = 44 := by native_decide
example : (derivedAssertionRequiredMissingCosted #[`w] #[`a, `b] emptyTables
    (.unary "SimpleQualityType" "missing") 0).cost = 46 := by native_decide
example : (derivedAssertionRequiredMissingCosted #[`w] #[`a, `b] emptyTables
    (.unary "ComplexQualityType" "missing") 0).cost = 48 := by native_decide
example : (derivedAssertionRequiredMissingCosted #[`w] #[`a, `b] emptyTables
    (.unary "QuaIndividual" "missing") 0).cost = 50 := by native_decide
example : (derivedAssertionRequiredMissingCosted #[`w] #[`a, `b] emptyTables
    (.binary "ExternallyDependent" "missing" "a") 0).cost = 48 := by native_decide
example : (derivedAssertionRequiredMissingCosted #[`w] #[`a, `b] emptyTables
    (.binary "ExistentialDependence" "missing" "a") 0).cost = 50 := by native_decide
example : (derivedAssertionRequiredMissingCosted #[`w] #[`a, `b] emptyTables
    (.binary "ExistentialIndependence" "missing" "a") 0).cost = 52 := by native_decide
example : (derivedAssertionRequiredMissingCosted #[`w] #[`a, `b] emptyTables
    (.binary "UltimateBearerOf" "missing" "a") 0).cost = 54 := by native_decide
example : (derivedAssertionRequiredMissingCosted #[`w] #[`a, `b] emptyTables
    (.binary "SubsetOf" "missing" "a") 0).cost = 56 := by native_decide
example : (derivedAssertionRequiredMissingCosted #[`w] #[`a, `b] emptyTables
    (.binary "ProperSubsetOf" "missing" "a") 0).cost = 58 := by native_decide
example : (derivedAssertionRequiredMissingCosted #[`w] #[`a, `b] emptyTables
    (.binary "ProperSub" "missing" "a") 0).cost = 60 := by native_decide
example : (derivedAssertionRequiredMissingCosted #[`w] #[`a, `b] emptyTables
    (.binary "GenericFunctionalDependence" "missing" "a") 0).cost = 62 := by native_decide
example : (derivedAssertionRequiredMissingCosted #[`w] #[`a, `b] emptyTables
    (.binary "GenericConstitutionalDependence" "missing" "a") 0).cost = 64 := by native_decide
example : (derivedAssertionRequiredMissingCosted #[`w] #[`a, `b] emptyTables
    (.binary "Categorizes" "missing" "a") 0).cost = 66 := by native_decide
example : (derivedAssertionRequiredMissingCosted #[`w] #[`a, `b] emptyTables
    (.binary "IsDisjointWith" "missing" "a") 0).cost = 68 := by native_decide
example : (derivedAssertionRequiredMissingCosted #[`w] #[`a, `b] emptyTables
    (.ternary "IsCompletelyCoveredBy" "missing" "a" "a") 0).cost = 62 := by native_decide
example : (derivedAssertionRequiredMissingCosted #[`w] #[`a, `b] emptyTables
    (.ternary "IsPartitionedInto" "missing" "a" "a") 0).cost = 64 := by native_decide
example : (derivedAssertionRequiredMissingCosted #[`w] #[`a, `b] emptyTables
    (.quaternary "IndividualFunctionalDependence" "missing" "a" "a" "a") 0).cost = 76 := by native_decide
example : (derivedAssertionRequiredMissingCosted #[`w] #[`a, `b] emptyTables
    (.quaternary "ComponentOf" "missing" "a" "a" "a") 0).cost = 78 := by native_decide
example : (derivedAssertionRequiredMissingCosted #[`w] #[`a, `b] emptyTables
    (.quaternary "Constitution" "missing" "a" "a" "a") 0).cost = 80 := by native_decide
example : (derivedAssertionEvidenceCosted #[`w] #[`a, `b] emptyTables
    (.unary "Quality" "missing") 0).cost = 23 := by native_decide
example : (derivedAssertionEvidenceCosted #[`w] #[`a, `b] emptyTables
    (.unary "ExternallyDependentMode" "missing") 0).cost = 25 := by native_decide
example : (derivedAssertionEvidenceCosted #[`w] #[`a, `b] emptyTables
    (.unary "NonEmptySet" "missing") 0).cost = 27 := by native_decide
example : (derivedAssertionEvidenceCosted #[`w] #[`a, `b] emptyTables
    (.unary "QualityStructure" "missing") 0).cost = 29 := by native_decide
example : (derivedAssertionEvidenceCosted #[`w] #[`a, `b] emptyTables
    (.unary "SimpleQuality" "missing") 0).cost = 31 := by native_decide
example : (derivedAssertionEvidenceCosted #[`w] #[`a, `b] emptyTables
    (.unary "ComplexQuality" "missing") 0).cost = 33 := by native_decide
example : (derivedAssertionEvidenceCosted #[`w] #[`a, `b] emptyTables
    (.unary "SimpleQualityType" "missing") 0).cost = 35 := by native_decide
example : (derivedAssertionEvidenceCosted #[`w] #[`a, `b] emptyTables
    (.unary "ComplexQualityType" "missing") 0).cost = 37 := by native_decide
example : (derivedAssertionEvidenceCosted #[`w] #[`a, `b] emptyTables
    (.unary "QuaIndividual" "missing") 0).cost = 39 := by native_decide
example : (derivedAssertionEvidenceCosted #[`w] #[`a, `b] emptyTables
    (.binary "ExternallyDependent" "missing" "a") 0).cost = 35 := by native_decide
example : (derivedAssertionEvidenceCosted #[`w] #[`a, `b] emptyTables
    (.binary "ExistentialDependence" "missing" "a") 0).cost = 37 := by native_decide
example : (derivedAssertionEvidenceCosted #[`w] #[`a, `b] emptyTables
    (.binary "UltimateBearerOf" "missing" "a") 0).cost = 39 := by native_decide
example : (derivedAssertionEvidenceCosted #[`w] #[`a, `b] emptyTables
    (.binary "ExistentialIndependence" "missing" "a") 0).cost = 41 := by native_decide
example : (derivedAssertionEvidenceCosted #[`w] #[`a, `b] emptyTables
    (.binary "IsDisjointWith" "missing" "a") 0).cost = 43 := by native_decide
example : (derivedAssertionEvidenceCosted #[`w] #[`a, `b] emptyTables
    (.binary "SubsetOf" "missing" "a") 0).cost = 45 := by native_decide
example : (derivedAssertionEvidenceCosted #[`w] #[`a, `b] emptyTables
    (.binary "ProperSubsetOf" "missing" "a") 0).cost = 47 := by native_decide
example : (derivedAssertionEvidenceCosted #[`w] #[`a, `b] emptyTables
    (.binary "ProperSub" "missing" "a") 0).cost = 49 := by native_decide
example : (derivedAssertionEvidenceCosted #[`w] #[`a, `b] emptyTables
    (.binary "GenericFunctionalDependence" "missing" "a") 0).cost = 51 := by native_decide
example : (derivedAssertionEvidenceCosted #[`w] #[`a, `b] emptyTables
    (.binary "GenericConstitutionalDependence" "missing" "a") 0).cost = 53 := by native_decide
example : (derivedAssertionEvidenceCosted #[`w] #[`a, `b] emptyTables
    (.binary "Categorizes" "missing" "a") 0).cost = 55 := by native_decide
example : (derivedAssertionEvidenceCosted #[`w] #[`a, `b] emptyTables
    (.ternary "IsCompletelyCoveredBy" "missing" "a" "a") 0).cost = 47 := by native_decide
example : (derivedAssertionEvidenceCosted #[`w] #[`a, `b] emptyTables
    (.ternary "IsPartitionedInto" "missing" "a" "a") 0).cost = 49 := by native_decide
example : (derivedAssertionEvidenceCosted #[`w] #[`a, `b] emptyTables
    (.quaternary "IndividualFunctionalDependence" "missing" "a" "a" "a") 0).cost = 59 := by native_decide
example : (derivedAssertionEvidenceCosted #[`w] #[`a, `b] emptyTables
    (.quaternary "ComponentOf" "missing" "a" "a" "a") 0).cost = 61 := by native_decide
example : (derivedAssertionEvidenceCosted #[`w] #[`a, `b] emptyTables
    (.quaternary "Constitution" "missing" "a" "a" "a") 0).cost = 63 := by native_decide

-- NonEmptySet has constant required-missing text but searches for an
-- incoming membership witness in its evidence row.
private def nonemptyFact : NamedDerivedFact := .unary "NonEmptySet" "a"
private def namedFacts : Array NamedScopedFact := #[.derived nonemptyFact .everywhere]
private def scopedFacts : Array ScopedCompiledFact := #[.derived (fun _ => "unused") .everywhere]
private def failure : FailedDerivedAssertion :=
  FailedDerivedAssertion.mk nonemptyFact .everywhere 0 true

example : (derivedAssertionRequiredMissingCosted #[`w] #[`a, `b] emptyTables nonemptyFact 0).cost =
    46 := by native_decide
example : (derivedAssertionEvidenceCosted #[`w] #[`a, `b] emptyTables nonemptyFact 0).cost =
    82 := by native_decide

-- Selection costs 76. The report costs 166: 46 required-missing operations,
-- 82 evidence operations, nine for suggestion selection, 23 for common
-- text/output control, and six to copy its two evidence rows.
example : (firstDerivedAssertionFailureCosted #[`w] #[`a, `b]
    namedFacts scopedFacts emptyTables).cost = 76 := by native_decide
example : (renderDerivedAssertionFailureCosted #[`w] #[`a, `b] emptyTables failure).cost =
    166 := by native_decide
example : (renderDerivedAssertionFailureCosted #[`w] #[`a, `b] emptyTables failure).value =
    renderDerivedAssertionFailureSpec #[`w] #[`a, `b] emptyTables failure :=
  renderDerivedAssertionFailureCosted_value _ _ _ _

-- Budget zero still constructs the report. Each retained row then adds
-- four copy operations. Six rows exhaust this report; larger budgets do
-- not change the value or count.
example : (derivedAssertionFailureBudgetedCosted 0 #[`w] #[`a, `b]
    namedFacts scopedFacts emptyTables).cost = 247 := by native_decide
example : (derivedAssertionFailureBudgetedCosted 0 #[`w] #[`a, `b]
    namedFacts scopedFacts emptyTables).value =
    some ((renderDerivedAssertionFailureSpec #[`w] #[`a, `b] emptyTables failure).extract 0 0) := by native_decide
example : (derivedAssertionFailureBudgetedCosted 1 #[`w] #[`a, `b]
    namedFacts scopedFacts emptyTables).cost = 251 := by native_decide
example : (derivedAssertionFailureBudgetedCosted 1 #[`w] #[`a, `b]
    namedFacts scopedFacts emptyTables).value =
    some ((renderDerivedAssertionFailureSpec #[`w] #[`a, `b] emptyTables failure).extract 0 1) := by native_decide
example : (derivedAssertionFailureBudgetedCosted 3 #[`w] #[`a, `b]
    namedFacts scopedFacts emptyTables).cost = 259 := by native_decide
example : (derivedAssertionFailureBudgetedCosted 3 #[`w] #[`a, `b]
    namedFacts scopedFacts emptyTables).value =
    some ((renderDerivedAssertionFailureSpec #[`w] #[`a, `b] emptyTables failure).extract 0 3) := by native_decide
example : (derivedAssertionFailureBudgetedCosted 4 #[`w] #[`a, `b]
    namedFacts scopedFacts emptyTables).cost = 263 := by native_decide
example : (derivedAssertionFailureBudgetedCosted 4 #[`w] #[`a, `b]
    namedFacts scopedFacts emptyTables).value =
    some ((renderDerivedAssertionFailureSpec #[`w] #[`a, `b] emptyTables failure).extract 0 4) := by native_decide
example : (derivedAssertionFailureBudgetedCosted 5 #[`w] #[`a, `b]
    namedFacts scopedFacts emptyTables).cost = 267 := by native_decide
example : (derivedAssertionFailureBudgetedCosted 5 #[`w] #[`a, `b]
    namedFacts scopedFacts emptyTables).value =
    some ((renderDerivedAssertionFailureSpec #[`w] #[`a, `b] emptyTables failure).extract 0 5) := by native_decide
example : (derivedAssertionFailureBudgetedCosted 6 #[`w] #[`a, `b]
    namedFacts scopedFacts emptyTables).cost = 271 := by native_decide
example : (derivedAssertionFailureBudgetedCosted 6 #[`w] #[`a, `b]
    namedFacts scopedFacts emptyTables).value =
    some ((renderDerivedAssertionFailureSpec #[`w] #[`a, `b] emptyTables failure).extract 0 6) := by native_decide
example : (derivedAssertionFailureBudgetedCosted 9 #[`w] #[`a, `b]
    namedFacts scopedFacts emptyTables).cost = 271 := by native_decide
example : (derivedAssertionFailureBudgetedCosted 9 #[`w] #[`a, `b]
    namedFacts scopedFacts emptyTables).value =
    some ((renderDerivedAssertionFailureSpec #[`w] #[`a, `b] emptyTables failure).extract 0 9) := by native_decide
example : (derivedAssertionFailureBudgetedCosted 100 #[`w] #[`a, `b]
    namedFacts scopedFacts emptyTables).cost = 271 := by native_decide
example : (derivedAssertionFailureBudgetedCosted 100 #[`w] #[`a, `b]
    namedFacts scopedFacts emptyTables).value =
    some ((renderDerivedAssertionFailureSpec #[`w] #[`a, `b] emptyTables failure).extract 0 100) := by native_decide

example : (derivedAssertionFailureCosted #[`w] #[`a, `b]
    namedFacts scopedFacts emptyTables).cost = 271 := by native_decide
example : (derivedAssertionAnalysisCosted #[`w] #[`a, `b]
    namedFacts scopedFacts emptyTables).cost = 272 := by native_decide

-- No assertion means no report or prefix copy. The UI fallback adds its
-- one-row construction only after selection returns none.
example : derivedAssertionFailureCosted #[`w] #[`a, `b] #[] #[] emptyTables =
    ⟨none, 1⟩ := by native_decide
example : (derivedAssertionAnalysisCosted #[`w] #[`a, `b] #[] #[] emptyTables).cost =
    5 := by native_decide
example : derivedAssertionFailureCosted #[] #[`a, `b] namedFacts scopedFacts emptyTables =
    ⟨none, 11⟩ := by native_decide

example (budget : Nat) (worlds things : Array Name) (named : Array NamedScopedFact)
    (resolved : Array ScopedCompiledFact) (tables : FactTables) :
    ((derivedAssertionFailureBudgetedCosted budget worlds things named resolved tables).value.getD #[]).size ≤ budget :=
  derivedAssertionFailureBudgetedCosted_size_le budget worlds things named resolved tables

example (budget : Nat) (worlds things : Array Name) (named : Array NamedScopedFact)
    (resolved : Array ScopedCompiledFact) (tables : FactTables) :
    (derivedAssertionFailureBudgetedCosted budget worlds things named resolved tables).cost ≤
      derivedAssertionFailureCostBound worlds.size things.size named.size
        ((derivedAssertionFailureBudgetedCosted budget worlds things named resolved tables).value.getD #[]).size tables :=
  derivedAssertionFailureBudgetedCosted_cost_le budget worlds things named resolved tables

end LeanUfo.Test.Complexity.DerivedReportComposition
