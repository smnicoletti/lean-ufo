import LeanUfo.UFO.DSL.Complexity

/-!
# Generic-report composition regressions

The general tests apply the size bounds to executed report functions. Exact
cases cover full assignment search, first and later failures, empty domains,
zero output budget, and text construction before a retention check. No test
requires exact counts to increase when model contents change.
-/

namespace LeanUfo.Test.Complexity.Reports

open LeanUfo.UFO.DSL LeanUfo.UFO.DSL.Complexity
open private DiagFormula DiagFormula.nodeCount DiagFormula.eqThing DiagFormula.not DiagFormula.or
  DiagFormula.atom DiagFormula.forallThing DiagFormula.forallVars DiagFormula.stripForalls
  DiagAtom.unary DiagVar DiagVar.mk DiagVarKind.thing DiagVarKind.world
  genericDiagnosticWitnessesCosted genericDiagnosticVisitCosted failingAtomsCosted
  minimizeFailureCosted MinimizedFailure.formula diagnosticFormula? diagnosticFormulaRegistry
  from LeanUfo.UFO.DSL.Diagnostic.AxiomAnalysis

private def worlds : Array Lean.Name := #[`w]
private def things : Array Lean.Name := #[`a, `b, `c]
private def vars : Array DiagVar := #[DiagVar.mk "x" DiagVarKind.thing]
private def equality : DiagFormula := DiagFormula.eqThing "x" "x"
private def firstFailure : DiagFormula := DiagFormula.not (DiagFormula.eqThing "x" "z")
private def laterFailure : DiagFormula := DiagFormula.eqThing "x" "z"

-- Initialization costs two. A zero budget adds only the first stop test (two).
example : (genericDiagnosticWitnessesCosted 0 worlds things #[] {} vars equality).cost = 4 :=
  by native_decide
-- An empty domain adds six outer-loop operations, but executes no body visit.
example : (genericDiagnosticWitnessesCosted 128 #[] things #[] {}
    #[DiagVar.mk "w" DiagVarKind.world] equality).cost = 8 := by native_decide
-- Each true visit costs 13. Each assignment adds four leaf operations,
-- two for the binding/index, and three for its loop: 2+6+3*(13+4+2+3)=74.
example : (genericDiagnosticWitnessesCosted 128 worlds things #[] {} vars equality).cost = 74 :=
  by native_decide
example : (genericDiagnosticWitnessesCosted 128 worlds things #[] {} vars equality).value = #[] :=
  by native_decide

-- Missing z resolves to zero. These reports therefore fail at a and b respectively.
example : (genericDiagnosticWitnessesCosted 1 worlds things #[] {} vars firstFailure).cost = 167 :=
  by native_decide
example : (genericDiagnosticWitnessesCosted 1 worlds things #[] {} vars laterFailure).cost = 134 :=
  by native_decide
example : (genericDiagnosticWitnessesCosted 1 worlds things #[] {} vars firstFailure).value =
    #["Counterexample assignment: x = a."] := by native_decide
example : (genericDiagnosticWitnessesCosted 1 worlds things #[] {} vars laterFailure).value =
    #["Counterexample assignment: x = b."] := by native_decide

-- A direct visit constructs its text even with no room. Retaining one row
-- adds its write and emission, so the two counts differ by exactly two.
example : (genericDiagnosticVisitCosted 0 worlds things #[] {} vars firstFailure
    #[] #[("x", 0)]).cost = 145 := by native_decide
example : (genericDiagnosticVisitCosted 1 worlds things #[] {} vars firstFailure
    #[] #[("x", 0)]).cost = 147 := by native_decide
example : (genericDiagnosticVisitCosted 0 worlds things #[] {} vars firstFailure
    #[] #[("x", 0)]).value.size = 0 := by native_decide
example : (genericDiagnosticVisitCosted 1 worlds things #[] {} vars firstFailure
    #[] #[("x", 0)]).value.size = 1 := by native_decide

-- Failed equalities have no relation atom to emit, but discovery still evaluates them.
example : (failingAtomsCosted 1 3 {} #[("x", 0)]
    (DiagFormula.or firstFailure firstFailure)).cost = 67 := by native_decide
example : (failingAtomsCosted 1 3 {} #[("x", 0)]
    (DiagFormula.or firstFailure firstFailure)).value.size = 0 := by native_decide

private def quantifiedAtom : DiagFormula := DiagFormula.forallThing "x"
  (DiagFormula.atom (DiagAtom.unary .endurant "x" "w"))
example : (failingAtomsCosted 1 3 {} #[] quantifiedAtom).cost = 92 := by native_decide
example : (failingAtomsCosted 1 3 {} #[] quantifiedAtom).value.size = 3 := by native_decide

example (W T : Nat) (tables : FactTables) (env : Array (String × Nat)) (formula : DiagFormula) :
    diagnosticQuantifierDepth (MinimizedFailure.formula
      (minimizeFailureCosted W T tables env formula).value) ≤ diagnosticQuantifierDepth formula :=
  diagnosticFailureMinimize_depth_le W T tables env formula

example (W T : Nat) (tables : FactTables) (env : Array (String × Nat)) (formula : DiagFormula) :
    (failingAtomsCosted W T tables env formula).value.size ≤
      DiagFormula.nodeCount formula * (W + T + 1) ^ diagnosticQuantifierDepth formula :=
  diagnosticFailingAtoms_size_le W T tables env formula

example (budget : Nat) (worldNames thingNames : Array Lean.Name) (facts : Array NamedScopedFact)
    (tables : FactTables) (vars : Array DiagVar) (body : DiagFormula)
    (out : Array String) (env : Array (String × Nat)) (V : Nat)
    (hVars : vars.size ≤ V) (hEnv : env.size ≤ V) :
    (genericDiagnosticVisitCosted budget worldNames thingNames facts tables vars body out env).cost ≤
      diagnosticGenericVisitBound worldNames.size thingNames.size tables facts.size V
        (DiagFormula.nodeCount body) (diagnosticQuantifierDepth body) :=
  diagnosticGenericVisit_cost_le_size budget worldNames thingNames facts tables vars body out env V hVars hEnv

example (budget : Nat) (worldNames thingNames : Array Lean.Name) (facts : Array NamedScopedFact)
    (tables : FactTables) (vars : Array DiagVar) (body : DiagFormula) :
    let V := vars.size
    let P := diagnosticGenericVisitBound worldNames.size thingNames.size tables
      facts.size (2 * V) (DiagFormula.nodeCount body) (diagnosticQuantifierDepth body)
    (genericDiagnosticWitnessesCosted budget worldNames thingNames facts tables vars body).cost ≤
      (P + 11 * (V + 1)) * (worldNames.size + thingNames.size + 1)^V + 2 :=
  diagnosticGenericWitnesses_cost_le_size budget worldNames thingNames facts tables vars body

example (budget : Nat) (worldNames thingNames : Array Lean.Name) (facts : Array NamedScopedFact)
    (tables : FactTables) (field : String) (formula : DiagFormula)
    (hGeneric : field ∉ ["ax68", "ax71", "ax73", "ax78", "ax79", "ax99"])
    (hFormula : diagnosticFormula? field = some formula) :
    (diagnosticWitnessesBudgetedCosted budget worldNames thingNames facts tables field).cost ≤
      diagnosticGenericReportBound worldNames.size thingNames.size tables facts.size
        (DiagFormula.forallVars formula).size (DiagFormula.nodeCount (DiagFormula.stripForalls formula))
        (diagnosticQuantifierDepth (DiagFormula.stripForalls formula)) diagnosticFormulaRegistry.size
        (diagnosticWitnessesBudgeted budget worldNames thingNames facts tables field).size :=
  diagnosticGenericReport_cost_le_size budget worldNames thingNames facts tables field formula hGeneric hFormula

example {W W' T T' F F' V V' s s' q q' r r' e e' : Nat} {tables tables' : FactTables}
    (hW : W ≤ W') (hT : T ≤ T') (hF : F ≤ F') (hV : V ≤ V')
    (hs : s ≤ s') (hq : q ≤ q') (hr : r ≤ r') (he : e ≤ e')
    (hDerived : tables.derivedProps.size ≤ tables'.derivedProps.size) :
    diagnosticGenericReportBound W T tables F V s q r e ≤
      diagnosticGenericReportBound W' T' tables' F' V' s' q' r' e' :=
  diagnosticGenericReportBound_mono hW hT hF hV hs hq hr he hDerived

example : (diagnosticWitnessesBudgetedCosted 0 worlds things #[] {} "ax1").cost = 47 :=
  by native_decide
example : (diagnosticWitnessesBudgetedCosted 1 worlds things #[] {} "ax1").cost = 1018 :=
  by native_decide

-- The frontend wrapper must not turn an unconfirmed proof into a semantic
-- counterexample. These counts use an unknown field, so no analyzer runs.
private def unconfirmed (errors : Array String) :=
  certificationFailureReportCosted worlds things #[] {} "unknown" true errors

-- Fixed work is 15. Each nonmatching message adds nine classification,
-- five row-production, and three copy operations.
example : (unconfirmed #[]).cost = 15 := by native_decide
example : (unconfirmed #["bad"]).cost = 32 := by native_decide
example : (unconfirmed #["bad", "bad"]).cost = 49 := by native_decide
example : (unconfirmed #["bad"]).value =
    #["No counterexample proof was found for unknown.",
      "The counterexample probe failed without a recognized timeout. This should be treated as an unclassified probe failure, not as a semantic counterexample.",
      "Counterexample probe error: bad"] := by native_decide

-- Timeout classification stops at the first matching message. Each later
-- substring requires one more test. A recognized timeout suppresses all errors.
example : (unconfirmed #["HEARTBEAT", "bad"]).cost = 22 := by native_decide
example : (unconfirmed #["TIMEOUT"]).cost = 23 := by native_decide
example : (unconfirmed #["maximum number of steps"]).cost = 24 := by native_decide
example : (unconfirmed #["bad", "TIMEOUT", "bad"]).cost = 32 := by native_decide
example : (unconfirmed #["bad", "TIMEOUT", "bad"]).value.size = 2 := by native_decide

-- Confirmed probes and unconfirmed axiom 99 skip error classification.
example : (certificationFailureReportCosted worlds things #[] {} "unknown" false
    #["HEARTBEAT"]).cost =
      (diagnosticWitnessesBudgetedCosted 128 worlds things #[] {} "unknown").cost +
        3 * (diagnosticWitnesses worlds things #[] {} "unknown").size + 8 := by native_decide
example : (certificationFailureReportCosted worlds things #[] {} "ax99" true
    #["HEARTBEAT"]).cost =
      (diagnosticWitnessesBudgetedCosted 128 worlds things #[] {} "ax99").cost +
        3 * (diagnosticWitnesses worlds things #[] {} "ax99").size + 10 := by native_decide
example : (certificationFailureReportCosted worlds things #[] {} "ax68" true #[]).cost =
    (ax68ClosureAnalysisCosted worlds things {}).cost +
      3 * (ax68ClosureAnalysis worlds things {}).size + 15 := by native_decide

end LeanUfo.Test.Complexity.Reports
