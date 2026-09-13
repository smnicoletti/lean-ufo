import LeanUfo.UFO.DSL.Diagnostic.AxiomAnalysis
import LeanUfo.UFO.DSL.Diagnostic.DerivedAssertions

/-!
# Source-level diagnostic entry points

`AxiomAnalysis` explains failed registered axioms. `DerivedAssertions` checks
user-written derived facts and explains their failures before certification.
`certificationFailureReportCosted` selects the report after the frontend's
proof probe. It charges the selected analyzer, timeout classification, and
surrounding rows. The proof probe itself is outside the operational model.
-/

namespace LeanUfo.UFO.DSL
open Complexity

/-- Only axiom 68 needs the closure precheck. Other fields pay for the field
comparison and Boolean branch, without searching for an ultimate bearer. -/
def certificationFieldPrecheckCosted (W T : Nat) (tables : FactTables) (field : String) :
    Costed Bool :=
  (Costed.tick (field == "ax68")).andThen fun _ => hasAx68ClosureFailureCosted W T tables

/-- Text primitives have unit cost here. The bound excludes the number of
characters inspected by lowercase conversion and substring search. -/
private def timeoutMessageCosted (message : String) : Costed Bool := do
  let lower ← Costed.tick message.toLower
  ((Costed.tick (lower.contains "heartbeat")).orElse fun _ =>
    Costed.tick (lower.contains "timeout")).orElse fun _ =>
      Costed.tick (lower.contains "maximum number of")

private def probeTimeoutCosted (errors : Array String) : Costed Bool :=
  anyArrayCosted errors timeoutMessageCosted

/-- Each error adds one text concatenation, one array write, and one emitted
row, in addition to the fold's read and iteration. -/
private def probeErrorRowsCosted (errors : Array String) : Costed (Array String) := do
  let empty ← Costed.tick (#[] : Array String)
  Costed.foldArray errors empty fun rows message =>
    Costed.tick (rows.push s!"Counterexample probe error: {message}") 3

/-- Only a confirmed probe permits the semantic-counterexample wording.
An unconfirmed axiom 99 instead explains the finite witness limitation.
Timeouts suppress raw probe errors. Axiom 68 can still add closure evidence.

The selected analyzer runs once. Counts compose its returned cost with branch
tests and row construction, following Niu et al.'s compositional cost method
(POPL 2022, doi:10.1145/3498670). Output copying costs three operations per row.
The 128-row witness limit does not truncate the surrounding probe messages. -/
def certificationFailureReportCosted
    (worldNames thingNames : Array Lean.Name) (namedFacts : Array NamedScopedFact)
    (tables : FactTables) (field : String) (probeFailed : Bool)
    (errors : Array String) : Costed (Array String) := do
  if ← Costed.tick probeFailed then
    if ← Costed.tick (field == "ax99") 2 then
      let base ← Costed.tick #[
        "Ax99 did not produce a confirmed semantic counterexample.",
        "This axiom contains an existential product-family witness. The reflective checker can only inspect product-family witnesses that are explicitly stored in the finite model.",
        "When the required witness data is missing, `checkAx99 = false` means that the finite representation is incomplete for this axiom; it does not by itself prove that the semantic axiom is false."
      ] 7
      let rows ← diagnosticWitnessesBudgetedCosted 128 worldNames thingNames namedFacts tables field
      Costed.appendArray base rows
    else
      let timedOut ← probeTimeoutCosted errors
      let reason ← Costed.tick
        (if timedOut then
          "The counterexample probe reported a heartbeat/timeout-style failure. This is an operational probe limit, not a semantic counterexample."
        else
          "The counterexample probe failed without a recognized timeout. This should be treated as an unclassified probe failure, not as a semantic counterexample.")
      let base ← Costed.tick #[s!"No counterexample proof was found for {field}.", reason] 7
      let probeErrors ← Costed.charge 1
        (if timedOut then Costed.tick #[] else probeErrorRowsCosted errors)
      let rows ← Costed.appendArray base probeErrors
      if ← Costed.tick (field == "ax68") 2 then
        let closure ← ax68ClosureAnalysisCosted worldNames thingNames tables
        Costed.appendArray rows closure
      else
        Costed.pure rows
  else
    let base ← Costed.tick #[
      s!"A finite counterexample was confirmed for {field}.",
      "Lean successfully proved the negation of this axiom for the generated finite model, so this is a semantic model failure rather than a counterexample-probe limit."
    ] 7
    let rows ← diagnosticWitnessesBudgetedCosted 128 worldNames thingNames namedFacts tables field
    Costed.appendArray base rows

end LeanUfo.UFO.DSL
