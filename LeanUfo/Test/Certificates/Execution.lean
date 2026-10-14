import LeanUfo.UFO.DSL.Certificate.Execution
import LeanUfo.UFO.DSL.Compiler.VerifiedModel
import LeanUfo.UFO.DSL.Complexity.Frontend
import LeanUfo.UFO.DSL.Syntax

/-!
# Explicit native proof preparation

These tests exercise the executor and frontend message capture. Small counts
and traces check stopping at the first native error. Generated declarations
use proofs returned by Lean's native API, including a parent reuse proof.
They contain no registered native-decision tactic to execute a second time.
-/

namespace LeanUfo.Test.Certificates.Execution

open LeanUfo.UFO.DSL
open CertificateChecking
open Lean Elab Command
open private checkedAxiomProofScript from LeanUfo.UFO.DSL.Certificate.Generation
open private elabCommandStringWithReport elabTermStringWithReport
  elabTermStringStrictWithReport ElabCheckResult.failed ElabCheckResult.errors
  from LeanUfo.UFO.DSL.Syntax

private def twoRequests : ProofScript :=
  .call "" (.expect "ax75" true) (.call "" (.expect "ax79" true) (.done ""))

private def counted (firstFails secondFails : Bool) :=
  twoRequests.prepareCosted fun request =>
    let first := request == .expect "ax75" true
    let failed := if first then firstFails else secondFails
    Complexity.Costed.tick
      (if failed then (.error "failed" : Except String String) else .ok "proof")
      (if first then 10 else 20)

example : (counted false false).cost = 37 := by decide
example : (counted true false).cost = 12 := by decide
example : (counted false true).cost = 35 := by decide
example : (counted true true).cost = 12 := by decide
example : ((ProofScript.done "text").prepareCosted
    (fun _ => Complexity.Costed.tick (.error "unused" : Except String String) 100)).cost = 1 := rfl

private def preparedAttempt (nativeFailed proofFailed : Bool) :=
  Complexity.preparedProofAttemptCosted
    { script := .call "" (.expect "ax75" true) (.done ""), wrap := id }
    (fun _ => Complexity.Costed.tick
      (if nativeFailed then (.error () : Except Unit String) else .ok "proof") 10)
    proofFailed

-- Excluded proof failure changes the returned status, but not the algorithm
-- work already done. Native failure skips the completed-text node instead.
example : ∀ nativeFailed proofFailed : Bool,
    (preparedAttempt nativeFailed proofFailed).value = (nativeFailed || proofFailed) := by decide
example : ∀ nativeFailed proofFailed : Bool,
    (preparedAttempt nativeFailed proofFailed).cost = (if nativeFailed then 12 else 14) := by decide

private def observed (firstFails secondFails : Bool) :
    Except String String × Array NativeCall :=
  (twoRequests.prepare (m := StateM (Array NativeCall)) (fun _ => pure ()) fun request => do
    modify (·.push request)
    let failed := if request == .expect "ax75" true then firstFails else secondFails
    pure (if failed then .error "failed" else .ok "proof")).run #[]

example : ∀ firstFails secondFails : Bool,
    (observed firstFails secondFails).2 =
      if firstFails then #[.expect "ax75" true]
      else #[.expect "ax75" true, .expect "ax79" true] := by native_decide

private def preparedChecked (reuse nativeTrialFails proofTrialFails proofDeclarationFails : Bool) :=
  Complexity.preparedCheckedAttemptsCosted ⟨"ax75", "True"⟩
    (fun _ => Complexity.Costed.tick (if reuse then some `Parent else none) 7)
    (fun declaration parent request => Complexity.Costed.map
      (fun _ => if !declaration && parent.isSome && nativeTrialFails then
          (.error () : Except Unit String) else .ok "proof")
      (Complexity.nativeRequestCosted request
        (fun _ => Complexity.Costed.tick true 10)
        (fun _ => Complexity.Costed.tick true 20)))
    (fun declaration parent => parent.isSome &&
      (if declaration then proofDeclarationFails else proofTrialFails))

-- The planner costs seven, fresh preparation fifteen, and reuse preparation
-- thirty-five. Native failure during reuse costs thirty-three and skips the
-- declaration. Failure in the subsequent proof retains the preparation cost.
example : preparedChecked false false false false = ⟨.checked none, 39⟩ := by decide
example : preparedChecked true false false false = ⟨.checked (some `Parent), 79⟩ := by decide
example : preparedChecked true true false false = ⟨.checked none, 75⟩ := by decide
example : preparedChecked true false true false = ⟨.checked none, 77⟩ := by decide
example : preparedChecked true false false true = ⟨.checked none, 112⟩ := by decide

def data : FiniteModel4 :=
  compileVerifiedModel { worldCount := 1, thingCount := 1 }
    (by decide) (by decide) (by decide)

private def declarePrepared (name target : String) (script : ProofScript) : CommandElabM Unit := do
  let result ← liftTermElabM <| prepareProofScript script
  let body ← match result with
    | .ok body => pure body
    | .error error => throw error
  if body.contains "(by native_decide" then
    throwError "prepared proof still contains a registered native tactic"
  let indented := String.intercalate "\n" ((body.splitOn "\n").map ("  " ++ ·))
  let source := s!"theorem {name} : {target} := by\n{indented}"
  match Parser.runParserCategory (← getEnv) `command source with
  | .ok stx => elabCommand stx
  | .error error => throwError "prepared proof did not parse: {error}"

run_cmd do
  declarePrepared "checked_ax75" "LeanUfo.UFO.DSL.Checker.checkAx75 data = true"
    (checkedAxiomProofScript ⟨"ax75", "True"⟩ none)

namespace Parent

def data : FiniteModel4 := LeanUfo.Test.Certificates.Execution.data

run_cmd do
  declarePrepared "checked_ax75" "LeanUfo.UFO.DSL.Checker.checkAx75 data = true"
    (checkedAxiomProofScript ⟨"ax75", "True"⟩ none)

end Parent

run_cmd do
  declarePrepared "checkedReuse" "LeanUfo.UFO.DSL.Checker.checkAx75 data = true"
    (checkedAxiomProofScript ⟨"ax75", "True"⟩ (some `LeanUfo.Test.Certificates.Execution.Parent))

example : Checker.checkAx75 data = true := checked_ax75
example : Checker.checkAx75 data = true := checkedReuse

-- The false expected answer fails before the nonexistent checker is resolved.
-- A successful result here would bypass the native decision's proof obligation.
run_cmd do
  let script : ProofScript := .call "" (.expect "ax75" false)
    (.call "" (.expect "missingChecker" true) (.done ""))
  let result ← liftTermElabM <| prepareProofScript script
  match result with
  | .ok _ => throwError "native preparation accepted a false expected answer"
  | .error (.error _ message) =>
      let text ← message.toString
      unless text.contains "is false" && !text.contains "missingChecker" do
        throwError "unexpected native preparation failure: {text}"
  | .error (.internal id _) => throwError "unexpected internal exception: {id.toString}"

-- An unknown checker is an elaboration error, not a proof of either answer.
run_cmd do
  let result ← liftTermElabM <| prepareProofScript
    (.call "" (.expect "missingChecker" true) (.done ""))
  match result with
  | .ok _ => throwError "native preparation accepted an unknown checker"
  | .error (.error _ message) =>
      let text ← message.toString
      unless text.contains "missingChecker" do
        throwError "unexpected unknown-checker failure: {text}"
  | .error (.internal id _) => throwError "unexpected internal exception: {id.toString}"

-- Preparation errors must be captured before parsing the remaining text, with
-- no leaked errors that could invalidate a later fresh attempt.
run_cmd do
  let source : ProofSource := {
    script := .call "" (.expect "ax75" false)
      (.call "" (.expect "missingChecker" true) (.done ""))
    wrap := id }
  let beforeCommand := (← get).messages.toList.length
  let beforeCore := (← liftCoreM Core.getMessageLog).toList.length
  for report in [elabCommandStringWithReport, elabTermStringWithReport,
      elabTermStringStrictWithReport] do
    let result ← report (liftTermElabM <| prepareProofSource source)
    unless ElabCheckResult.failed result &&
        (ElabCheckResult.errors result).any (·.contains "is false") &&
        !(ElabCheckResult.errors result).any (·.contains "missingChecker") do
      throwError "native failure escaped the expected proof-attempt classification"
  unless (← get).messages.toList.length == beforeCommand &&
      (← liftCoreM Core.getMessageLog).toList.length == beforeCore do
    throwError "proof-attempt capture leaked native errors"

namespace Integrated

def data : FiniteModel4 := LeanUfo.Test.Certificates.Execution.data

-- Exercise the same source generators and captured executor used by Syntax,
-- including a successful trial after the captured failures above.
run_cmd do
  let field : CertField := ⟨"ax75", "True"⟩
  for parent in [none, some `LeanUfo.Test.Certificates.Execution.Parent] do
    let trial ← elabTermStringStrictWithReport (liftTermElabM <|
      prepareProofSource (checkedAxiomProofCheck field parent))
    if ElabCheckResult.failed trial then
      throwError "prepared checked trial failed: {ElabCheckResult.errors trial}"
  let declaration ← elabCommandStringWithReport (liftTermElabM <|
    prepareProofSource (checkedAxiomTheorem field
      (some `LeanUfo.Test.Certificates.Execution.Parent)))
  if ElabCheckResult.failed declaration then
    throwError "prepared checked declaration failed: {ElabCheckResult.errors declaration}"

example : Checker.checkAx75 data = true := checked_ax75

end Integrated

end LeanUfo.Test.Certificates.Execution
