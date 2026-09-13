import LeanUfo.UFO.DSL.Complexity.Certification
import LeanUfo.UFO.DSL.Guarantees
import Lean.Util.CollectAxioms

/-!
# Source-linked field and registry composition

These applications use the real axiom-73 checker and its semantic axiom-75
prerequisite on the model reconstructed from a successful source compilation.
Root and extension cases permit every observed proof outcome. Separate exact
tests check that a root planner performs no work and an empty registry runs
no field callbacks. Native execution and retry traces are tested in
`Test/Certificates/Execution.lean`.
The imported public guarantees and workflow bounds are also audited below for
unexpected axioms. This keeps native proof trust out of the general theorems.
-/

namespace LeanUfo.Test.Complexity.Certification

open LeanUfo.UFO.DSL
open Complexity Complexity.Certification CertificateChecking

run_cmd do
  for theoremName in #[``sourceWorkflow_bound, ``sourceWorkflow_scalar_bound,
      ``sourceWorkflow_fixed_data_bound, ``sourceWorkflowScalarBound_mono,
      ``ScopedCompiledFact.derived_at_expands_to_singleton,
      ``CertificateReuse.certificateReuseSource_fresh_none] do
    for axiomName in ← Lean.collectAxioms theoremName do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "{theoremName} uses unexpected axiom {axiomName}"

private theorem registered73 (input : CompiledInput) : input.Registered Checker.checkAx73Costed := by
  refine ⟨.of (fun _ => Checker.checkAx73Costed input.model)
    (Checker.checkAx73Costed_cost_le input.model), ?_, rfl⟩
  simp [Checker.checkAxioms4BoundedRegistry]

private theorem registered75 (input : CompiledInput) : input.Registered Checker.checkAx75Costed := by
  refine ⟨.of (fun _ => Checker.checkAx75Costed input.model)
    (Checker.checkAx75Costed_cost_le input.model), ?_, rfl⟩
  simp [Checker.checkAxioms4BoundedRegistry]

example (input : CompiledInput) (fresh : Bool) (field : CertField) :
    plannerCosted input none fresh field = Costed.pure none := rfl

example (input : CompiledInput) : commonSize input none = input.inputSize := by
  simp [commonSize, parentInput]

example (input : CompiledInput) (fresh : Bool)
    (checkedOutcomes : Bool → Option Lean.Name → ProofOutcome Unit)
    (semanticOutcomes : Bool → Bool → ProofOutcome Unit) :
    (fieldCosted input none fresh ⟨"ax73", "True"⟩ Checker.checkAx73Costed
      (fun _ => Checker.checkAx75Costed) checkedOutcomes semanticOutcomes).cost ≤
      124 * input.inputSize ^ 4 + 11041 * input.inputSize +
        8 * (54896424 * input.inputSize ^ 16) + 55 := by
  have bound := fieldCosted_bound input none fresh ⟨"ax73", "True"⟩ Checker.checkAx73Costed
    (fun _ => Checker.checkAx75Costed) checkedOutcomes semanticOutcomes
    (registered73 input) (registered73 input) (fun _ => registered75 input)
  simp only [commonSize, parentInput, Nat.max_self] at bound
  omega

example (input : CompiledInput) (parent : ParentInput) (fresh : Bool)
    (checkedOutcomes : Bool → Option Lean.Name → ProofOutcome Unit)
    (semanticOutcomes : Bool → Bool → ProofOutcome Unit) :
    (fieldCosted input (some parent) fresh ⟨"ax73", "True"⟩ Checker.checkAx73Costed
      (fun _ => Checker.checkAx75Costed) checkedOutcomes semanticOutcomes).cost ≤
      124 * input.inputSize ^ 4 + 18 * input.inputSize + 11023 * parent.input.inputSize +
        8 * (54896424 * (max input.inputSize parent.input.inputSize) ^ 16) + 55 :=
  fieldCosted_bound input (some parent) fresh ⟨"ax73", "True"⟩ Checker.checkAx73Costed
    (fun _ => Checker.checkAx75Costed) checkedOutcomes semanticOutcomes
    (registered73 input) (registered73 parent.input) (fun _ => registered75 input)

example (input : CompiledInput) (parent : Option ParentInput) (fresh : Bool)
    (checks : CertField → FiniteModel4 → Costed Bool)
    (semanticChecks : CertField → NativeCall → FiniteModel4 → Costed Bool)
    (checkedOutcomes : CertField → Bool → Option Lean.Name → ProofOutcome Unit)
    (semanticOutcomes : CertField → Bool → Bool → ProofOutcome Unit) :
    registryCosted input parent fresh #[] checks semanticChecks checkedOutcomes semanticOutcomes =
      ⟨{}, 2⟩ := rfl

-- A one-field registry uses the real generated axiom-73 proof forms. Its
-- upper bound also covers native errors and either declaration mode failing.
example (input : CompiledInput) (parent : Option ParentInput) (fresh : Bool)
    (checkedOutcomes : CertField → Bool → Option Lean.Name → ProofOutcome Unit)
    (semanticOutcomes : CertField → Bool → Bool → ProofOutcome Unit) :
    (registryCosted input parent fresh #[⟨"ax73", "True"⟩]
      (fun _ => Checker.checkAx73Costed) (fun _ _ => Checker.checkAx75Costed)
      checkedOutcomes semanticOutcomes).cost ≤
      124 * input.inputSize ^ 4 + 18 * input.inputSize +
        11023 * (parentInput input parent).inputSize +
        8 * (54896424 * commonSize input parent ^ 16) + 64 := by
  have bound := registryCosted_bound input parent fresh #[⟨"ax73", "True"⟩]
    (fun _ => Checker.checkAx73Costed) (fun _ _ => Checker.checkAx75Costed)
    checkedOutcomes semanticOutcomes (fun _ => registered73 input)
    (fun _ => registered73 (parentInput input parent)) (fun _ _ => registered75 input)
  have size : (#[⟨"ax73", "True"⟩] : Array CertField).size = 1 := rfl
  rw [size, Nat.one_mul] at bound
  omega

example {C P R C' P' R' : Nat}
    (child : C ≤ C') (parent : P ≤ P') (fields : R ≤ R') :
    2 + R * (124 * C ^ 4 + 18 * C + 11023 * P +
      8 * (54896424 * (max C P) ^ 16) + 62) ≤
    2 + R' * (124 * C' ^ 4 + 18 * C' + 11023 * P' +
      8 * (54896424 * (max C' P') ^ 16) + 62) :=
  registryBound_mono child parent fields

private def stopped : RegistryResult Nat :=
  { completed := #["ax1"], actualReuse := #[("ax1", none)], failedField? := some 2 }

example :
    (reportAfterRegistryCosted stopped (fun _ => Costed.tick #["failure"] 100)).cost = 101 := by
  decide

example :
    (reportAfterRegistryCosted ({} : RegistryResult Nat)
      (fun _ => Costed.tick #["must not run"] 1000000)).cost = 1 := by decide

-- The production selector invokes only the recorded failed field, once, and
-- retains the completed/reuse prefix unchanged in the returned result.
example :
    (reportAfterRegistry (m := StateM (Array Nat)) (fun _ => pure ()) stopped (fun field => do
      modify (·.push field)
      pure #["failure"])).run #[] =
      (.failed stopped 2 #["failure"], #[2]) := rfl

example :
    (reportAfterRegistry (m := StateM (Array Nat)) (fun _ => pure ()) ({} : RegistryResult Nat)
      (fun field => do
        modify (·.push field)
        pure #["must not run"])).run #[] = (.checked {}, #[]) := rfl

example (input : CompiledInput) (parent : Option ParentInput) (fresh : Bool)
    (worldNames thingNames : Array Lean.Name)
    (checks : CertField → FiniteModel4 → Costed Bool)
    (semanticChecks counterexampleChecks : CertField → NativeCall → FiniteModel4 → Costed Bool)
    (checkedOutcomes : CertField → Bool → Option Lean.Name → ProofOutcome Unit)
    (semanticOutcomes : CertField → Bool → Bool → ProofOutcome Unit)
    (counterexampleOutcomes : CertField → ProofOutcome Unit) (errors : CertField → Array String) :
    registryAndReportCosted input parent worldNames thingNames fresh #[] checks semanticChecks
      counterexampleChecks checkedOutcomes semanticOutcomes counterexampleOutcomes errors =
      ⟨.checked {}, 3⟩ := rfl

example : runAfterAssertionsCosted (Costed.tick (some #["assertion failure"]) 10) false
    derivedAssertionFailureReportCosted (fun _ => Costed.tick (7 : Nat) 100) =
      ⟨.failed #["assertion failure"], 13⟩ := rfl

example : (runAfterAssertionsCosted (Costed.tick none 10) true
    derivedAssertionFailureReportCosted (fun _ => Costed.tick (7 : Nat) 100)).cost = 16 := rfl

example : runAfterAssertionsCosted (Costed.tick none 10) false
    derivedAssertionFailureReportCosted (fun _ => Costed.tick (7 : Nat) 100) =
      ⟨.checked 7, 112⟩ := rfl

private def assertionTrace (saved : Option (Array String)) (failed : Bool) :=
  (runAfterAssertions (m := StateM (Array Nat)) (fun _ => pure ())
    (fun _ => do modify (·.push 1); pure saved)
    (fun _ => do modify (·.push 2); pure failed)
    (fun _ => do modify (·.push 3); pure #["failure"])
    (fun _ => do modify (·.push 4); pure (7 : Nat))).run #[]

example : (assertionTrace (some #["saved"]) false).2 = #[1, 3] := rfl
example : (assertionTrace none true).2 = #[1, 2, 3] := rfl
example : (assertionTrace none false).2 = #[1, 2, 4] := rfl

-- Apply the whole workflow theorem, including source compilation and derived
-- assertions, to a real axiom-75 request. Proof failures may select diagnostics.
example (input : CompiledInput) (parent : Option ParentInput) (fresh derivedFailed : Bool)
    (checkedOutcomes : CertField → Bool → Option Lean.Name → ProofOutcome Unit)
    (semanticOutcomes : CertField → Bool → Bool → ProofOutcome Unit)
    (counterexampleOutcomes : CertField → ProofOutcome Unit) (errors : CertField → Array String) :
    compilerOperationalCost input.source +
      (postCompileCosted input parent fresh derivedFailed #[⟨"ax75", "True"⟩]
        (fun _ => Checker.checkAx75Costed) (fun _ _ => Checker.checkAx75Costed)
        (fun _ _ => Checker.checkAx75Costed) checkedOutcomes semanticOutcomes counterexampleOutcomes errors).cost ≤
      548981572 * commonSize input parent ^ 16 +
      match (registryCosted input parent fresh #[⟨"ax75", "True"⟩]
          (fun _ => Checker.checkAx75Costed) (fun _ _ => Checker.checkAx75Costed)
          checkedOutcomes semanticOutcomes).value.failedField? with
      | none => 0
      | some field => failureReportBound input (namesFromStrings input.source.worlds)
          (namesFromStrings input.source.things) field (errors field) :=
  sourceWorkflow_scalar_bound input parent fresh derivedFailed #[⟨"ax75", "True"⟩]
    (fun _ => Checker.checkAx75Costed) (fun _ _ => Checker.checkAx75Costed)
    (fun _ _ => Checker.checkAx75Costed) checkedOutcomes semanticOutcomes counterexampleOutcomes errors
    (fun _ => registered75 input) (fun _ => registered75 (parentInput input parent))
    (fun _ _ => registered75 input) (fun _ _ => registered75 input)

end LeanUfo.Test.Complexity.Certification
