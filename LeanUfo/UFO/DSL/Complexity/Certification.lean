import LeanUfo.UFO.DSL.Complexity.Theorems
import LeanUfo.UFO.DSL.Complexity.Diagnostics.Source

/-!
# Source-linked certification workflow

This module composes the source bounds with the same preparation and retry
drivers used by `Syntax.lean`. A `CompiledInput` keeps a source together with
its successful compiler result and nonempty-domain proofs. It prevents the
workflow bound from using an unrelated model or table-size assumption.

Proof-production and elaboration outcomes are observed inputs. Their work is
outside the algorithmic cost model; the native checker computations that
precede them are counted here. Resolved checker functions must satisfy full
counted registry membership on the reconstructed model. Resolution of generated
checker names and Lean's native-code machinery remain trusted boundaries.

The composition follows Niu et al.'s cost-aware semantics (POPL 2022): costs
come from executed components, and erasure discards costs without changing
their results. See `docs/dsl/complexity.md` for the machine model and exclusions.
-/

namespace LeanUfo.UFO.DSL.Complexity.Certification

open CertificateChecking
open private ax68ClosureAnalysisCostBound from LeanUfo.UFO.DSL.Diagnostic.AxiomAnalysis

/-- A successful source compilation, with exactly the domain proofs required
by the generated finite model. These fields record evidence, not extra work. -/
structure CompiledInput where
  source : ModelSource
  compiled : CompiledModelSource
  success : compileModelSource source = .ok compiled
  worldsPositive : 0 < compiled.ast.worldCount
  thingsPositive : 0 < compiled.ast.thingCount

def CompiledInput.inputSize (input : CompiledInput) : Nat :=
  (sourceMetrics input.source).inputSize

def CompiledInput.model (input : CompiledInput) : FiniteModel4 :=
  compileVerifiedModel input.compiled.ast input.worldsPositive input.thingsPositive
    (compileModelSource_ok_wellBounded input.source input.compiled input.success)

/-- The entire counted result must be a registered checker result. Boolean
agreement alone would allow an arbitrarily expensive implementation. -/
def CompiledInput.Registered (input : CompiledInput) (check : FiniteModel4 → Costed Bool) : Prop :=
  ∃ entry : BoundedCheck, entry ∈ (Checker.checkAxioms4BoundedRegistry input.model).toList ∧
    check input.model = entry.run ()

def CompiledInput.operand (input : CompiledInput) (check : FiniteModel4 → Costed Bool) : Costed Bool :=
  reconstructedCheckCosted input.compiled.ast input.worldsPositive input.thingsPositive
    (compileModelSource_ok_wellBounded input.source input.compiled input.success) check

theorem CompiledInput.operand_bound (input : CompiledInput) (check : FiniteModel4 → Costed Bool)
    (registered : input.Registered check) :
    (input.operand check).cost ≤ 54896424 * input.inputSize ^ 16 :=
  reconstructedCheck_source_bound input.source input.compiled input.success
    input.worldsPositive input.thingsPositive check registered

structure ParentInput where
  name : Lean.Name
  input : CompiledInput

/-- With no parent, the parent thunk is unused by fresh scripts. Giving that
thunk the child input makes the common operand definition total. It does not
execute a second check for an expected-answer request. -/
def parentInput (child : CompiledInput) (parent : Option ParentInput) : CompiledInput :=
  match parent with | none => child | some parent => parent.input

def commonSize (child : CompiledInput) (parent : Option ParentInput) : Nat :=
  max child.inputSize (parentInput child parent).inputSize

def plannerCosted (child : CompiledInput) (parent : Option ParentInput)
    (fresh : Bool) (field : CertField) : Costed (Option Lean.Name) :=
  match parent with
  | none => Costed.pure none
  | some parent => certificateReuseSourceCosted parent.name parent.input.source child.source
      parent.input.compiled.tables child.compiled.tables fresh field.field

theorem plannerCosted_bound (child : CompiledInput) (parent : Option ParentInput)
    (fresh : Bool) (field : CertField) :
    (plannerCosted child parent fresh field).cost ≤
      18 * child.inputSize + 11023 * (parentInput child parent).inputSize := by
  cases parent with
  | none => simp [plannerCosted, Costed.pure]
  | some parent =>
      exact certificateReuseSource_source_bound parent.name parent.input.source child.source
        parent.input.compiled child.compiled.tables fresh field.field parent.input.success

/-- This records outcomes of excluded proof work, not arbitrary callbacks
whose executable work is assigned zero cost. Native results are supplied only
after the corresponding counted Boolean computation has run. -/
structure ProofOutcome (ε : Type) where
  nativeResult : NativeCall → Bool → Except ε String
  elaborationFailed : Bool

def checkedAttemptsCosted {ε : Type} (child : CompiledInput) (parent : Option ParentInput)
    (fresh : Bool) (field : CertField) (check : FiniteModel4 → Costed Bool)
    (outcomes : Bool → Option Lean.Name → ProofOutcome ε) : Costed Result :=
  preparedCheckedAttemptsCosted field (fun _ => plannerCosted child parent fresh field)
    (fun declaration reuse request => Costed.map ((outcomes declaration reuse).nativeResult request)
      (nativeRequestCosted request (fun _ => child.operand check)
        (fun _ => (parentInput child parent).operand check)))
    (fun declaration reuse => (outcomes declaration reuse).elaborationFailed)

/-- Both root and extension models use the production checked-attempt driver.
The root planner returns `none` without work. The common upper bound permits
six operands, although a root model cannot enter the reuse/fallback branch. -/
theorem checkedAttemptsCosted_bound {ε : Type}
    (child : CompiledInput) (parent : Option ParentInput)
    (fresh : Bool) (field : CertField) (check : FiniteModel4 → Costed Bool)
    (outcomes : Bool → Option Lean.Name → ProofOutcome ε)
    (childRegistered : child.Registered check)
    (parentRegistered : (parentInput child parent).Registered check) :
    (checkedAttemptsCosted child parent fresh field check outcomes).cost ≤
      18 * child.inputSize + 11023 * (parentInput child parent).inputSize +
        6 * (54896424 * commonSize child parent ^ 16) + 25 := by
  let budget := 54896424 * commonSize child parent ^ 16
  have childBound := (child.operand_bound check childRegistered).trans
    (Nat.mul_le_mul_left 54896424 (Nat.pow_le_pow_left
      (Nat.le_max_left child.inputSize (parentInput child parent).inputSize) 16))
  have parentBound := ((parentInput child parent).operand_bound check parentRegistered).trans
    (Nat.mul_le_mul_left 54896424 (Nat.pow_le_pow_left
      (Nat.le_max_right child.inputSize (parentInput child parent).inputSize) 16))
  have attempts := preparedCheckedAttempts_cost_le field
    (fun _ => plannerCosted child parent fresh field)
    (fun declaration reuse request => Costed.map ((outcomes declaration reuse).nativeResult request)
      (nativeRequestCosted request (fun _ => child.operand check)
        (fun _ => (parentInput child parent).operand check)))
    (fun declaration reuse => (outcomes declaration reuse).elaborationFailed) budget (by
      intro declaration reuse
      cases reuse <;>
        simp only [Costed.map_cost, nativeRequest_cost, Option.isSome_none,
          Option.isSome_some, Bool.false_eq_true, ↓reduceIte, Nat.one_mul]
      all_goals dsimp only [budget, commonSize] at *; omega)
  have planner := plannerCosted_bound child parent fresh field
  dsimp only [checkedAttemptsCosted, budget] at *
  omega

def semanticAttemptCosted {ε : Type} (input : CompiledInput) (field : CertField)
    (declaration : Bool) (checks : NativeCall → FiniteModel4 → Costed Bool)
    (outcome : ProofOutcome ε) : Costed Bool :=
  preparedProofAttemptCosted (if declaration then
      certAxiomTheorem input.compiled.ast.worldCount input.compiled.ast.thingCount input.compiled.tables field
    else certAxiomProofCheck input.compiled.ast.worldCount input.compiled.ast.thingCount input.compiled.tables field)
    (fun request => Costed.map (outcome.nativeResult request)
      (nativeRequestCosted request (fun _ => input.operand (checks request))
        (fun _ => input.operand (checks request)))) outcome.elaborationFailed

theorem semanticAttemptCosted_bound {ε : Type} (input : CompiledInput) (field : CertField)
    (declaration : Bool) (checks : NativeCall → FiniteModel4 → Costed Bool)
    (outcome : ProofOutcome ε)
    (registered : ∀ request, input.Registered (checks request)) :
    (semanticAttemptCosted input field declaration checks outcome).cost ≤
      54896424 * input.inputSize ^ 16 + 5 :=
  source_prepared_semantic_bound input.source input.compiled input.success
    input.worldsPositive input.thingsPositive field declaration checks
    outcome.nativeResult outcome.elaborationFailed (fun request _ => registered request)

/-- The declaration's command flag selects its observed proof outcome, as in
the frontend. Both declaration modes prepare the same theorem source. -/
def fieldCosted {ε : Type} (child : CompiledInput) (parent : Option ParentInput)
    (fresh : Bool) (field : CertField) (check : FiniteModel4 → Costed Bool)
    (semanticChecks : NativeCall → FiniteModel4 → Costed Bool)
    (checkedOutcomes : Bool → Option Lean.Name → ProofOutcome ε)
    (semanticOutcomes : Bool → Bool → ProofOutcome ε) : Costed Result :=
  runFieldCosted
    (fun _ => certificationFieldPrecheckCosted child.source.worlds.size child.source.things.size
      child.compiled.tables field.field)
    (fun _ => checkedAttemptsCosted child parent fresh field check checkedOutcomes)
    (fun _ => useCommandCertificateProbeCosted field)
    (fun _ => semanticAttemptCosted child field false semanticChecks (semanticOutcomes false false))
    (fun command => semanticAttemptCosted child field true semanticChecks (semanticOutcomes true command))

/-- The field bound includes closure prechecking, actual reuse planning, up
to six checked-proof operands, and up to two semantic-proof operands. The
constant 55 covers attempt preparation, policy selection, and driver control. -/
theorem fieldCosted_bound {ε : Type} (child : CompiledInput) (parent : Option ParentInput)
    (fresh : Bool) (field : CertField) (check : FiniteModel4 → Costed Bool)
    (semanticChecks : NativeCall → FiniteModel4 → Costed Bool)
    (checkedOutcomes : Bool → Option Lean.Name → ProofOutcome ε)
    (semanticOutcomes : Bool → Bool → ProofOutcome ε)
    (childRegistered : child.Registered check)
    (parentRegistered : (parentInput child parent).Registered check)
    (semanticRegistered : ∀ request, child.Registered (semanticChecks request)) :
    (fieldCosted child parent fresh field check semanticChecks checkedOutcomes semanticOutcomes).cost ≤
      124 * child.inputSize ^ 4 + 18 * child.inputSize +
        11023 * (parentInput child parent).inputSize +
        8 * (54896424 * commonSize child parent ^ 16) + 55 := by
  have driver := fieldDriver_cost_le
    (fun _ => certificationFieldPrecheckCosted child.source.worlds.size child.source.things.size
      child.compiled.tables field.field)
    (fun _ => checkedAttemptsCosted child parent fresh field check checkedOutcomes)
    (fun _ => useCommandCertificateProbeCosted field)
    (fun _ => semanticAttemptCosted child field false semanticChecks (semanticOutcomes false false))
    (fun command => semanticAttemptCosted child field true semanticChecks (semanticOutcomes true command))
  have precheck := source_field_precheck_scalar_bound child.source child.compiled.tables field.field
  have checked := checkedAttemptsCosted_bound child parent fresh field check checkedOutcomes
    childRegistered parentRegistered
  have policy := commandProbePolicy_cost_le field
  have semantic declaration command := semanticAttemptCosted_bound child field declaration
    semanticChecks (semanticOutcomes declaration command) semanticRegistered
  have common : 54896424 * child.inputSize ^ 16 ≤ 54896424 * commonSize child parent ^ 16 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_max_left _ _) 16)
  have trial := semantic false false
  have command := semantic true true
  have declaration := semantic true false
  dsimp only [fieldCosted, CompiledInput.inputSize] at *
  omega

/-- Erasure leaves the field driver's precheck, retry result, command policy,
and semantic trial/declaration order unchanged. The values below are the same
component computations with their accumulated costs discarded. -/
theorem fieldCosted_erasure {ε : Type} (child : CompiledInput) (parent : Option ParentInput)
    (fresh : Bool) (field : CertField) (check : FiniteModel4 → Costed Bool)
    (semanticChecks : NativeCall → FiniteModel4 → Costed Bool)
    (checkedOutcomes : Bool → Option Lean.Name → ProofOutcome ε)
    (semanticOutcomes : Bool → Bool → ProofOutcome ε) :
    (fieldCosted child parent fresh field check semanticChecks checkedOutcomes semanticOutcomes).value =
      runField (m := Id) (fun _ => pure ())
        (fun _ => (certificationFieldPrecheckCosted child.source.worlds.size child.source.things.size
          child.compiled.tables field.field).value)
        (fun _ => (checkedAttemptsCosted child parent fresh field check checkedOutcomes).value)
        (fun _ => useCommandCertificateProbe field)
        (fun _ => (semanticAttemptCosted child field false semanticChecks
          (semanticOutcomes false false)).value)
        (fun command => (semanticAttemptCosted child field true semanticChecks
          (semanticOutcomes true command)).value) :=
  fieldDriver_erasure _ _ _ _ _

/-- This is the production registry driver with the source-linked field
composition above. After the first failure it retains the completed prefix
and skips all later field computations. -/
def registryCosted {ε : Type} (child : CompiledInput) (parent : Option ParentInput)
    (fresh : Bool) (fields : Array CertField)
    (checks : CertField → FiniteModel4 → Costed Bool)
    (semanticChecks : CertField → NativeCall → FiniteModel4 → Costed Bool)
    (checkedOutcomes : CertField → Bool → Option Lean.Name → ProofOutcome ε)
    (semanticOutcomes : CertField → Bool → Bool → ProofOutcome ε) : Costed (RegistryResult CertField) :=
  runFieldsCosted fields CertField.field fun field =>
    fieldCosted child parent fresh field (checks field) (semanticChecks field)
      (checkedOutcomes field) (semanticOutcomes field)

/-- Erasing the outer composition preserves completed names, reuse rows, and
the failed field. The field's own erasure is supplied by the shared field,
checked-attempt, and proof-preparation erasure theorems. -/
theorem registryCosted_erasure {ε : Type} (child : CompiledInput) (parent : Option ParentInput)
    (fresh : Bool) (fields : Array CertField)
    (checks : CertField → FiniteModel4 → Costed Bool)
    (semanticChecks : CertField → NativeCall → FiniteModel4 → Costed Bool)
    (checkedOutcomes : CertField → Bool → Option Lean.Name → ProofOutcome ε)
    (semanticOutcomes : CertField → Bool → Bool → ProofOutcome ε) :
    (registryCosted child parent fresh fields checks semanticChecks checkedOutcomes semanticOutcomes).value =
      runFields (m := Id) (fun _ => pure ()) fields CertField.field (fun field =>
        (fieldCosted child parent fresh field (checks field) (semanticChecks field)
          (checkedOutcomes field) (semanticOutcomes field)).value) :=
  registryDriver_erasure fields CertField.field _

/-- Each visited field contributes at most seven outer-driver operations in
addition to its source-linked field bound. This parameterizes the number of
registered fields, not the complexity of unrestricted input formulas. -/
theorem registryCosted_bound {ε : Type} (child : CompiledInput) (parent : Option ParentInput)
    (fresh : Bool) (fields : Array CertField)
    (checks : CertField → FiniteModel4 → Costed Bool)
    (semanticChecks : CertField → NativeCall → FiniteModel4 → Costed Bool)
    (checkedOutcomes : CertField → Bool → Option Lean.Name → ProofOutcome ε)
    (semanticOutcomes : CertField → Bool → Bool → ProofOutcome ε)
    (childRegistered : ∀ field, child.Registered (checks field))
    (parentRegistered : ∀ field, (parentInput child parent).Registered (checks field))
    (semanticRegistered : ∀ field request, child.Registered (semanticChecks field request)) :
    (registryCosted child parent fresh fields checks semanticChecks checkedOutcomes semanticOutcomes).cost ≤
      2 + fields.size * (124 * child.inputSize ^ 4 + 18 * child.inputSize +
        11023 * (parentInput child parent).inputSize +
        8 * (54896424 * commonSize child parent ^ 16) + 62) := by
  let action field := fieldCosted child parent fresh field (checks field) (semanticChecks field)
    (checkedOutcomes field) (semanticOutcomes field)
  let budget := 124 * child.inputSize ^ 4 + 18 * child.inputSize +
    11023 * (parentInput child parent).inputSize +
    8 * (54896424 * commonSize child parent ^ 16) + 62
  have perField field : (action field).cost + 7 ≤ budget := by
    have bound := fieldCosted_bound child parent fresh field (checks field) (semanticChecks field)
      (checkedOutcomes field) (semanticOutcomes field) (childRegistered field)
      (parentRegistered field) (semanticRegistered field)
    dsimp only [action, budget]
    omega
  have sumBound (xs : List CertField) :
      (xs.map (fun field => (action field).cost + 7)).sum ≤ xs.length * budget := by
    induction xs with
    | nil => simp
    | cons field rest ih =>
        have head := perField field
        simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
        omega
  have driver := registryDriver_cost_le fields CertField.field action
  have total := sumBound fields.toList
  simp only [Array.length_toList] at total
  change (runFieldsCosted fields CertField.field action).cost ≤ _
  dsimp only [budget] at total
  omega

/-- The primary data-complexity result fixes the UFO registry at 113 fields.
Repeated trials, declarations, failed reuse, and skipped later fields are
already included. This bounds registry certification, before failure-report
selection and the source compiler/pre-certification assertion stage. -/
theorem fixedRegistryCosted_bound {ε : Type} (child : CompiledInput) (parent : Option ParentInput)
    (fresh : Bool) (checks : CertField → FiniteModel4 → Costed Bool)
    (semanticChecks : CertField → NativeCall → FiniteModel4 → Costed Bool)
    (checkedOutcomes : CertField → Bool → Option Lean.Name → ProofOutcome ε)
    (semanticOutcomes : CertField → Bool → Bool → ProofOutcome ε)
    (childRegistered : ∀ field, child.Registered (checks field))
    (parentRegistered : ∀ field, (parentInput child parent).Registered (checks field))
    (semanticRegistered : ∀ field request, child.Registered (semanticChecks field request)) :
    (registryCosted child parent fresh certFields checks semanticChecks checkedOutcomes semanticOutcomes).cost ≤
      2 + 113 * (124 * child.inputSize ^ 4 + 18 * child.inputSize +
        11023 * (parentInput child parent).inputSize +
        8 * (54896424 * commonSize child parent ^ 16) + 62) :=
  registryCosted_bound child parent fresh certFields checks semanticChecks checkedOutcomes semanticOutcomes
    childRegistered parentRegistered semanticRegistered

def counterexampleAttemptCosted {ε : Type} (input : CompiledInput) (field : CertField)
    (checks : NativeCall → FiniteModel4 → Costed Bool) (outcome : ProofOutcome ε) : Costed Bool :=
  preparedProofAttemptCosted (certAxiomCounterexampleCheck field)
    (fun request => Costed.map (outcome.nativeResult request)
      (nativeRequestCosted request (fun _ => input.operand (checks request))
        (fun _ => input.operand (checks request)))) outcome.elaborationFailed

theorem counterexampleAttemptCosted_bound {ε : Type} (input : CompiledInput) (field : CertField)
    (checks : NativeCall → FiniteModel4 → Costed Bool) (outcome : ProofOutcome ε)
    (registered : ∀ request, input.Registered (checks request)) :
    (counterexampleAttemptCosted input field checks outcome).cost ≤
      2 * (54896424 * input.inputSize ^ 16) + 9 :=
  source_prepared_counterexample_bound input.source input.compiled input.success
    input.worldsPositive input.thingsPositive field checks outcome.nativeResult
    outcome.elaborationFailed (fun request _ => registered request)

/-- The caller supplies the already-created name arrays. The source's named
facts and compiled tables are reused, as in `certificationFailureAnalysis`.
Captured proof-error texts are observed output from excluded proof work. -/
def failureAnalysisCosted {ε : Type} (input : CompiledInput)
    (worldNames thingNames : Array Lean.Name) (field : CertField)
    (checks : NativeCall → FiniteModel4 → Costed Bool) (outcome : ProofOutcome ε)
    (errors : Array String) : Costed (Array String) :=
  Costed.bind (counterexampleAttemptCosted input field checks outcome) fun failed =>
    certificationFailureReportCosted worldNames thingNames input.source.facts
      input.compiled.tables field.field failed errors

/-- The diagnostic term uses the existing selected-analyzer bound and emitted
row counts. It is separate from the fixed-registry certification polynomial:
formula evaluation and report construction have their own size parameters. -/
def failureReportBound (input : CompiledInput) (worldNames thingNames : Array Lean.Name)
    (field : CertField) (errors : Array String) : Nat :=
  18 + 17 * errors.size +
    diagnosticWitnessesInnerCostBound worldNames thingNames input.source.facts input.compiled.tables field.field +
    7 * (diagnosticWitnesses worldNames thingNames input.source.facts input.compiled.tables field.field).size +
    ax68ClosureAnalysisCostBound worldNames.size thingNames.size +
    3 * (ax68ClosureAnalysis worldNames thingNames input.compiled.tables).size

/-- The probe's computed failure status selects the actual report branch.
No independent report result or arbitrary analyzer-cost assumption is used. -/
theorem failureAnalysisCosted_bound {ε : Type} (input : CompiledInput)
    (worldNames thingNames : Array Lean.Name) (field : CertField)
    (checks : NativeCall → FiniteModel4 → Costed Bool) (outcome : ProofOutcome ε)
    (errors : Array String) (registered : ∀ request, input.Registered (checks request)) :
    (failureAnalysisCosted input worldNames thingNames field checks outcome errors).cost ≤
      2 * (54896424 * input.inputSize ^ 16) + 9 +
        failureReportBound input worldNames thingNames field errors := by
  have probe := counterexampleAttemptCosted_bound input field checks outcome registered
  have report := certificationFailureReport_cost_le worldNames thingNames input.source.facts
    input.compiled.tables field.field (counterexampleAttemptCosted input field checks outcome).value errors
  dsimp only [failureAnalysisCosted, failureReportBound] at *
  rw [Costed.bind_cost]
  omega

theorem failureAnalysisCosted_erasure {ε : Type} (input : CompiledInput)
    (worldNames thingNames : Array Lean.Name) (field : CertField)
    (checks : NativeCall → FiniteModel4 → Costed Bool) (outcome : ProofOutcome ε)
    (errors : Array String) :
    (failureAnalysisCosted input worldNames thingNames field checks outcome errors).value =
      (certificationFailureReportCosted worldNames thingNames input.source.facts input.compiled.tables
        field.field (counterexampleAttemptCosted input field checks outcome).value errors).value :=
  Costed.bind_value _ _

/-- Run the registry, then prepare the failed field's counterexample probe
and report only when the shared production selector requests them. -/
def registryAndReportCosted {ε : Type} (child : CompiledInput) (parent : Option ParentInput)
    (worldNames thingNames : Array Lean.Name) (fresh : Bool) (fields : Array CertField)
    (checks : CertField → FiniteModel4 → Costed Bool)
    (semanticChecks counterexampleChecks : CertField → NativeCall → FiniteModel4 → Costed Bool)
    (checkedOutcomes : CertField → Bool → Option Lean.Name → ProofOutcome ε)
    (semanticOutcomes : CertField → Bool → Bool → ProofOutcome ε)
    (counterexampleOutcomes : CertField → ProofOutcome ε)
    (errors : CertField → Array String) : Costed (RegistryReport CertField) :=
  Costed.bind (registryCosted child parent fresh fields checks semanticChecks checkedOutcomes semanticOutcomes)
    fun progress => reportAfterRegistryCosted progress fun field =>
      failureAnalysisCosted child worldNames thingNames field
        (counterexampleChecks field) (counterexampleOutcomes field) (errors field)

theorem registryAndReportCosted_erasure {ε : Type} (child : CompiledInput) (parent : Option ParentInput)
    (worldNames thingNames : Array Lean.Name) (fresh : Bool) (fields : Array CertField)
    (checks : CertField → FiniteModel4 → Costed Bool)
    (semanticChecks counterexampleChecks : CertField → NativeCall → FiniteModel4 → Costed Bool)
    (checkedOutcomes : CertField → Bool → Option Lean.Name → ProofOutcome ε)
    (semanticOutcomes : CertField → Bool → Bool → ProofOutcome ε)
    (counterexampleOutcomes : CertField → ProofOutcome ε) (errors : CertField → Array String) :
    (registryAndReportCosted child parent worldNames thingNames fresh fields checks semanticChecks
      counterexampleChecks checkedOutcomes semanticOutcomes counterexampleOutcomes errors).value =
      let progress := runFields (m := Id) (fun _ => pure ()) fields CertField.field (fun field =>
        (fieldCosted child parent fresh field (checks field) (semanticChecks field)
          (checkedOutcomes field) (semanticOutcomes field)).value)
      reportAfterRegistry (m := Id) (fun _ => pure ()) progress (fun field =>
        (failureAnalysisCosted child worldNames thingNames field
          (counterexampleChecks field) (counterexampleOutcomes field) (errors field)).value) := by
  simp only [registryAndReportCosted, Costed.bind_value, reportAfterRegistry_erasure,
    registryCosted_erasure]

/-- The diagnostic term belongs only to the field the registry actually
failed. It is zero after success. Thus the bound does not multiply report
construction by registry size or charge a second report after an early error.
All native-cost premises are concrete counted registry memberships. -/
theorem registryAndReportCosted_bound {ε : Type} (child : CompiledInput) (parent : Option ParentInput)
    (worldNames thingNames : Array Lean.Name) (fresh : Bool) (fields : Array CertField)
    (checks : CertField → FiniteModel4 → Costed Bool)
    (semanticChecks counterexampleChecks : CertField → NativeCall → FiniteModel4 → Costed Bool)
    (checkedOutcomes : CertField → Bool → Option Lean.Name → ProofOutcome ε)
    (semanticOutcomes : CertField → Bool → Bool → ProofOutcome ε)
    (counterexampleOutcomes : CertField → ProofOutcome ε) (errors : CertField → Array String)
    (childRegistered : ∀ field, child.Registered (checks field))
    (parentRegistered : ∀ field, (parentInput child parent).Registered (checks field))
    (semanticRegistered : ∀ field request, child.Registered (semanticChecks field request))
    (counterexampleRegistered : ∀ field request, child.Registered (counterexampleChecks field request)) :
    (registryAndReportCosted child parent worldNames thingNames fresh fields checks semanticChecks
      counterexampleChecks checkedOutcomes semanticOutcomes counterexampleOutcomes errors).cost ≤
      3 + fields.size * (124 * child.inputSize ^ 4 + 18 * child.inputSize +
        11023 * (parentInput child parent).inputSize +
        8 * (54896424 * commonSize child parent ^ 16) + 62) +
      match (registryCosted child parent fresh fields checks semanticChecks
          checkedOutcomes semanticOutcomes).value.failedField? with
      | none => 0
      | some field => 2 * (54896424 * child.inputSize ^ 16) + 9 +
          failureReportBound child worldNames thingNames field (errors field) := by
  have registry := registryCosted_bound child parent fresh fields checks semanticChecks
    checkedOutcomes semanticOutcomes childRegistered parentRegistered semanticRegistered
  rw [registryAndReportCosted, Costed.bind_cost, reportAfterRegistry_cost]
  cases failed : (registryCosted child parent fresh fields checks semanticChecks
      checkedOutcomes semanticOutcomes).value.failedField? with
  | none => simp only; omega
  | some field =>
      have report := failureAnalysisCosted_bound child worldNames thingNames field
        (counterexampleChecks field) (counterexampleOutcomes field) (errors field)
        (counterexampleRegistered field)
      simp only
      omega

/-- After successful compilation, construct the two frontend name arrays
once, check derived assertions, and run certification only if they pass.
`input.success` identifies these tables and facts as the actual compiler result;
it is not an extra independently sized model supplied to the workflow. -/
def postCompileCosted {ε : Type} (child : CompiledInput) (parent : Option ParentInput)
    (fresh derivedProofFailed : Bool) (fields : Array CertField)
    (checks : CertField → FiniteModel4 → Costed Bool)
    (semanticChecks counterexampleChecks : CertField → NativeCall → FiniteModel4 → Costed Bool)
    (checkedOutcomes : CertField → Bool → Option Lean.Name → ProofOutcome ε)
    (semanticOutcomes : CertField → Bool → Bool → ProofOutcome ε)
    (counterexampleOutcomes : CertField → ProofOutcome ε) (errors : CertField → Array String) :
    Costed (AssertionResult (RegistryReport CertField)) := do
  let worldNames ← namesFromStringsCosted child.source.worlds
  let thingNames ← namesFromStringsCosted child.source.things
  runAfterAssertionsCosted
    (derivedAssertionFailureCosted worldNames thingNames child.source.facts
      child.compiled.scopedFacts child.compiled.tables)
    derivedProofFailed derivedAssertionFailureReportCosted (fun _ =>
      registryAndReportCosted child parent worldNames thingNames fresh fields checks semanticChecks
        counterexampleChecks checkedOutcomes semanticOutcomes counterexampleOutcomes errors)

/-- Erasure connects the post-compilation composition to the shared assertion
driver on the source's actual names, facts, and tables. Lower-level erasure
theorems then expand the registry and report computation in the last callback. -/
theorem postCompileCosted_erasure {ε : Type} (child : CompiledInput) (parent : Option ParentInput)
    (fresh derivedProofFailed : Bool) (fields : Array CertField)
    (checks : CertField → FiniteModel4 → Costed Bool)
    (semanticChecks counterexampleChecks : CertField → NativeCall → FiniteModel4 → Costed Bool)
    (checkedOutcomes : CertField → Bool → Option Lean.Name → ProofOutcome ε)
    (semanticOutcomes : CertField → Bool → Bool → ProofOutcome ε)
    (counterexampleOutcomes : CertField → ProofOutcome ε) (errors : CertField → Array String) :
    (postCompileCosted child parent fresh derivedProofFailed fields checks semanticChecks
      counterexampleChecks checkedOutcomes semanticOutcomes counterexampleOutcomes errors).value =
      let worldNames := namesFromStrings child.source.worlds
      let thingNames := namesFromStrings child.source.things
      runAfterAssertions (m := Id) (fun _ => pure ())
        (fun _ => derivedAssertionFailure? worldNames thingNames child.source.facts
          child.compiled.scopedFacts child.compiled.tables)
        (fun _ => derivedProofFailed)
        (fun saved => (derivedAssertionFailureReportCosted saved).value)
        (fun _ => (registryAndReportCosted child parent worldNames thingNames fresh fields checks
          semanticChecks counterexampleChecks checkedOutcomes semanticOutcomes counterexampleOutcomes errors).value) := by
  simp only [postCompileCosted, Bind.bind, Costed.bind_value, runAfterAssertions_erasure,
    namesFromStrings, derivedAssertionFailure?]

/-- Source compilation, name conversion, and the derived-assertion stage cost
at most 6129N⁵ plus two driver decisions. The remaining term is the concrete
registry/report computation, not the cost of an unconstrained callback. -/
theorem postCompileCosted_prefix_bound {ε : Type} (child : CompiledInput) (parent : Option ParentInput)
    (fresh derivedProofFailed : Bool) (fields : Array CertField)
    (checks : CertField → FiniteModel4 → Costed Bool)
    (semanticChecks counterexampleChecks : CertField → NativeCall → FiniteModel4 → Costed Bool)
    (checkedOutcomes : CertField → Bool → Option Lean.Name → ProofOutcome ε)
    (semanticOutcomes : CertField → Bool → Bool → ProofOutcome ε)
    (counterexampleOutcomes : CertField → ProofOutcome ε) (errors : CertField → Array String) :
    compilerOperationalCost child.source +
      (postCompileCosted child parent fresh derivedProofFailed fields checks semanticChecks
        counterexampleChecks checkedOutcomes semanticOutcomes counterexampleOutcomes errors).cost ≤
      6129 * child.inputSize ^ 5 + 2 +
        (registryAndReportCosted child parent (namesFromStrings child.source.worlds)
          (namesFromStrings child.source.things) fresh fields checks semanticChecks counterexampleChecks
          checkedOutcomes semanticOutcomes counterexampleOutcomes errors).cost := by
  let precheck := derivedAssertionFailureCosted (namesFromStrings child.source.worlds)
    (namesFromStrings child.source.things) child.source.facts child.compiled.scopedFacts child.compiled.tables
  let remaining := registryAndReportCosted child parent (namesFromStrings child.source.worlds)
    (namesFromStrings child.source.things) fresh fields checks semanticChecks counterexampleChecks
    checkedOutcomes semanticOutcomes counterexampleOutcomes errors
  have driver := runAfterAssertions_cost_le precheck derivedProofFailed
    derivedAssertionFailureReportCosted (fun _ => remaining)
  have report := derivedAssertionFailureReportCosted_cost_le precheck.value
  have assertions := source_derivedAssertionFailure_cost_bound child.source child.compiled child.success
  have compiler := source_compiler_scalar_polynomial_bound child.source
  have names := sourceNameConversion_cost_bound child.source
  have positive := sourceMetrics_inputSize_pos child.source
  have linear : (sourceMetrics child.source).inputSize ≤ (sourceMetrics child.source).inputSize ^ 5 := by
    simpa using Nat.pow_le_pow_right positive (show 1 ≤ 5 by omega)
  have fourth := Nat.pow_le_pow_right positive (show 4 ≤ 5 by omega)
  have one : 1 ≤ (sourceMetrics child.source).inputSize ^ 5 := by omega
  have compilerBound := compiler.trans (Nat.mul_le_mul_left 511 fourth)
  have nameBound := names.trans (Nat.mul_le_mul_left 6 linear)
  simp only [postCompileCosted, Bind.bind, Costed.bind_cost, namesFromStringsCosted_value]
  dsimp only [precheck, remaining, namesFromStrings, CompiledInput.inputSize] at *
  simp only [namesFromStringsCosted_value] at *
  omega

/-- End-to-end algorithm bound for a successfully compiled source. It includes
name conversion, derived-assertion checking, every scheduled native attempt,
reuse planning, registry traversal, and the selected failure analysis. Parsing,
proof elaboration, final theorem/manifest emission, and widgets are excluded.

The diagnostic allowance is selected from the registry result. If derived
assertions fail first, that registry is not executed; the same allowance is
still a valid upper bound. Actual costs retain that earlier exit. -/
theorem sourceWorkflow_bound {ε : Type} (child : CompiledInput) (parent : Option ParentInput)
    (fresh derivedProofFailed : Bool) (fields : Array CertField)
    (checks : CertField → FiniteModel4 → Costed Bool)
    (semanticChecks counterexampleChecks : CertField → NativeCall → FiniteModel4 → Costed Bool)
    (checkedOutcomes : CertField → Bool → Option Lean.Name → ProofOutcome ε)
    (semanticOutcomes : CertField → Bool → Bool → ProofOutcome ε)
    (counterexampleOutcomes : CertField → ProofOutcome ε) (errors : CertField → Array String)
    (childRegistered : ∀ field, child.Registered (checks field))
    (parentRegistered : ∀ field, (parentInput child parent).Registered (checks field))
    (semanticRegistered : ∀ field request, child.Registered (semanticChecks field request))
    (counterexampleRegistered : ∀ field request, child.Registered (counterexampleChecks field request)) :
    compilerOperationalCost child.source +
      (postCompileCosted child parent fresh derivedProofFailed fields checks semanticChecks
        counterexampleChecks checkedOutcomes semanticOutcomes counterexampleOutcomes errors).cost ≤
      6129 * child.inputSize ^ 5 + 5 +
        fields.size * (124 * child.inputSize ^ 4 + 18 * child.inputSize +
          11023 * (parentInput child parent).inputSize +
          8 * (54896424 * commonSize child parent ^ 16) + 62) +
      match (registryCosted child parent fresh fields checks semanticChecks
          checkedOutcomes semanticOutcomes).value.failedField? with
      | none => 0
      | some field => 2 * (54896424 * child.inputSize ^ 16) + 9 +
          failureReportBound child (namesFromStrings child.source.worlds)
            (namesFromStrings child.source.things) field (errors field) := by
  have prefixBound := postCompileCosted_prefix_bound child parent fresh derivedProofFailed fields checks
    semanticChecks counterexampleChecks checkedOutcomes semanticOutcomes counterexampleOutcomes errors
  have registry := registryAndReportCosted_bound child parent (namesFromStrings child.source.worlds)
    (namesFromStrings child.source.things) fresh fields checks semanticChecks counterexampleChecks
    checkedOutcomes semanticOutcomes counterexampleOutcomes errors childRegistered parentRegistered
    semanticRegistered counterexampleRegistered
  omega

/-- Arithmetic reduction of the concrete multivariate workflow bound. Every
source component has already been included in C and P. The two extra operands
reserve the failed field's counterexample probe; diagnostic output is separate. -/
theorem sourceWorkflowCore_scalar_bound (C P R : Nat) (positive : 0 < C) :
    6129 * C ^ 5 + 5 + R * (124 * C ^ 4 + 18 * C + 11023 * P +
        8 * (54896424 * (max C P) ^ 16) + 62) + 2 * (54896424 * C ^ 16) + 9 ≤
      (439182619 * R + 109798991) * (max C P) ^ 16 := by
  let n := max C P
  have child : C ≤ n := Nat.le_max_left _ _
  have parent : P ≤ n := Nat.le_max_right _ _
  have hn : 0 < n := positive.trans_le child
  have one : 1 ≤ n ^ 16 := by
    simpa using Nat.pow_le_pow_right hn (show 0 ≤ 16 by omega)
  have linear : n ≤ n ^ 16 := by
    simpa using Nat.pow_le_pow_right hn (show 1 ≤ 16 by omega)
  have c := child.trans linear
  have p := parent.trans linear
  have fourth := (Nat.pow_le_pow_left child 4).trans
    (Nat.pow_le_pow_right hn (show 4 ≤ 16 by omega))
  have fifth := (Nat.pow_le_pow_left child 5).trans
    (Nat.pow_le_pow_right hn (show 5 ≤ 16 by omega))
  have native := Nat.mul_le_mul_left (2 * 54896424) (Nat.pow_le_pow_left child 16)
  have perField : 124 * C ^ 4 + 18 * C + 11023 * P +
      8 * (54896424 * n ^ 16) + 62 ≤ 439182619 * n ^ 16 := by omega
  have registry := Nat.mul_le_mul_left R perField
  have normalization : (439182619 * R + 109798991) * n ^ 16 =
      R * (439182619 * n ^ 16) + 109798991 * n ^ 16 := by ring
  change _ ≤ (439182619 * R + 109798991) * n ^ 16
  rw [normalization]
  dsimp only [n] at *
  omega

/-- One-variable corollary for the executed algorithmic workflow. N is the
larger source size and R is the registry length. Fixing R at 113 gives the
data-complexity coefficient 49,737,434,938. The selected diagnostic term stays
explicit; this is not a uniform polynomial for unrestricted formulas. -/
theorem sourceWorkflow_scalar_bound {ε : Type} (child : CompiledInput) (parent : Option ParentInput)
    (fresh derivedProofFailed : Bool) (fields : Array CertField)
    (checks : CertField → FiniteModel4 → Costed Bool)
    (semanticChecks counterexampleChecks : CertField → NativeCall → FiniteModel4 → Costed Bool)
    (checkedOutcomes : CertField → Bool → Option Lean.Name → ProofOutcome ε)
    (semanticOutcomes : CertField → Bool → Bool → ProofOutcome ε)
    (counterexampleOutcomes : CertField → ProofOutcome ε) (errors : CertField → Array String)
    (childRegistered : ∀ field, child.Registered (checks field))
    (parentRegistered : ∀ field, (parentInput child parent).Registered (checks field))
    (semanticRegistered : ∀ field request, child.Registered (semanticChecks field request))
    (counterexampleRegistered : ∀ field request, child.Registered (counterexampleChecks field request)) :
    compilerOperationalCost child.source +
      (postCompileCosted child parent fresh derivedProofFailed fields checks semanticChecks
        counterexampleChecks checkedOutcomes semanticOutcomes counterexampleOutcomes errors).cost ≤
      (439182619 * fields.size + 109798991) * commonSize child parent ^ 16 +
      match (registryCosted child parent fresh fields checks semanticChecks
          checkedOutcomes semanticOutcomes).value.failedField? with
      | none => 0
      | some field => failureReportBound child (namesFromStrings child.source.worlds)
          (namesFromStrings child.source.things) field (errors field) := by
  have workflow := sourceWorkflow_bound child parent fresh derivedProofFailed fields checks semanticChecks
    counterexampleChecks checkedOutcomes semanticOutcomes counterexampleOutcomes errors
    childRegistered parentRegistered semanticRegistered counterexampleRegistered
  have scalar := sourceWorkflowCore_scalar_bound child.inputSize (parentInput child parent).inputSize
    fields.size (sourceMetrics_inputSize_pos child.source)
  dsimp only [commonSize] at *
  cases failed : (registryCosted child parent fresh fields checks semanticChecks
      checkedOutcomes semanticOutcomes).value.failedField? with
  | none =>
      simp only [failed] at workflow ⊢
      omega
  | some field =>
      simp only [failed] at workflow ⊢
      apply workflow.trans
      simpa only [Nat.add_assoc] using Nat.add_le_add_right scalar
        (failureReportBound child (namesFromStrings child.source.worlds)
          (namesFromStrings child.source.things) field (errors field))

/-- Fixed-registry data complexity, with diagnostics kept as an explicit
output-sensitive term. The constant is the scalar coefficient at R = 113;
it is derived from the component bounds, not assigned as an execution count. -/
theorem sourceWorkflow_fixed_data_bound {ε : Type} (child : CompiledInput) (parent : Option ParentInput)
    (fresh derivedProofFailed : Bool)
    (checks : CertField → FiniteModel4 → Costed Bool)
    (semanticChecks counterexampleChecks : CertField → NativeCall → FiniteModel4 → Costed Bool)
    (checkedOutcomes : CertField → Bool → Option Lean.Name → ProofOutcome ε)
    (semanticOutcomes : CertField → Bool → Bool → ProofOutcome ε)
    (counterexampleOutcomes : CertField → ProofOutcome ε) (errors : CertField → Array String)
    (childRegistered : ∀ field, child.Registered (checks field))
    (parentRegistered : ∀ field, (parentInput child parent).Registered (checks field))
    (semanticRegistered : ∀ field request, child.Registered (semanticChecks field request))
    (counterexampleRegistered : ∀ field request, child.Registered (counterexampleChecks field request)) :
    compilerOperationalCost child.source +
      (postCompileCosted child parent fresh derivedProofFailed certFields checks semanticChecks
        counterexampleChecks checkedOutcomes semanticOutcomes counterexampleOutcomes errors).cost ≤
      49737434938 * commonSize child parent ^ 16 +
      match (registryCosted child parent fresh certFields checks semanticChecks
          checkedOutcomes semanticOutcomes).value.failedField? with
      | none => 0
      | some field => failureReportBound child (namesFromStrings child.source.worlds)
          (namesFromStrings child.source.things) field (errors field) :=
  sourceWorkflow_scalar_bound child parent fresh derivedProofFailed certFields checks semanticChecks
    counterexampleChecks checkedOutcomes semanticOutcomes counterexampleOutcomes errors
    childRegistered parentRegistered semanticRegistered counterexampleRegistered

/-- The scalar upper bound grows with source size, registry length, and the
separate diagnostic allowance. The allowance is a size/output bound, not a
requirement that actual reports grow when facts are added. -/
theorem sourceWorkflowScalarBound_mono {N R D N' R' D' : Nat}
    (sourceGrows : N ≤ N') (registryGrows : R ≤ R') (diagnosticsGrow : D ≤ D') :
    (439182619 * R + 109798991) * N ^ 16 + D ≤
      (439182619 * R' + 109798991) * N' ^ 16 + D' := by
  exact Nat.add_le_add (Nat.mul_le_mul
    (Nat.add_le_add_right (Nat.mul_le_mul_left 439182619 registryGrows) 109798991)
    (Nat.pow_le_pow_left sourceGrows 16)) diagnosticsGrow

/-- Adding source size or registered fields cannot reduce this upper bound.
Exact execution costs need not be monotone: an earlier answer can skip work. -/
theorem registryBound_mono {C P R C' P' R' : Nat}
    (childGrows : C ≤ C') (parentGrows : P ≤ P') (registryGrows : R ≤ R') :
    2 + R * (124 * C ^ 4 + 18 * C + 11023 * P +
        8 * (54896424 * (max C P) ^ 16) + 62) ≤
      2 + R' * (124 * C' ^ 4 + 18 * C' + 11023 * P' +
        8 * (54896424 * (max C' P') ^ 16) + 62) := by
  have precheck := Nat.mul_le_mul_left 124 (Nat.pow_le_pow_left childGrows 4)
  have childPlan := Nat.mul_le_mul_left 18 childGrows
  have parentPlan := Nat.mul_le_mul_left 11023 parentGrows
  have checks := Nat.mul_le_mul_left 8 (Nat.mul_le_mul_left 54896424
    (Nat.pow_le_pow_left (max_le_max childGrows parentGrows) 16))
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul registryGrows
  omega

end LeanUfo.UFO.DSL.Complexity.Certification
