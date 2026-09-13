import LeanUfo.UFO.DSL.Certificate.Checking
import LeanUfo.UFO.DSL.Certificate.Generation
import LeanUfo.UFO.DSL.Diagnostic.Analysis

/-!
# Frontend control-flow costs

These theorems cover the checked-field driver used by `Syntax.lean`.
Reuse planning runs once. At most four proof callbacks then run: the initial
trial and declaration, followed by the fresh trial and declaration after
failed reuse. Skipped callbacks cost nothing. The driver adds at most five
branch operations.

`registryDriver_cost_le` sums the field callbacks over the actual outer driver.
It includes progress-array initialization and updates, and skipped visits after
failure. `registryDriver_erasure` preserves the returned prefix and reuse rows.

`fieldDriver_cost_le` covers the precheck and semantic attempt order around
the checked driver. `certificationRegistry_control_bound` composes both levels
with the actual closure precheck and command-only policy. Source-linked proof
costs are supplied by `Complexity/Certification.lean`, which composes the
algorithmic workflow.

Generated proof scripts supply their typed native-call requests to the count
proofs. Fresh checked scripts request one checker; reuse requests two.
Semantic scripts request at most one, and counterexample scripts at most two.
These are request counts, not operation costs or a verified Lean interpreter.
The shared preparation loop executes them before the remaining proof text.
A native preparation error skips later requests. `proofScriptPrepare_cost_le`
bounds this loop by its native callback costs and at most three control
operations per request, plus one for the final text node.

The failure-report selector has an output-equivalence theorem and a bound
that includes the selected analyzer, probe-error scan, and surrounding rows.
String operations have unit cost, independent of their character counts.

Reuse comparison has a counted core with two checker costs and one Boolean
comparison. The local driver bounds take each callback's cost separately;
`Complexity/Certification.lean` supplies concrete counted registry operands.
Neither module bounds excluded proof elaboration or every operation in a
whole `ufo_model` command.
-/

namespace LeanUfo.UFO.DSL.Complexity

open CertificateChecking
open private checkedAxiomProofScript checkerCertificateProof? certAxiomCounterexampleScript
  checkerSoundnessName? checkerCounterexampleBackend?
  CheckerCounterexampleBackend.checkFn
  from LeanUfo.UFO.DSL.Certificate.Generation
open private timeoutMessageCosted probeTimeoutCosted probeErrorRowsCosted
  from LeanUfo.UFO.DSL.Diagnostic.Analysis
open private ax68ClosureAnalysisCosted_cost_le ax68ClosureAnalysisCostBound
  from LeanUfo.UFO.DSL.Diagnostic.AxiomAnalysis

/-- Erase checker costs before the comparison, as the generated proof does.
Both evaluations use the same counted Boolean comparison primitive. -/
theorem compareChecks_erasure (child parent : Unit → Costed Bool) :
    (compareChecksCosted child parent).value =
      resultsAgree (child ()).value (parent ()).value := rfl

/-- Both checker callbacks run once, in child/parent order, before one Boolean
comparison. Each operand cost includes all work in that callback, including
model construction when the callback performs it. -/
theorem reuseComparison_cost (child parent : Unit → Costed Bool) :
    (compareChecksCosted child parent).cost =
      (child ()).cost + (parent ()).cost + 1 := by
  simp [compareChecksCosted, resultsAgreeCosted, Costed.bind, Costed.tick, Nat.add_assoc]

/-- Compose the counted computations named by one emitted request. The
arguments are its resolved checker calls, including any model reconstruction.
The emitter resolves names before generating the expression; no runtime name
lookup or request dispatch is charged here. This models the emitted Boolean
expression, not the cost of traversing request metadata in this interpreter. -/
def nativeRequestCosted (request : NativeCall)
    (child parent : Unit → Costed Bool) : Costed Bool :=
  match request with
  | .expect _ answer => compareChecksCosted child (fun _ => Costed.pure answer)
  | .agree .. => compareChecksCosted child parent

/-- The generated proof uses `resultsAgree` on the erased checker results.
Expected-answer requests compare with a literal and do not evaluate a parent.
The surrounding native-decision tactic and its proof construction are excluded. -/
theorem nativeRequest_erasure (request : NativeCall)
    (child parent : Unit → Costed Bool) :
    (nativeRequestCosted request child parent).value =
      match request with
      | .expect _ answer => resultsAgree (child ()).value answer
      | .agree .. => resultsAgree (child ()).value (parent ()).value := by
  cases request <;> rfl

/-- This is the cost of the executed checker components plus one Boolean
comparison, not a size-based envelope. A parent contributes only on agreement. -/
theorem nativeRequest_cost (request : NativeCall)
    (child parent : Unit → Costed Bool) :
    (nativeRequestCosted request child parent).cost =
      (child ()).cost +
        (match request with | .expect .. => 0 | .agree .. => (parent ()).cost) + 1 := by
  cases request <;>
    simp [nativeRequestCosted, reuseComparison_cost, Costed.pure_cost]

/-- Expected-answer requests do not depend on a parent computation, in either
their result or their cost. The emitted term contains only the child checker. -/
theorem nativeRequest_expect_parent_irrelevant (field : String) (answer : Bool)
    (child parent other : Unit → Costed Bool) :
    nativeRequestCosted (.expect field answer) child parent =
      nativeRequestCosted (.expect field answer) child other := rfl

/-- Rebuild tables and the finite model, then run the checker on that returned
model. This is one reconstruction path. A reused native model can omit that
path; the per-call upper bound allows it without assuming runtime memoization. -/
def reconstructedCheckCosted (ast : ModelAST)
    (hw : 0 < ast.worldCount) (ht : 0 < ast.thingCount)
    (bounded : Production.explicitModelWellBounded ast)
    (check : FiniteModel4 → Costed Bool) : Costed Bool :=
  Costed.bind (compileVerifiedModelCosted ast hw ht bounded) check

theorem reconstructedCheck_erasure (ast : ModelAST)
    (hw : 0 < ast.worldCount) (ht : 0 < ast.thingCount)
    (bounded : Production.explicitModelWellBounded ast)
    (check : FiniteModel4 → Costed Bool) :
    (reconstructedCheckCosted ast hw ht bounded check).value =
      (check (compileVerifiedModel ast hw ht bounded)).value := by
  simp only [reconstructedCheckCosted, Costed.bind_value, compileVerifiedModelCosted_value]

theorem reconstructedCheck_cost (ast : ModelAST)
    (hw : 0 < ast.worldCount) (ht : 0 < ast.thingCount)
    (bounded : Production.explicitModelWellBounded ast)
    (check : FiniteModel4 → Costed Bool) :
    (reconstructedCheckCosted ast hw ht bounded check).cost =
      (compileVerifiedModelCosted ast hw ht bounded).cost +
        (check (compileVerifiedModel ast hw ht bounded)).cost := by
  simp only [reconstructedCheckCosted, Costed.bind_cost, compileVerifiedModelCosted_value]

/-- Both checked-proof entry points render this same single request. A reuse
request contains two checker evaluations inside one Boolean decision. -/
theorem checkedScript_nativeCalls (field : CertField) (reuse : Option Lean.Name) :
    (checkedAxiomProofScript field reuse).nativeCalls =
      [match reuse with
       | none => .expect field.field true
       | some parent => .agree field.field parent] := by
  cases reuse <;> rfl

theorem checkedScript_checkerCalls (field : CertField) (reuse : Option Lean.Name) :
    (checkedAxiomProofScript field reuse).checkerCalls = if reuse.isSome then 2 else 1 := by
  cases reuse <;> rfl

/-- Semantic proof scripts have at most one native checker call, for the
future prerequisites of axioms 73 and 78. Other premises reuse existing proofs.
This bounds requests; a native preparation error may prevent their completion. -/
theorem semanticScript_checkerCalls (field : CertField) (script : ProofScript)
    (selected : checkerCertificateProof? field = some script) :
    script.checkerCalls ≤ 1 := by
  unfold checkerCertificateProof? at selected
  split at selected
  all_goals try (cases selected; decide)
  cases found : checkerSoundnessName? field <;>
    simp [found] at selected
  subst script
  simp [ProofScript.checkerCalls, ProofScript.nativeCalls]

/-- A counterexample probe requests at most two checker evaluations, ordered
with any future prerequisite first. The axiom-99 general tactic fallback is
excluded proof work, not a registered native-call request. -/
theorem counterexampleScript_checkerCalls (field : CertField) :
    (certAxiomCounterexampleScript field).checkerCalls ≤ 2 := by
  unfold certAxiomCounterexampleScript
  split_ifs
  all_goals simp [ProofScript.checkerCalls, ProofScript.nativeCalls, NativeCall.checkerCalls]
  cases checkerCounterexampleBackend? field <;>
    simp [ProofScript.nativeCalls, NativeCall.checkerCalls]

/-- Packaging the counterexample script does not add checker requests. -/
theorem counterexampleProofSource_checkerCalls (field : CertField) :
    (certAxiomCounterexampleCheck field).script.checkerCalls ≤ 2 :=
  counterexampleScript_checkerCalls field

/-- Stopping before a later native decision cannot increase the number of
requested checker invocations. This is a prefix bound, not a claim that all
requests were executed or a bound on the excluded proof engine. -/
theorem script_prefix_checkerCalls_le (script : ProofScript) (limit : Nat) :
    ((script.nativeCalls.take limit).map NativeCall.checkerCalls).sum ≤ script.checkerCalls := by
  have prefixBound (calls : List NativeCall) (limit : Nat) :
      ((calls.take limit).map NativeCall.checkerCalls).sum ≤
        (calls.map NativeCall.checkerCalls).sum := by
    induction calls generalizing limit with
    | nil => simp
    | cons request rest ih =>
        cases limit with
        | zero => simp
        | succ n =>
            simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
            exact Nat.add_le_add_left (ih n) _
  exact prefixBound script.nativeCalls limit

/-- For every registered field with a direct counterexample backend, the
completeness proof and the typed native request name the same checker. The
finite registry makes this a closed fact checked by the kernel. -/
theorem registeredCounterexample_names_agree :
    certFields.all (fun field =>
      match checkerCounterexampleBackend? field with
      | none => true
      | some backend => CheckerCounterexampleBackend.checkFn backend ==
          checkerFunctionName field.field) = true := by
  decide +kernel

/-- Preparation erasure preserves both the rendered proof and the first
error. Both instantiations execute the same script loop. -/
theorem proofScriptPrepare_erasure {ε : Type} (script : ProofScript)
    (native : NativeCall → Costed (Except ε String)) :
    (script.prepareCosted native).value =
      script.prepare (m := Id) (fun _ => pure ()) (fun request => (native request).value) := by
  induction script with
  | done text => rfl
  | call before request rest ih =>
      cases h : (native request).value <;>
        simp [ProofScript.prepareCosted, ProofScript.prepare, Costed.bind, Costed.pure,
          Costed.tick, Bind.bind, Pure.pure, h] at *
      exact congrArg (Except.map (fun text => before ++ request.proofTermWith _ ++ text)) ih

/-- Each visited request has its own returned native cost. The executor adds
at most three branch operations per request and one for the final text node.
Failure can omit the suffix, so the full-script sum is an upper bound. -/
theorem proofScriptPrepare_cost_le {ε : Type} (script : ProofScript)
    (native : NativeCall → Costed (Except ε String)) :
    (script.prepareCosted native).cost ≤
      (script.nativeCalls.map (fun request => (native request).cost)).sum +
        3 * script.nativeCalls.length + 1 := by
  induction script with
  | done text => simp [ProofScript.prepareCosted, ProofScript.prepare, ProofScript.nativeCalls,
      Costed.bind, Costed.pure, Costed.tick, Bind.bind, Pure.pure]
  | call before request rest ih =>
      cases h : (native request).value <;>
        simp [ProofScript.prepareCosted, ProofScript.prepare, ProofScript.nativeCalls,
          Costed.bind, Costed.pure, Costed.tick, Bind.bind, Pure.pure, h] at * <;> omega

/-- Algorithmic part of one frontend proof attempt. Native preparation runs
the shared executor. `proofFailed` is the result supplied by excluded Lean
elaboration, not an executable callback assigned zero cost. A preparation
error skips that proof result and reports failure immediately. Wrapping text
and translating proof-engine errors remain outside the algorithmic count. -/
def preparedProofAttemptCosted {ε : Type} (source : ProofSource)
    (native : NativeCall → Costed (Except ε String)) (proofFailed : Bool) : Costed Bool :=
  Costed.map (fun prepared =>
    match prepared with
    | .error _ => true
    | .ok _ => proofFailed) (source.script.prepareCosted native)

theorem preparedProofAttempt_erasure {ε : Type} (source : ProofSource)
    (native : NativeCall → Costed (Except ε String)) (proofFailed : Bool) :
    (preparedProofAttemptCosted source native proofFailed).value =
      match source.script.prepare (m := Id) (fun _ => pure ())
          (fun request => (native request).value) with
      | .error _ => true
      | .ok _ => proofFailed := by
  simp only [preparedProofAttemptCosted, Costed.map_value, proofScriptPrepare_erasure]
  rfl

theorem preparedProofAttempt_cost {ε : Type} (source : ProofSource)
    (native : NativeCall → Costed (Except ε String)) (proofFailed : Bool) :
    (preparedProofAttemptCosted source native proofFailed).cost =
      (source.script.prepareCosted native).cost := rfl

/-- Every native decision contains at least one checker invocation. This
connects the request-traversal term to the per-field checker-count bounds. -/
theorem script_nativeCalls_le_checkerCalls (script : ProofScript) :
    script.nativeCalls.length ≤ script.checkerCalls := by
  induction script with
  | done text => simp [ProofScript.nativeCalls, ProofScript.checkerCalls]
  | call before request rest ih =>
      cases request <;>
        simp [ProofScript.nativeCalls, ProofScript.checkerCalls, NativeCall.checkerCalls] at * <;>
        omega

/-- Uniform request bounds compose with the shared preparation loop. This
lemma is used only after the native operand costs have been bounded; it does
not assign a cost to proof production or elaboration. -/
theorem preparedProofAttempt_cost_le_uniform {ε : Type} (source : ProofSource)
    (native : NativeCall → Costed (Except ε String)) (proofFailed : Bool) (budget : Nat)
    (nativeBound : ∀ request ∈ source.script.nativeCalls, (native request).cost ≤ budget) :
    (preparedProofAttemptCosted source native proofFailed).cost ≤
      source.script.nativeCalls.length * (budget + 3) + 1 := by
  have sumBound (requests : List NativeCall)
      (included : ∀ request ∈ requests, request ∈ source.script.nativeCalls) :
      (requests.map (fun request => (native request).cost)).sum ≤ requests.length * budget := by
    induction requests with
    | nil => simp
    | cons request rest ih =>
        have head := nativeBound request (included request (by simp))
        have tail := ih (fun r hr => included r (by simp [hr]))
        simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
        omega
  have operands := sumBound source.script.nativeCalls (fun _ member => member)
  have loop := proofScriptPrepare_cost_le source.script native
  rw [preparedProofAttempt_cost]
  simp only [Nat.mul_add]
  omega

/-- Both semantic proof forms use at most one native checker request. The
ordinary fallback has no registered request and remains excluded proof work. -/
theorem semanticProofSource_checkerCalls (W T : Nat) (tables : FactTables)
    (field : CertField) (declaration : Bool) :
    (if declaration then certAxiomTheorem W T tables field
      else certAxiomProofCheck W T tables field).script.checkerCalls ≤ 1 := by
  cases selected : checkerCertificateProof? field with
  | none =>
      cases declaration <;>
        simp [certAxiomTheorem, certAxiomProofCheck, selected,
          ProofScript.checkerCalls, ProofScript.nativeCalls]
  | some script =>
      have bound := semanticScript_checkerCalls field script selected
      cases declaration <;>
        simpa only [Bool.false_eq_true, ↓reduceIte, certAxiomTheorem,
          certAxiomProofCheck, selected] using bound

theorem preparedSemanticProof_cost_le {ε : Type} (W T : Nat) (tables : FactTables)
    (field : CertField) (declaration : Bool)
    (native : NativeCall → Costed (Except ε String)) (proofFailed : Bool) (budget : Nat)
    (nativeBound : ∀ request ∈ (if declaration then certAxiomTheorem W T tables field
        else certAxiomProofCheck W T tables field).script.nativeCalls,
      (native request).cost ≤ budget + 1) :
    (preparedProofAttemptCosted (if declaration then certAxiomTheorem W T tables field
      else certAxiomProofCheck W T tables field) native proofFailed).cost ≤ budget + 5 := by
  let source := if declaration then certAxiomTheorem W T tables field
    else certAxiomProofCheck W T tables field
  have count : source.script.nativeCalls.length ≤ 1 :=
    (script_nativeCalls_le_checkerCalls source.script).trans
      (semanticProofSource_checkerCalls W T tables field declaration)
  have bound := preparedProofAttempt_cost_le_uniform source native proofFailed (budget + 1) nativeBound
  have scaled := Nat.mul_le_mul_right (budget + 1 + 3) count
  change (preparedProofAttemptCosted source native proofFailed).cost ≤ _
  omega

/-- Both checked-proof forms prepare the same single request. A fresh request
has one checker operand; a reused request has two. The remaining five units
cover the comparison and preparation control, not excluded proof work. -/
theorem preparedCheckedProof_cost_le {ε : Type}
    (field : CertField) (reuse : Option Lean.Name) (declaration : Bool)
    (native : NativeCall → Costed (Except ε String)) (proofFailed : Bool) (budget : Nat)
    (nativeBound : (native (match reuse with
      | none => .expect field.field true
      | some parent => .agree field.field parent)).cost ≤
        (if reuse.isSome then 2 else 1) * budget + 1) :
    (preparedProofAttemptCosted
      (if declaration then checkedAxiomTheorem field reuse else checkedAxiomProofCheck field reuse)
      native proofFailed).cost ≤ (if reuse.isSome then 2 else 1) * budget + 5 := by
  have preparation := proofScriptPrepare_cost_le (checkedAxiomProofScript field reuse) native
  rw [checkedScript_nativeCalls] at preparation
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.length_cons, List.length_nil] at preparation
  cases declaration <;>
    simp only [Bool.false_eq_true, ↓reduceIte, preparedProofAttempt_cost,
      checkedAxiomTheorem, checkedAxiomProofCheck] <;> omega

/-- The production checked driver, with each callback's algorithm work supplied
by its generated proof source. The Boolean index selects declaration versus
trial. Proof-production and elaboration outcomes are external inputs; all
native checker costs remain in `native`. Fresh fallback uses `none` and does
not repeat the planner. -/
def preparedCheckedAttemptsCosted {ε : Type} (field : CertField)
    (plan : Unit → Costed (Option Lean.Name))
    (native : Bool → Option Lean.Name → NativeCall → Costed (Except ε String))
    (proofFailed : Bool → Option Lean.Name → Bool) : Costed Result :=
  let attempt := fun declaration reuse => preparedProofAttemptCosted
    (if declaration then checkedAxiomTheorem field reuse else checkedAxiomProofCheck field reuse)
    (native declaration reuse) (proofFailed declaration reuse)
  runCosted plan (attempt false) (attempt true)
    (fun _ => attempt false none) (fun _ => attempt true none)

/-- Erasing costs preserves the driver's result. Both sides use `run`, so
instrumentation does not select a different callback sequence. -/
theorem checkedField_erasure (plan : Unit → Costed (Option Lean.Name))
    (p d : Option Lean.Name → Costed Bool) (fp fd : Unit → Costed Bool) :
    (runCosted plan p d fp fd).value =
      run (m := Id) (fun _ => pure ()) (fun u => (plan u).value)
        (fun u => (p u).value) (fun u => (d u).value)
        (fun u => (fp u).value) (fun u => (fd u).value) := by
  cases hplan : plan () with
  | mk reuse cost =>
    cases hp : (p reuse).value <;> cases hd : (d reuse).value <;>
      cases hfp : (fp ()).value <;> cases hfd : (fd ()).value <;> cases reuse <;>
      simp [runCosted, run, Costed.bind, Costed.pure, Costed.tick,
        Bind.bind, Pure.pure, hplan, hp, hd, hfp, hfd]

/-- Plan once and allow all four proof callbacks. Their initial parent is the
planner's actual result. Exact counts include only callbacks on the selected
branch; the five additional operations are driver decisions. -/
theorem checkedField_cost_le (plan : Unit → Costed (Option Lean.Name))
    (p d : Option Lean.Name → Costed Bool) (fp fd : Unit → Costed Bool) :
    (runCosted plan p d fp fd).cost ≤
      (plan ()).cost + (p (plan ()).value).cost + (d (plan ()).value).cost +
        (fp ()).cost + (fd ()).cost + 5 := by
  cases hplan : plan () with
  | mk reuse cost =>
    cases hp : (p reuse).value <;> cases hd : (d reuse).value <;>
      cases hfp : (fp ()).value <;> cases hfd : (fd ()).value <;> cases reuse <;>
      simp [runCosted, run, Costed.bind, Costed.pure, Costed.tick,
        Bind.bind, Pure.pure, hplan, hp, hd, hfp, hfd] <;> omega

/-- Initial reuse can run two two-operand decisions. Fresh fallback can run
two one-operand decisions. Preparation contributes at most twenty operations
across these four attempts, and the retry driver contributes at most five.
The planner's actual cost is added once. -/
theorem preparedCheckedAttempts_cost_le {ε : Type} (field : CertField)
    (plan : Unit → Costed (Option Lean.Name))
    (native : Bool → Option Lean.Name → NativeCall → Costed (Except ε String))
    (proofFailed : Bool → Option Lean.Name → Bool) (budget : Nat)
    (nativeBound : ∀ declaration reuse,
      (native declaration reuse (match reuse with
        | none => .expect field.field true
        | some parent => .agree field.field parent)).cost ≤
          (if reuse.isSome then 2 else 1) * budget + 1) :
    (preparedCheckedAttemptsCosted field plan native proofFailed).cost ≤
      (plan ()).cost + 6 * budget + 25 := by
  let attempt := fun declaration reuse => preparedProofAttemptCosted
    (if declaration then checkedAxiomTheorem field reuse else checkedAxiomProofCheck field reuse)
    (native declaration reuse) (proofFailed declaration reuse)
  have one (declaration) (reuse) :
      (attempt declaration reuse).cost ≤ (if reuse.isSome then 2 else 1) * budget + 5 :=
    preparedCheckedProof_cost_le field reuse declaration (native declaration reuse)
      (proofFailed declaration reuse) budget (nativeBound declaration reuse)
  have initialTrial := one false (plan ()).value
  have initialDeclaration := one true (plan ()).value
  have freshTrial := one false none
  have freshDeclaration := one true none
  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Nat.one_mul]
    at freshTrial freshDeclaration
  have factor : (if (plan ()).value.isSome then 2 else 1) ≤ 2 := by split <;> omega
  have scaled := Nat.mul_le_mul_right budget factor
  have driver := checkedField_cost_le plan (attempt false) (attempt true)
    (fun _ => attempt false none) (fun _ => attempt true none)
  change (runCosted plan (attempt false) (attempt true)
    (fun _ => attempt false none) (fun _ => attempt true none)).cost ≤ _
  omega

/-- Erasure preserves the initial/fresh attempt sequence, including failure
before declaration and the returned reuse choice. Lean's proof outcomes remain
inputs on both sides; the executor's native computations are erased in place. -/
theorem preparedCheckedAttempts_erasure {ε : Type} (field : CertField)
    (plan : Unit → Costed (Option Lean.Name))
    (native : Bool → Option Lean.Name → NativeCall → Costed (Except ε String))
    (proofFailed : Bool → Option Lean.Name → Bool) :
    (preparedCheckedAttemptsCosted field plan native proofFailed).value =
      let attempt := fun declaration reuse =>
        let source := if declaration then checkedAxiomTheorem field reuse else checkedAxiomProofCheck field reuse
        match source.script.prepare (m := Id) (fun _ => pure ())
            (fun request => (native declaration reuse request).value) with
        | .error _ => true
        | .ok _ => proofFailed declaration reuse
      run (m := Id) (fun _ => pure ()) (fun _ => (plan ()).value)
        (attempt false) (attempt true) (fun _ => attempt false none) (fun _ => attempt true none) := by
  simp only [preparedCheckedAttemptsCosted, checkedField_erasure, preparedProofAttempt_erasure]
  rfl

/-- Other fields skip closure search entirely. The axiom-68 branch composes
the existing bearer-search bound with its field comparison and branch. -/
theorem certificationFieldPrecheck_cost_le (W T : Nat) (tables : FactTables) (field : String) :
    (certificationFieldPrecheckCosted W T tables field).cost ≤
      2 * (W * (T * (T * (11 * T + 26) + 19) + 3)) + 6 := by
  have h := Costed.andThen_cost_le (Costed.tick (field == "ax68"))
    (fun _ => hasAx68ClosureFailureCosted W T tables) 1 _ (by rfl)
    (hasAx68ClosureFailureCosted_cost_le W T tables)
  unfold certificationFieldPrecheckCosted
  omega

theorem certificationFieldPrecheck_value (W T : Nat) (tables : FactTables) (field : String) :
    (certificationFieldPrecheckCosted W T tables field).value =
      (field == "ax68" && hasAx68ClosureFailure W T tables) := by
  simp only [certificationFieldPrecheckCosted, Costed.andThen_value, Costed.tick_value,
    hasAx68ClosureFailure]

/-- The fixed policy performs at most eight string comparisons and seven
Boolean branches. String-character work is outside the unit-cost model. -/
theorem commandProbePolicy_cost_le (field : CertField) :
    (useCommandCertificateProbeCosted field).cost ≤ 15 := by
  unfold useCommandCertificateProbeCosted
  apply Costed.orElse_cost_le _ _ 1 13 (by rfl)
  apply Costed.orElse_cost_le _ _ 1 11 (by rfl)
  apply Costed.orElse_cost_le _ _ 1 9 (by rfl)
  apply Costed.orElse_cost_le _ _ 1 7 (by rfl)
  apply Costed.orElse_cost_le _ _ 1 5 (by rfl)
  apply Costed.orElse_cost_le _ _ 1 3 (by rfl)
  exact Costed.orElse_cost_le _ _ 1 1 (by rfl) (by rfl)

theorem commandProbePolicy_value (field : CertField) :
    useCommandCertificateProbe field =
      (field.field == "ax1" || field.field == "ax2" || field.field == "ax3" ||
        field.field == "ax4" || field.field == "ax5" || field.field == "ax6" ||
        field.field == "ax44" || field.field == "ax68") := by
  simp only [useCommandCertificateProbe, useCommandCertificateProbeCosted,
    Costed.orElse_value, Costed.tick_value, Bool.or_assoc]

/-- Erasure preserves the field's result and actual reuse source through its
precheck, checked attempts, and semantic attempts. All use the same driver. -/
theorem fieldDriver_erasure (precheck : Unit → Costed Bool)
    (checked : Unit → Costed Result) (commandOnly : Unit → Costed Bool)
    (preflight : Unit → Costed Bool) (declaration : Bool → Costed Bool) :
    (runFieldCosted precheck checked commandOnly preflight declaration).value =
      runField (m := Id) (fun _ => pure ()) (fun u => (precheck u).value)
        (fun u => (checked u).value) (fun u => (commandOnly u).value)
        (fun u => (preflight u).value) (fun command => (declaration command).value) := by
  cases hp : (precheck ()).value <;> cases hc : (checked ()).value <;>
    cases hm : (commandOnly ()).value <;> cases ht : (preflight ()).value <;>
    cases hd : (declaration true).value <;> cases hf : (declaration false).value <;>
    simp [runFieldCosted, runField, Bind.bind, Pure.pure, Costed.bind, Costed.tick,
      Costed.pure, hp, hc, hm, ht, hd, hf]

/-- At most five driver decisions surround the callbacks. Only one declaration
mode can run, so its budget is the larger mode cost, not their sum. The checked
callback separately includes reuse planning and the initial/fresh driver. -/
theorem fieldDriver_cost_le (precheck : Unit → Costed Bool)
    (checked : Unit → Costed Result) (commandOnly : Unit → Costed Bool)
    (preflight : Unit → Costed Bool) (declaration : Bool → Costed Bool) :
    (runFieldCosted precheck checked commandOnly preflight declaration).cost ≤
      (precheck ()).cost + (checked ()).cost + (commandOnly ()).cost + (preflight ()).cost +
        max (declaration true).cost (declaration false).cost + 5 := by
  cases hp : (precheck ()).value <;> cases hc : (checked ()).value <;>
    cases hm : (commandOnly ()).value <;> cases ht : (preflight ()).value <;>
    cases hd : (declaration true).value <;> cases hf : (declaration false).value <;>
    simp [runFieldCosted, runField, Bind.bind, Pure.pure, Costed.bind, Costed.tick,
      Costed.pure, hp, hc, hm, ht, hd, hf] <;> omega

private theorem registryVisit_value {α : Type} (nameOf : α → String)
    (check : α → Costed Result) (progress : RegistryResult α) (field : α) :
    (runFields.visit (fun n => Costed.tick () n) nameOf check progress field).value =
      runFields.visit (m := Id) (fun _ => pure ()) nameOf
        (fun field => (check field).value) progress field := by
  cases h : progress.failedField? <;> cases hr : (check field).value <;>
    simp [runFields.visit, Bind.bind, Pure.pure, Costed.bind, Costed.tick,
      Costed.pure, h, hr]

/-- The outer loop returns the same successful prefix, reuse rows, and failed
field after erasure. The list induction is a proof specification only: the
executable driver traverses the array directly. `nameOf` reads a stored name. -/
theorem registryDriver_erasure {α : Type} (fields : Array α) (nameOf : α → String)
    (check : α → Costed Result) :
    (runFieldsCosted fields nameOf check).value =
      runFields (m := Id) (fun _ => pure ()) fields nameOf
        (fun field => (check field).value) := by
  have fold (xs : List α) (progress : RegistryResult α) :
      (xs.foldlM (runFields.visit (fun n => Costed.tick () n) nameOf check) progress).value =
        xs.foldlM (runFields.visit (m := Id) (fun _ => pure ()) nameOf
          (fun field => (check field).value)) progress := by
    induction xs generalizing progress with
    | nil => rfl
    | cons field rest ih =>
        simp only [List.foldlM_cons, Bind.bind, Costed.bind_value, ih, registryVisit_value]
  simpa [runFieldsCosted, runFields, Bind.bind, Costed.bind_value] using fold fields.toList {}

/-- Two array initializations precede the registry. Each field costs at most
seven driver operations plus its callback. After failure, visits cost three
and skip the callback. This sum therefore bounds repeated per-field execution,
not a single early-exit invocation of the aggregate Boolean checker. -/
theorem registryDriver_cost_le {α : Type} (fields : Array α) (nameOf : α → String)
    (check : α → Costed Result) :
    (runFieldsCosted fields nameOf check).cost ≤
      2 + (fields.toList.map (fun field => (check field).cost + 7)).sum := by
  have visit (progress : RegistryResult α) (field : α) :
      (runFields.visit (fun n => Costed.tick () n) nameOf check progress field).cost ≤
        (check field).cost + 7 := by
    cases h : progress.failedField? <;> cases hr : (check field).value <;>
      simp [runFields.visit, Bind.bind, Pure.pure, Costed.bind, Costed.tick,
        Costed.pure, h, hr] <;> omega
  have fold (xs : List α) (progress : RegistryResult α) :
      (xs.foldlM (runFields.visit (fun n => Costed.tick () n) nameOf check) progress).cost ≤
        (xs.map (fun field => (check field).cost + 7)).sum := by
    induction xs generalizing progress with
    | nil => simp [Pure.pure, Costed.pure]
    | cons field rest ih =>
        simp only [List.foldlM_cons, Bind.bind, Costed.bind_cost, List.map_cons, List.sum_cons]
        exact Nat.add_le_add (visit progress field) (ih _)
  simpa [runFieldsCosted, runFields, Bind.bind, Costed.bind_cost] using
    Nat.add_le_add_left (fold fields.toList {}) 2

/-- Compose both production drivers with the actual precheck and command-only
policy. W and T are explicit domain sizes. The remaining costs belong to
checked and semantic proof callbacks; this theorem does not assign a cost to
Lean elaboration or assume that an arbitrary callback is polynomial. The
constant 33 adds six precheck, fifteen policy, five field, and seven outer-loop
operations. Only the precheck's nonconstant search term depends on W and T. -/
theorem certificationRegistry_control_bound (W T : Nat) (tables : FactTables)
    (checked : CertField → Costed Result) (preflight : CertField → Costed Bool)
    (declaration : CertField → Bool → Costed Bool) :
    (runFieldsCosted certFields CertField.field fun field =>
      runFieldCosted (fun _ => certificationFieldPrecheckCosted W T tables field.field)
        (fun _ => checked field) (fun _ => useCommandCertificateProbeCosted field)
        (fun _ => preflight field) (declaration field)).cost ≤
      2 + (certFields.toList.map (fun field =>
        2 * (W * (T * (T * (11 * T + 26) + 19) + 3)) +
          (checked field).cost + (preflight field).cost +
          max (declaration field true).cost (declaration field false).cost + 33)).sum := by
  let action (field : CertField) :=
    runFieldCosted (fun _ => certificationFieldPrecheckCosted W T tables field.field)
      (fun _ => checked field) (fun _ => useCommandCertificateProbeCosted field)
      (fun _ => preflight field) (declaration field)
  let bound (field : CertField) :=
    2 * (W * (T * (T * (11 * T + 26) + 19) + 3)) +
      (checked field).cost + (preflight field).cost +
      max (declaration field true).cost (declaration field false).cost + 33
  have perField (field : CertField) : (action field).cost + 7 ≤ bound field := by
    have driver := fieldDriver_cost_le
      (fun _ => certificationFieldPrecheckCosted W T tables field.field)
      (fun _ => checked field) (fun _ => useCommandCertificateProbeCosted field)
      (fun _ => preflight field) (declaration field)
    have precheck := certificationFieldPrecheck_cost_le W T tables field.field
    have policy := commandProbePolicy_cost_le field
    dsimp only [action, bound]
    omega
  have sum (fields : List CertField) :
      (fields.map (fun field => (action field).cost + 7)).sum ≤ (fields.map bound).sum := by
    induction fields with
    | nil => simp
    | cons field rest ih =>
        simp only [List.map_cons, List.sum_cons]
        exact Nat.add_le_add (perField field) ih
  exact (registryDriver_cost_le certFields CertField.field action).trans
    (Nat.add_le_add_left (sum certFields.toList) 2)

/-- The report selector uses the actual registry result. Its cost is one
decision plus the selected analyzer, or just one decision after success. -/
theorem reportAfterRegistry_cost {α : Type} (progress : RegistryResult α)
    (analyze : α → Costed (Array String)) :
    (reportAfterRegistryCosted progress analyze).cost =
      1 + match progress.failedField? with
        | none => 0
        | some field => (analyze field).cost := by
  cases h : progress.failedField? <;>
    simp [reportAfterRegistryCosted, reportAfterRegistry, Bind.bind, Pure.pure,
      Costed.bind, Costed.tick, Costed.pure, h]

theorem reportAfterRegistry_erasure {α : Type} (progress : RegistryResult α)
    (analyze : α → Costed (Array String)) :
    (reportAfterRegistryCosted progress analyze).value =
      reportAfterRegistry (m := Id) (fun _ => pure ()) progress
        (fun field => (analyze field).value) := by
  cases h : progress.failedField? <;>
    simp [reportAfterRegistryCosted, reportAfterRegistry, Bind.bind, Pure.pure,
      Costed.bind, Costed.tick, Costed.pure, h]

/-- Derived-fact failure and registry certification are exclusive branches.
The saved precheck is charged once, with two surrounding control decisions. -/
theorem runAfterAssertions_cost_le {α : Type}
    (precheck : Costed (Option (Array String))) (proofFailed : Bool)
    (report : Option (Array String) → Costed (Array String)) (certify : Unit → Costed α) :
    (runAfterAssertionsCosted precheck proofFailed report certify).cost ≤
      precheck.cost + 2 + max (report precheck.value).cost (certify ()).cost := by
  cases saved : precheck.value <;> cases proofFailed <;>
    simp [runAfterAssertionsCosted, runAfterAssertions, Bind.bind, Pure.pure,
      Costed.bind, Costed.tick, Costed.pure, saved] <;> omega

theorem runAfterAssertions_erasure {α : Type}
    (precheck : Costed (Option (Array String))) (proofFailed : Bool)
    (report : Option (Array String) → Costed (Array String)) (certify : Unit → Costed α) :
    (runAfterAssertionsCosted precheck proofFailed report certify).value =
      runAfterAssertions (m := Id) (fun _ => pure ()) (fun _ => precheck.value)
        (fun _ => proofFailed) (fun saved => (report saved).value) (fun _ => (certify ()).value) := by
  cases saved : precheck.value <;> cases proofFailed <;>
    simp [runAfterAssertionsCosted, runAfterAssertions, Bind.bind, Pure.pure,
      Costed.bind, Costed.tick, Costed.pure, saved]

private theorem probeTimeout_value (errors : Array String) :
    (probeTimeoutCosted errors).value = errors.any (fun message =>
      let lower := message.toLower
      lower.contains "heartbeat" || lower.contains "timeout" ||
        lower.contains "maximum number of") := by
  simp [probeTimeoutCosted, anyArrayCosted_eq_list, anyListCosted_value,
    timeoutMessageCosted, Bind.bind, Costed.bind_value, Costed.orElse_value,
    Array.any_toList]

private theorem probeTimeout_cost_le (errors : Array String) :
    (probeTimeoutCosted errors).cost ≤ 9 * errors.size := by
  have h : ∀ message ∈ errors, (timeoutMessageCosted message).cost ≤ 6 := by
    intro message _
    cases h1 : message.toLower.contains "heartbeat" <;>
      cases h2 : message.toLower.contains "timeout" <;>
      simp only [timeoutMessageCosted, Bind.bind, Costed.bind_cost, Costed.tick,
        Costed.orElse, h1, h2, Bool.false_eq_true, ↓reduceIte] <;> decide
  simpa [probeTimeoutCosted, Nat.mul_comm] using
    anyArrayCosted_cost_le errors timeoutMessageCosted 6 h

private theorem probeErrorRows_value (errors : Array String) :
    (probeErrorRowsCosted errors).value =
      errors.map (fun message => s!"Counterexample probe error: {message}") := by
  simp only [probeErrorRowsCosted, Bind.bind, Costed.bind_value,
    Costed.tick_value, Costed.foldArray_value, Array.map_eq_foldl]

private theorem probeErrorRows_cost (errors : Array String) :
    (probeErrorRowsCosted errors).cost = 5 * errors.size + 1 := by
  have h := Costed.foldArray_cost_eq errors (#[] : Array String)
    (fun rows message => Costed.tick (rows.push s!"Counterexample probe error: {message}") 3)
    3 (by intros; rfl)
  simpa [probeErrorRowsCosted, Bind.bind, Costed.bind_cost, Nat.mul_comm,
    Nat.add_comm] using h

/-- Erasure preserves the report's classification, text, and row order for
every probe outcome. Timeout detection is shared between its two consumers. -/
theorem certificationFailureReport_value
    (worldNames thingNames : Array Lean.Name) (facts : Array NamedScopedFact)
    (tables : FactTables) (field : String) (failed : Bool) (errors : Array String) :
    (certificationFailureReportCosted worldNames thingNames facts tables field failed errors).value =
      if failed then
        if field == "ax99" then
          #["Ax99 did not produce a confirmed semantic counterexample.",
            "This axiom contains an existential product-family witness. The reflective checker can only inspect product-family witnesses that are explicitly stored in the finite model.",
            "When the required witness data is missing, `checkAx99 = false` means that the finite representation is incomplete for this axiom; it does not by itself prove that the semantic axiom is false."] ++
              diagnosticWitnesses worldNames thingNames facts tables field
        else
          let timedOut := errors.any fun message =>
            let lower := message.toLower
            lower.contains "heartbeat" || lower.contains "timeout" || lower.contains "maximum number of"
          let reason := if timedOut then
            "The counterexample probe reported a heartbeat/timeout-style failure. This is an operational probe limit, not a semantic counterexample."
          else
            "The counterexample probe failed without a recognized timeout. This should be treated as an unclassified probe failure, not as a semantic counterexample."
          let rows := #[s!"No counterexample proof was found for {field}.", reason] ++
            (if timedOut then #[] else errors.map (fun message => s!"Counterexample probe error: {message}"))
          if field == "ax68" then rows ++ ax68ClosureAnalysis worldNames thingNames tables else rows
      else
        #[s!"A finite counterexample was confirmed for {field}.",
          "Lean successfully proved the negation of this axiom for the generated finite model, so this is a semantic model failure rather than a counterexample-probe limit."] ++
            diagnosticWitnesses worldNames thingNames facts tables field := by
  cases failed <;> cases h99 : field == "ax99" <;> cases h68 : field == "ax68" <;>
    cases ht : (probeTimeoutCosted errors).value
  all_goals have htv := ht
  all_goals rw [probeTimeout_value] at htv
  all_goals simp only [certificationFailureReportCosted, Bind.bind, Costed.bind_value,
    Costed.tick_value, Costed.charge_value, Costed.pure_value, h99, h68, ht, htv,
    Bool.false_eq_true, ↓reduceIte, probeErrorRows_value, Costed.appendArray_value,
    diagnosticWitnesses, diagnosticWitnessesBudgeted, ax68ClosureAnalysis]

/-- The production selector composes the concrete witness and closure bounds.
E probe errors add at most 17E operations: 9E for classification, 5E for error
rows, and 3E for copying them. Witness rows cost four operations at the report
boundary and three more here. Unselected analyzers contribute no actual cost,
although this upper bound reserves space for either branch. -/
theorem certificationFailureReport_cost_le
    (worldNames thingNames : Array Lean.Name) (facts : Array NamedScopedFact)
    (tables : FactTables) (field : String) (failed : Bool) (errors : Array String) :
    (certificationFailureReportCosted worldNames thingNames facts tables field failed errors).cost ≤
      18 + 17 * errors.size +
        diagnosticWitnessesInnerCostBound worldNames thingNames facts tables field +
        7 * (diagnosticWitnesses worldNames thingNames facts tables field).size +
        ax68ClosureAnalysisCostBound worldNames.size thingNames.size +
        3 * (ax68ClosureAnalysis worldNames thingNames tables).size := by
  have ht := probeTimeout_cost_le errors
  have he := probeErrorRows_cost errors
  have hs : (probeErrorRowsCosted errors).value.size = errors.size := by
    rw [probeErrorRows_value, Array.size_map]
  have hw := diagnosticWitnessesBudgetedCosted_cost_le_inner_add_emitted
    128 worldNames thingNames facts tables field
  have hc := ax68ClosureAnalysisCosted_cost_le worldNames thingNames tables
  cases failed <;> cases h99 : field == "ax99" <;> cases h68 : field == "ax68" <;>
    cases htimeout : (probeTimeoutCosted errors).value
  all_goals simp only [certificationFailureReportCosted, Bind.bind,
    Costed.bind_cost, Costed.tick_cost,
    Costed.tick_value, Costed.appendArray_cost, Costed.charge_cost, Costed.charge_value,
    Costed.pure_cost, Array.size_empty, hs, h99, h68, htimeout, Bool.false_eq_true,
    ↓reduceIte]
  all_goals dsimp only [diagnosticWitnesses, diagnosticWitnessesBudgeted,
    ax68ClosureAnalysis] at *
  all_goals omega

end LeanUfo.UFO.DSL.Complexity
