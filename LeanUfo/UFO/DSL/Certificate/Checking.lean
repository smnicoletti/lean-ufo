import Lean.Data.Name
import LeanUfo.UFO.DSL.Complexity.CostModel

/-!
# Certificate attempt and registry drivers

The frontend first tries a generated proof without declaring its theorem.
Only a successful trial permits declaration. Failed reuse permits one fresh
attempt; a failed fresh attempt ends this field's certification.

`run` owns reuse planning and these initial/fresh attempts. The planner runs
once, and both initial attempts receive its result. `runField` surrounds them
with the closure precheck and semantic proof attempts. `runFields` visits the registry
and retains the successful prefix before the first failure. All three drivers
share production and counted control flow. `runAfterAssertions` guards registry
execution with the saved derived-fact precheck and its proof outcome;
`reportAfterRegistry` analyzes only the failed field. `charge` records decisions, array
visits, and progress writes. Erasing charges leaves callback order unchanged.
`Complexity/Certification.lean` supplies source-linked costs for the native
checker computations and diagnostic callbacks.
This separation follows the compositional cost method of Niu et al. (POPL
2022), described in `docs/dsl/complexity.md`. Proof elaboration is excluded.
-/

namespace LeanUfo.UFO.DSL.CertificateChecking

/-- Agreement also holds when both answers are false. The parent's checked
theorem is still required to conclude that the child passes. -/
@[inline] def resultsAgreeCosted (child parent : Bool) : Complexity.Costed Bool :=
  Complexity.Costed.tick (child == parent) 1

@[inline] def resultsAgree (child parent : Bool) : Bool :=
  (resultsAgreeCosted child parent).value

/-- Compose checker costs before comparing their erased answers. Generated
proofs use ordinary Boolean checker calls to keep their goals compact.
`compareChecks_erasure` proves that this composition has the same value. -/
def compareChecksCosted (child parent : Unit → Complexity.Costed Bool) :
    Complexity.Costed Bool :=
  Complexity.Costed.bind (child ()) fun childAnswer =>
    Complexity.Costed.bind (parent ()) fun parentAnswer =>
      resultsAgreeCosted childAnswer parentAnswer

/-- The generated proof uses this equivalence to recover equality of the
ordinary checker results from the counted comparison's erased result. -/
theorem resultsAgree_eq_true (child parent : Bool) :
    resultsAgree child parent = true ↔ child = parent := by
  simp [resultsAgree, resultsAgreeCosted, Complexity.Costed.tick]

inductive Result where
  | failed
  | checked (reuseFrom? : Option Lean.Name)
deriving Repr, DecidableEq

/-- Callbacks return `true` on failure, as do the frontend's elaboration probes.
The thunks prevent an unused declaration or fallback from running eagerly. -/
def run {m : Type → Type} [Monad m]
    (charge : Nat → m Unit) (plan : Unit → m (Option Lean.Name))
    (preflight declaration : Option Lean.Name → m Bool)
    (freshPreflight freshDeclaration : Unit → m Bool) :
    m Result := do
  let reuseFrom? ← plan ()
  let failed ← do
    let preflightFailed ← preflight reuseFrom?
    charge 1
    if preflightFailed then pure true else declaration reuseFrom?
  charge 1
  if failed then
    charge 1
    match reuseFrom? with
    | none => pure .failed
    | some _ =>
        let freshFailed ← do
          let preflightFailed ← freshPreflight ()
          charge 1
          if preflightFailed then pure true else freshDeclaration ()
        charge 1
        if freshFailed then pure .failed else pure (.checked none)
  else
    pure (.checked reuseFrom?)

def runCosted (plan : Unit → Complexity.Costed (Option Lean.Name))
    (preflight declaration : Option Lean.Name → Complexity.Costed Bool)
    (freshPreflight freshDeclaration : Unit → Complexity.Costed Bool) :
    Complexity.Costed Result :=
  run (fun n => Complexity.Costed.tick () n) plan
    preflight declaration freshPreflight freshDeclaration

/-- One field's precheck, checked proof, and semantic proof, in that order.
The command-only policy is evaluated once after the checked proof succeeds.
The declaration receives that result so its profiling label needs no rescan.
Each Boolean test or result match costs one driver operation. -/
def runField {m : Type → Type} [Monad m]
    (charge : Nat → m Unit) (precheck : Unit → m Bool)
    (checked : Unit → m Result) (commandOnly : Unit → m Bool)
    (semanticPreflight : Unit → m Bool) (semanticDeclaration : Bool → m Bool) : m Result := do
  let precheckFailed ← precheck ()
  charge 1
  if precheckFailed then pure .failed else
    let result ← checked ()
    charge 1
    match result with
    | .failed => pure .failed
    | .checked reuse =>
        let command ← commandOnly ()
        charge 1
        let failed ←
          if command then semanticDeclaration true else do
            let failed ← semanticPreflight ()
            charge 1
            if failed then pure true else semanticDeclaration false
        charge 1
        if failed then pure .failed else pure (.checked reuse)

def runFieldCosted (precheck : Unit → Complexity.Costed Bool)
    (checked : Unit → Complexity.Costed Result) (commandOnly : Unit → Complexity.Costed Bool)
    (semanticPreflight : Unit → Complexity.Costed Bool)
    (semanticDeclaration : Bool → Complexity.Costed Bool) : Complexity.Costed Result :=
  runField (fun n => Complexity.Costed.tick () n) precheck checked commandOnly
    semanticPreflight semanticDeclaration

/-- The completed names and reuse rows feed separate widget/manifest inputs.
They grow together only after a field's checked and semantic proofs succeed. -/
structure RegistryResult (α : Type) where
  completed : Array String := #[]
  actualReuse : Array (String × Option Lean.Name) := #[]
  failedField? : Option α := none
deriving Repr, DecidableEq

/-- Visit the registry in order. After failure, later visits pay only for the
loop, array read, and failure test. Their proof callbacks do not run.
The same driver supplies production control flow and counted composition.
`nameOf` is a stored-name accessor, `CertField.field` in production. Its one
record read is charged here; arbitrary computation of a name is not covered. -/
def runFields {m : Type → Type} [Monad m] {α : Type}
    (charge : Nat → m Unit) (fields : Array α) (nameOf : α → String)
    (check : α → m Result) : m (RegistryResult α) := do
  charge 2
  fields.foldlM (visit charge nameOf check) {}
where
  visit (charge : Nat → m Unit) (nameOf : α → String) (check : α → m Result)
      (progress : RegistryResult α) (field : α) : m (RegistryResult α) := do
    charge 3
    match progress.failedField? with
    | some _ => pure progress
    | none =>
        let result ← check field
        charge 1
        match result with
        | .failed =>
            charge 1
            pure { progress with failedField? := some field }
        | .checked reuse =>
            -- One field-name read and two writes to the progress arrays.
            charge 3
            let name := nameOf field
            pure { progress with
              completed := progress.completed.push name
              actualReuse := progress.actualReuse.push (name, reuse) }

def runFieldsCosted {α : Type} (fields : Array α) (nameOf : α → String)
    (check : α → Complexity.Costed Result) : Complexity.Costed (RegistryResult α) :=
  runFields (fun n => Complexity.Costed.tick () n) fields nameOf check

/-- The report branch retains the registry's completed prefix and reuse rows.
The failed field is carried explicitly, so callers need no second lookup or
default field when rendering diagnostics. -/
inductive RegistryReport (α : Type) where
  | checked (progress : RegistryResult α)
  | failed (progress : RegistryResult α) (field : α) (rows : Array String)
deriving Repr, DecidableEq

/-- Report at most the one field where certification stopped. A successful
registry never runs a counterexample probe or a failure analyzer. One charged
decision selects the branch; the analyzer owns its own computational costs. -/
def reportAfterRegistry {m : Type → Type} [Monad m] {α : Type}
    (charge : Nat → m Unit) (progress : RegistryResult α)
    (analyze : α → m (Array String)) : m (RegistryReport α) := do
  charge 1
  match progress.failedField? with
  | none => pure (.checked progress)
  | some field => return .failed progress field (← analyze field)

def reportAfterRegistryCosted {α : Type} (progress : RegistryResult α)
    (analyze : α → Complexity.Costed (Array String)) : Complexity.Costed (RegistryReport α) :=
  reportAfterRegistry (fun n => Complexity.Costed.tick () n) progress analyze

inductive AssertionResult (α : Type) where
  | failed (rows : Array String)
  | checked (result : α)
deriving Repr, DecidableEq

/-- The pure derived-fact precheck runs once. A known false assertion skips
its Lean proof; either kind of assertion failure skips registry certification.
Report selection receives the saved precheck result rather than rerunning it. -/
def runAfterAssertions {m : Type → Type} [Monad m] {α : Type}
    (charge : Nat → m Unit) (precheck : Unit → m (Option (Array String)))
    (proofFailed : Unit → m Bool) (report : Option (Array String) → m (Array String))
    (certify : Unit → m α) : m (AssertionResult α) := do
  let saved ← precheck ()
  charge 1
  let failed ← match saved with
    | some _ => pure true
    | none => proofFailed ()
  charge 1
  if failed then return .failed (← report saved)
  else return .checked (← certify ())

/-- `proofFailed` is an observed result of excluded Lean proof work. The
precheck, selected report, and certification callbacks retain their costs. -/
def runAfterAssertionsCosted {α : Type}
    (precheck : Complexity.Costed (Option (Array String))) (proofFailed : Bool)
    (report : Option (Array String) → Complexity.Costed (Array String))
    (certify : Unit → Complexity.Costed α) : Complexity.Costed (AssertionResult α) :=
  runAfterAssertions (fun n => Complexity.Costed.tick () n) (fun _ => precheck)
    (fun _ => Complexity.Costed.pure proofFailed) report certify

end LeanUfo.UFO.DSL.CertificateChecking
