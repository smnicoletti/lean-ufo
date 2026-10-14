import LeanUfo.UFO.DSL.Certificate.Generation
import LeanUfo.UFO.DSL.Complexity.Frontend

/-!
# Certificate prerequisite reuse

These tests protect the registry order and generated checker calls on which
the frontend's cost composition depends. They inspect both the trial proof
and the declaration, since each is elaborated separately. Counterexample
probes must not refer to a checked theorem for the failed field: its preflight
can fail before that theorem exists. End-to-end certification and diagnostic
fixtures separately check elaboration and semantic outcomes.
-/

namespace LeanUfo.Test.Certificates.Generation

open LeanUfo.UFO.DSL
open private checkedAxiomProofScript checkerCertificateProof? certAxiomCounterexampleScript
  from LeanUfo.UFO.DSL.Certificate.Generation

-- Certificate explanations preserve the strict symbol from printed (a108).
example : certFormula "ax108" =
    "categorizes(t₁, t₂) ↔ Type(t₁) ∧ ∀ t₃, t₃ :: t₁ → t₃ ⊏ t₂" := rfl

private def registryField (name : String) : CertField :=
  match certFields.find? (·.field == name) with
  | some field => field
  | none => ⟨"missing", "False"⟩

private def precedes (earlier later : String) : Bool :=
  let fields := (certFields.map (·.field)).toList
  fields.contains earlier && fields.contains later &&
    decide (fields.idxOf earlier < fields.idxOf later)

-- Earlier checked declarations are available; future prerequisites are not.
example : ["ax47", "ax72"].all (precedes · "ax73") = true := by native_decide
example : precedes "ax73" "ax75" = true := by native_decide
example : ["ax48", "ax52", "ax72", "ax75", "ax77"].all
    (precedes · "ax78") = true := by native_decide
example : precedes "ax78" "ax79" = true := by native_decide
example : ["ax72", "ax75"].all (precedes · "ax79") = true := by native_decide

private def nativeCalls (source : String) : Nat :=
  (source.splitOn "native_decide").length - 1

private def trial (name : String) : String :=
  (certAxiomProofCheck 0 0 {} (registryField name)).render

private def declaration (name : String) : String :=
  (certAxiomTheorem 0 0 {} (registryField name)).render

private def probe (name : String) : String :=
  (certAxiomCounterexampleCheck (registryField name)).render

-- Requests and emitted terms come from the same script. The explicit native
-- type fixes both the field and expected answer, including failure probes.
example : (certAxiomCounterexampleScript (registryField "ax73")).nativeCalls =
    [.expect "ax75" true, .expect "ax73" false] := by native_decide
example : (certAxiomCounterexampleScript (registryField "ax78")).nativeCalls =
    [.expect "ax79" true, .expect "ax78" false] := by native_decide
example : (certAxiomCounterexampleScript (registryField "ax79")).nativeCalls =
    [.expect "ax79" false] := by native_decide

example : certFields.all (fun field =>
    let script := checkedAxiomProofScript field none
    decide (script.nativeCalls = [.expect field.field true]) &&
      script.render.contains
        s!"(by native_decide : LeanUfo.UFO.DSL.CertificateChecking.resultsAgree (LeanUfo.UFO.DSL.Checker.{checkerFunctionName field.field} data) true = true)") =
      true := by native_decide

example : certFields.all (fun field =>
    let script := checkedAxiomProofScript field (some `Parent)
    decide (script.nativeCalls = [.agree field.field `Parent]) &&
      decide (script.checkerCalls = 2)) = true := by native_decide

-- The only raw native fallback is axiom 99's excluded general proof tactic.
-- All registered-check decisions must appear as typed request nodes.
example : certFields.all (fun field =>
    let script := certAxiomCounterexampleScript field
    if field.field == "ax99" then
      decide (script.nativeCalls = []) && script.render.contains "try grind"
    else decide (script.nativeCalls.length = nativeCalls script.render)) = true := by native_decide

example : certFields.all (fun field =>
    match checkerCertificateProof? field with
    | none => false
    | some script => decide (script.nativeCalls.length = nativeCalls script.render)) = true :=
  by native_decide

example (field : CertField) (reuse : Option Lean.Name) :
    (checkedAxiomProofScript field reuse).checkerCalls = if reuse.isSome then 2 else 1 :=
  Complexity.checkedScript_checkerCalls field reuse

-- Proof sources keep native requests available to the executor without
-- rendering tactic text. The axiom-99 fallback is an ordinary completed script.
example : (certAxiomProofCheck 0 0 {} (registryField "ax73")).script.nativeCalls =
    [.expect "ax75" true] := by native_decide
example : (certAxiomProofCheck 0 0 {} (registryField "ax99")).script.nativeCalls = [] :=
  by native_decide
example : (certAxiomCounterexampleCheck (registryField "ax99")).script.nativeCalls = [] :=
  by native_decide

-- These limits reproduce the options already present in each generated source.
-- They describe execution preparation and do not enlarge a proof's budget.
example : let source := checkedAxiomTheorem (registryField "ax73")
  source.maxHeartbeats? = some 1000000 ∧ source.maxRecDepth? = some 20000 := by native_decide
example : let source := checkedAxiomProofCheck (registryField "ax73")
  source.maxHeartbeats? = none ∧ source.maxRecDepth? = none := by native_decide
example : let source := certAxiomProofCheck 0 0 {} (registryField "ax73")
  source.maxHeartbeats? = some 1000000 ∧ source.maxRecDepth? = none := by native_decide
example : let source := certAxiomCounterexampleCheck (registryField "ax73")
  source.maxHeartbeats? = some 1000000 ∧ source.maxRecDepth? = some 20000 := by native_decide
example : let source := certAxiomCounterexampleCheck (registryField "ax99")
  source.maxHeartbeats? = some 1000000 ∧ source.maxRecDepth? = none := by native_decide

-- A stop after the future prerequisite retains one checker request, not two.
example : ((certAxiomCounterexampleScript (registryField "ax73")).nativeCalls.take 1).map
    CertificateChecking.NativeCall.checkerCalls = [1] := by native_decide
example (script : CertificateChecking.ProofScript) (limit : Nat) :
    ((script.nativeCalls.take limit).map CertificateChecking.NativeCall.checkerCalls).sum ≤
      script.checkerCalls := Complexity.script_prefix_checkerCalls_le script limit

-- Every reuse proof calls the comparison erasure and still requires the
-- parent's checked theorem. Cost records stay out of generated proof goals.
example : certFields.all (fun field =>
    let source := (checkedAxiomProofCheck field (some `Parent)).render
    source.contains "CertificateChecking.resultsAgree_eq_true" &&
    source.contains s!"Parent.{checkedTheoremName field.field}" &&
    !source.contains "Costed") = true := by native_decide
example : certFields.all (fun field =>
    let source := (checkedAxiomTheorem field (some `Parent)).render
    source.contains "CertificateChecking.resultsAgree_eq_true" &&
    source.contains s!"Parent.{checkedTheoremName field.field}" &&
    !source.contains "Costed") = true := by native_decide

example : ∀ child parent : Bool,
    CertificateChecking.resultsAgreeCosted child parent =
      ⟨child == parent, 1⟩ := by decide
example : ∀ child parent : Bool,
    CertificateChecking.compareChecksCosted
      (fun _ => Complexity.Costed.tick child 10)
      (fun _ => Complexity.Costed.tick parent 20) =
      ⟨child == parent, 31⟩ := by decide

example : ∀ child answer : Bool,
    Complexity.nativeRequestCosted (.expect "ax75" answer)
      (fun _ => Complexity.Costed.tick child 10)
      (fun _ => Complexity.Costed.tick false 1000000) =
        ⟨child == answer, 11⟩ := by decide

example : ∀ child parent : Bool,
    Complexity.nativeRequestCosted (.agree "ax75" `Parent)
      (fun _ => Complexity.Costed.tick child 10)
      (fun _ => Complexity.Costed.tick parent 20) =
        ⟨child == parent, 31⟩ := by decide

example (field : String) (answer : Bool)
    (child parent other : Unit → Complexity.Costed Bool) :
    Complexity.nativeRequestCosted (.expect field answer) child parent =
      Complexity.nativeRequestCosted (.expect field answer) child other :=
  Complexity.nativeRequest_expect_parent_irrelevant field answer child parent other

-- Inspect every registered field, not only the special prerequisite cases.
-- These are generated-source regressions, not execution counts: one reuse
-- decision compares child and parent checks, and a failed proof can stop early.
example : certFields.all (fun field =>
    nativeCalls (checkedAxiomProofCheck field none).render == 1) = true := by native_decide
example : certFields.all (fun field =>
    nativeCalls (checkedAxiomTheorem field none).render == 1) = true := by native_decide
example : certFields.all (fun field =>
    nativeCalls (checkedAxiomProofCheck field (some `Parent)).render == 1) = true :=
  by native_decide
example : certFields.all (fun field =>
    nativeCalls (checkedAxiomTheorem field (some `Parent)).render == 1) = true :=
  by native_decide
example : (certFields.filter useCommandCertificateProbe).map CertField.field =
    #["ax1", "ax2", "ax3", "ax4", "ax5", "ax6", "ax44", "ax68"] := by native_decide
example : (certFields.filter (fun field =>
    nativeCalls (certAxiomProofCheck 0 0 {} field).render > 0)).map CertField.field =
    #["ax73", "ax78"] := by native_decide
example : (certFields.filter (fun field =>
    (certAxiomCounterexampleCheck field).render.contains "try grind")).map CertField.field =
    #["ax99"] := by native_decide

-- Only future prerequisites run during the semantic proof: check 75 for
-- axiom 73 and check 79 for axiom 78. Axiom 79 reuses all its premises.
example : nativeCalls (trial "ax73") = 1 := by native_decide
example : nativeCalls (declaration "ax73") = 1 := by native_decide
example : nativeCalls (trial "ax78") = 1 := by native_decide
example : nativeCalls (declaration "ax78") = 1 := by native_decide
example : nativeCalls (trial "ax79") = 0 := by native_decide
example : nativeCalls (declaration "ax79") = 0 := by native_decide

example : ["checked_ax47", "checked_ax72", "checked_ax73"].all
    (fun name => (trial "ax73").contains name) = true := by native_decide
example : ["checked_ax48", "checked_ax52", "checked_ax72", "checked_ax75",
    "checked_ax77", "checked_ax78"].all
    (fun name => (trial "ax78").contains name) = true := by native_decide
example : ["checked_ax72", "checked_ax75", "checked_ax79"].all
    (fun name => (trial "ax79").contains name) = true := by native_decide

-- A failed field is still evaluated as false. Its earlier prerequisites use
-- existing proofs, and a later prerequisite still runs before that test.
example : nativeCalls (probe "ax73") = 2 := by native_decide
example : nativeCalls (probe "ax78") = 2 := by native_decide
example : nativeCalls (probe "ax79") = 1 := by native_decide
example : (probe "ax73").contains "checked_ax73" = false := by native_decide
example : (probe "ax78").contains "checked_ax78" = false := by native_decide
example : (probe "ax79").contains "checked_ax79" = false := by native_decide
example : (probe "ax73").contains
    "resultsAgree (LeanUfo.UFO.DSL.Checker.checkAx75 data) true = true)" = true :=
  by native_decide
example : (probe "ax78").contains
    "resultsAgree (LeanUfo.UFO.DSL.Checker.checkAx79 data) true = true)" = true :=
  by native_decide

private def parent? (reuse : Bool) : Option Lean.Name :=
  if reuse then some `Parent else none

-- This sum counts only native algorithm work in the supplied prefix. Proof
-- text and traversal of the metadata list are outside that cost boundary.
private def prefixAlgorithmCost (script : CertificateChecking.ProofScript) (limit : Nat) : Nat :=
  ((script.nativeCalls.take limit).map (fun request =>
    (Complexity.nativeRequestCosted request
      (fun _ => Complexity.Costed.tick true 10)
      (fun _ => Complexity.Costed.tick true 20)).cost)).sum

example : certFields.all (fun field =>
    let fresh := checkedAxiomProofScript field none
    let reused := checkedAxiomProofScript field (some `Parent)
    decide (prefixAlgorithmCost fresh 0 = 0) &&
      decide (prefixAlgorithmCost fresh 1 = 11) &&
      decide (prefixAlgorithmCost reused 0 = 0) &&
      decide (prefixAlgorithmCost reused 1 = 31)) = true := by native_decide

example : let script := certAxiomCounterexampleScript (registryField "ax73")
    (List.range 4).map (prefixAlgorithmCost script) = [0, 11, 22, 22] := by native_decide

example : let script := certAxiomCounterexampleScript (registryField "ax78")
    (List.range 4).map (prefixAlgorithmCost script) = [0, 11, 22, 22] := by native_decide

private def recordAttempt (label : String) (failed : Bool) : StateM (Array String) Bool := do
  modify (·.push label)
  pure failed

private def observedAttempts (reuse p d fp fd : Bool) :
    CertificateChecking.Result × Array String :=
  (CertificateChecking.run (fun _ => pure ()) (fun _ => pure (parent? reuse))
    (fun _ => recordAttempt "preflight" p)
    (fun _ => recordAttempt "declaration" d)
    (fun _ => recordAttempt "fresh-preflight" fp)
    (fun _ => recordAttempt "fresh-declaration" fd)).run #[]

-- This table describes the permitted callbacks independently of the monadic
-- driver. A preflight failure suppresses its declaration. Reuse failure is
-- the only route to either fresh callback.
private def expectedAttempts (reuse p d fp fd : Bool) :
    CertificateChecking.Result × Array String :=
  let initial := if p then #["preflight"] else #["preflight", "declaration"]
  if !(p || d) then
    (.checked (parent? reuse), initial)
  else if !reuse then
    (.failed, initial)
  else
    let fresh := if fp then #["fresh-preflight"] else #["fresh-preflight", "fresh-declaration"]
    (if fp || fd then .failed else .checked none, initial ++ fresh)

example : ∀ reuse p d fp fd : Bool,
    observedAttempts reuse p d fp fd = expectedAttempts reuse p d fp fd := by native_decide

private def countedAttempts (reuse p d fp fd : Bool) :=
  CertificateChecking.runCosted (fun _ => Complexity.Costed.pure (parent? reuse))
    (fun _ => Complexity.Costed.tick p 10)
    (fun _ => Complexity.Costed.tick d 20)
    (fun _ => Complexity.Costed.tick fp 100)
    (fun _ => Complexity.Costed.tick fd 200)

example : countedAttempts false true false false false = ⟨.failed, 13⟩ := by decide
example : countedAttempts false false false true true = ⟨.checked none, 32⟩ := by decide
example : countedAttempts true false false true true = ⟨.checked (some `Parent), 32⟩ := by decide
example : countedAttempts true true false true false = ⟨.failed, 115⟩ := by decide
example : countedAttempts true false true true false = ⟨.failed, 135⟩ := by decide
example : countedAttempts true false true false false = ⟨.checked none, 335⟩ := by decide
example : countedAttempts true true false false true = ⟨.failed, 315⟩ := by decide

private def plannedAttempts (reuse p d fp fd : Bool) :
    CertificateChecking.Result × Array String :=
  (CertificateChecking.run (fun _ => pure ())
    (fun _ => do
      modify (·.push "plan")
      pure (parent? reuse))
    (fun parent => recordAttempt ("preflight:" ++ toString parent) p)
    (fun parent => recordAttempt ("declaration:" ++ toString parent) d)
    (fun _ => recordAttempt "fresh-preflight" fp)
    (fun _ => recordAttempt "fresh-declaration" fd)).run #[]

-- The independent outcome table supplies the proof order. Planning adds one
-- first event, and both initial callbacks must receive its selected parent.
example : ∀ reuse p d fp fd : Bool,
    plannedAttempts reuse p d fp fd =
      let expected := expectedAttempts reuse p d fp fd
      (expected.1, #["plan"] ++ expected.2.map (fun label =>
        if label == "preflight" || label == "declaration" then
          label ++ ":" ++ toString (parent? reuse) else label)) := by native_decide

-- A seven-operation planner contributes seven on every path, including
-- failed reuse followed by fresh fallback. It is never run a second time.
example : ∀ reuse p d fp fd : Bool,
    CertificateChecking.runCosted (fun _ => Complexity.Costed.tick (parent? reuse) 7)
      (fun _ => Complexity.Costed.tick p 10)
      (fun _ => Complexity.Costed.tick d 20)
      (fun _ => Complexity.Costed.tick fp 100)
      (fun _ => Complexity.Costed.tick fd 200) =
        ⟨(countedAttempts reuse p d fp fd).value,
          (countedAttempts reuse p d fp fd).cost + 7⟩ := by decide

-- Reaching the outer precheck is not enough to run the planner: a precheck
-- failure skips the entire checked-attempt driver.
example :
    ((CertificateChecking.runField (m := StateM (Array String)) (fun _ => pure ())
      (fun _ => recordAttempt "precheck" true)
      (fun _ => CertificateChecking.run (fun _ => pure ())
        (fun _ => do modify (·.push "plan"); pure (some `Parent))
        (fun _ => recordAttempt "preflight" false)
        (fun _ => recordAttempt "declaration" false)
        (fun _ => recordAttempt "fresh-preflight" false)
        (fun _ => recordAttempt "fresh-declaration" false))
      (fun _ => recordAttempt "policy" false)
      (fun _ => recordAttempt "semantic-preflight" false)
      (fun _ => recordAttempt "semantic-declaration" false)).run #[] :
        CertificateChecking.Result × Array String) =
        (.failed, #["precheck"]) := by rfl

private def observedField (p k reuse command t dc dt : Bool) :
    CertificateChecking.Result × Array String :=
  (CertificateChecking.runField (m := StateM (Array String)) (fun _ => pure ())
    (fun _ => recordAttempt "precheck" p)
    (fun _ => do
      modify (·.push "checked")
      pure (if k then .failed else .checked (parent? reuse)))
    (fun _ => recordAttempt "policy" command)
    (fun _ => recordAttempt "semantic-trial" t)
    (fun mode => if mode then recordAttempt "command" dc else recordAttempt "declaration" dt)).run #[]

private def expectedField (p k reuse command t dc dt : Bool) :
    CertificateChecking.Result × Array String :=
  if p then (.failed, #["precheck"])
  else if k then (.failed, #["precheck", "checked"])
  else
    let visited := #["precheck", "checked", "policy"]
    if command then
      (if dc then .failed else .checked (parent? reuse), visited.push "command")
    else if t then (.failed, visited.push "semantic-trial")
    else (if dt then .failed else .checked (parent? reuse),
      visited ++ #["semantic-trial", "declaration"])

-- All 128 outcome/reuse combinations preserve result and callback order.
-- The policy is absent after early failure and occurs once on every later path.
example : ∀ p k reuse command t dc dt : Bool,
    observedField p k reuse command t dc dt = expectedField p k reuse command t dc dt := by
  native_decide

private def countedField (p k command t dc dt : Bool) :=
  CertificateChecking.runFieldCosted
    (fun _ => Complexity.Costed.tick p 10)
    (fun _ => Complexity.Costed.tick (if k then .failed else .checked (some `Parent)) 20)
    (fun _ => Complexity.Costed.tick command 30)
    (fun _ => Complexity.Costed.tick t 100)
    (fun mode => if mode then Complexity.Costed.tick dc 200 else Complexity.Costed.tick dt 300)

example : countedField true false false false false false = ⟨.failed, 11⟩ := by decide
example : countedField false true false false false false = ⟨.failed, 32⟩ := by decide
example : countedField false false true true false true = ⟨.checked (some `Parent), 264⟩ := by decide
example : countedField false false true false true false = ⟨.failed, 264⟩ := by decide
example : countedField false false false true false false = ⟨.failed, 165⟩ := by decide
example : countedField false false false false false false = ⟨.checked (some `Parent), 465⟩ := by decide
example : countedField false false false false false true = ⟨.failed, 465⟩ := by decide

example : (useCommandCertificateProbeCosted (registryField "ax1")).cost = 2 := by native_decide
example : (useCommandCertificateProbeCosted (registryField "ax44")).cost = 14 := by native_decide
example : (useCommandCertificateProbeCosted (registryField "ax68")).cost = 15 := by native_decide
example : (useCommandCertificateProbeCosted (registryField "ax99")).cost = 15 := by native_decide
-- The guard skips closure search even for large supplied dimensions.
example : certificationFieldPrecheckCosted 1000000 1000000 {} "ax1" = ⟨false, 2⟩ := by native_decide
example : (certificationFieldPrecheckCosted 0 0 {} "ax68").cost =
    (hasAx68ClosureFailureCosted 0 0 {}).cost + 2 := by native_decide

private def fieldAnswer (passed reuse : Bool) : CertificateChecking.Result :=
  if passed then .checked (parent? reuse) else .failed

private def observedRegistry (answers : Array CertificateChecking.Result) :
    CertificateChecking.RegistryResult Nat × Array Nat :=
  (CertificateChecking.runFields (m := StateM (Array Nat)) (fun _ => pure ())
    #[0, 1, 2] toString (fun i => do
      modify (·.push i)
      pure (answers.getD i .failed))).run #[]

-- The independent specification uses the first failed index. It does not
-- reproduce the driver's state updates. All 64 success/reuse combinations
-- check the successful prefix, parent metadata, failed field, and call trace.
private def expectedRegistry (a b c ra rb rc : Bool) :
    CertificateChecking.RegistryResult Nat × Array Nat :=
  let stop := if !a then 0 else if !b then 1 else if !c then 2 else 3
  let parents := #[parent? ra, parent? rb, parent? rc]
  let completed := (#[0, 1, 2] : Array Nat).extract 0 stop
  ({ completed := completed.map toString
     actualReuse := completed.map (fun i => (toString i, parents[i]!))
     failedField? := if stop < 3 then some stop else none },
   (#[0, 1, 2] : Array Nat).extract 0 (stop + 1))

example : ∀ a b c ra rb rc : Bool,
    observedRegistry #[fieldAnswer a ra, fieldAnswer b rb, fieldAnswer c rc] =
      expectedRegistry a b c ra rb rc := by native_decide

private def countedRegistry (a b c : Bool) :=
  let answers := #[fieldAnswer a true, fieldAnswer b false, fieldAnswer c true]
  let costs := #[10, 20, 100]
  CertificateChecking.runFieldsCosted #[0, 1, 2] toString
    (fun i => Complexity.Costed.tick (answers.getD i .failed) costs[i]!)

-- Two initializations, seven driver operations on success, five on failure,
-- and three on each subsequent skipped visit. Callback costs are 10/20/100.
example : (countedRegistry true true true).cost = 153 := by native_decide
example : (countedRegistry false true true).cost = 23 := by native_decide
example : (countedRegistry true false true).cost = 47 := by native_decide
example : (countedRegistry true true false).cost = 151 := by native_decide
example : (CertificateChecking.runFieldsCosted (#[] : Array Nat) toString
    (fun _ => Complexity.Costed.tick (.checked none) 100)).cost = 2 := by decide

-- The outer loop composes the existing checked-attempt driver, not only
-- synthetic ticks. All fresh attempts here succeed and each costs 32.
example : (CertificateChecking.runFieldsCosted certFields CertField.field
    (fun _ => countedAttempts false false false false false)).cost = 4409 := by native_decide

-- Both production drivers, the real policy, and the real precheck compose.
-- The 105 trial/declaration fields each cost 63. The eight command-only
-- fields cost 439 together, plus the one closure precheck. Initialization adds two.
private def composedRegistry :=
  CertificateChecking.runFieldsCosted certFields CertField.field fun field =>
    CertificateChecking.runFieldCosted
      (fun _ => certificationFieldPrecheckCosted 0 0 {} field.field)
      (fun _ => countedAttempts false false false false false)
      (fun _ => useCommandCertificateProbeCosted field)
      (fun _ => Complexity.Costed.tick false)
      (fun _ => Complexity.Costed.tick false)

example : composedRegistry.cost = 7056 + (hasAx68ClosureFailureCosted 0 0 {}).cost := by
  native_decide
example : composedRegistry.value.completed = certFields.map CertField.field := by native_decide
example : composedRegistry.value.failedField?.isNone = true := by native_decide

end LeanUfo.Test.Certificates.Generation
