import LeanUfo.UFO.DSL.Certificate.Generation

/-!
# Native proof preparation

The frontend uses this executor to prepare each generated proof attempt.
Within one invocation, it owns the order and number of registered native decisions.
Each successful decision supplies a proof for the generated certificate text.
Lean's existing `nativeEqTrue` API performs the native computation and produces
that proof, retaining the trust boundary of `native_decide`.

Only the closed Boolean expression named by the request is evaluated here.
Parsing, elaboration, native compilation, and proof rendering are outside the
unit-cost model. The executor's branch costs and the requested checker work
are separate from those activities.
-/

namespace LeanUfo.UFO.DSL.CertificateChecking

open Lean Elab Meta

/-- Produce a proof of the same Boolean expression used by the counted request
composition. Do not admit elaboration errors: a synthetic sorry must never
stand in for a Boolean operand passed to native evaluation. -/
private def prepareNativeRequest (request : NativeCall) :
    TermElabM (Except Exception String) := do
  try
    let source := request.booleanSource
    let stx ← match Parser.runParserCategory (← getEnv) `term source with
      | .ok stx => pure stx
      | .error error => throwError "failed to parse native UFO request:\n{error}"
    let expression ← Term.withoutErrToSorry do
      let expression ← Term.elabTermEnsuringType stx (some (mkConst ``Bool))
      Term.synthesizeSyntheticMVarsNoPostponing
      instantiateMVars expression
    if expression.hasSorry then
      throwError "native UFO request contains an admitted term"
    match ← nativeEqTrue `native_decide expression with
    | .notTrue =>
        throwError "Tactic `native_decide` evaluated that the proposition\n  {source} = true\nis false"
    | .success proof =>
        -- Fully qualified proof names remain valid when inserted into a
        -- generated theorem in the current model namespace.
        let rendered ← withOptions (fun options => options.setBool `pp.fullNames true) <|
          Meta.ppExpr proof
        pure (.ok rendered.pretty)
  catch error => pure (.error error)

/-- Run the same loop used by `ProofScript.prepareCosted`. The caller owns the
surrounding message scope and handles any preparation error like a failed
proof attempt. Returned text contains proofs for the registered requests,
not tactics that can execute those requests again. -/
def prepareProofScript (script : ProofScript) : TermElabM (Except Exception String) :=
  script.prepare (fun n => pure (Complexity.Costed.tick () n).value) prepareNativeRequest

/-- Native preparation runs under the limits already attached to the generated
proof. Without this scope, moving decisions out of the proof text would expose
them to different heartbeat and recursion limits. The caller must run this
action inside its proof-attempt error capture. Source wrapping and exception
translation are part of the excluded elaboration bridge. -/
def prepareProofSource (source : ProofSource) : TermElabM String := do
  let configure := fun options : Options =>
    let options := match source.maxHeartbeats? with
      | none => options
      | some limit => options.set `maxHeartbeats limit
    match source.maxRecDepth? with
    | none => options
    | some limit => options.set `maxRecDepth limit
  withOptions configure do
    match ← prepareProofScript source.script with
    | .ok body => pure (source.wrap body)
    | .error error => throw error

end LeanUfo.UFO.DSL.CertificateChecking
