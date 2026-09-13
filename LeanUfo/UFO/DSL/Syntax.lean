import Lean
import LeanUfo.UFO.DSL.Certificate.Checking
import LeanUfo.UFO.DSL.Certificate.Execution
import LeanUfo.UFO.DSL.Certificate.Generation
import LeanUfo.UFO.DSL.Certificate.Reuse
import LeanUfo.UFO.DSL.Certificate.Tactic
import LeanUfo.UFO.DSL.Compiler
import LeanUfo.UFO.DSL.Compiler.VerifiedModel
import LeanUfo.UFO.DSL.Complexity.Diagnostics
import LeanUfo.UFO.DSL.Diagnostic.Analysis
import LeanUfo.UFO.DSL.Diagnostic.Widget
import LeanUfo.UFO.DSL.Frontend.ModelText
import LeanUfo.UFO.DSL.Frontend.SurfaceSyntax

/-!
# Lean command syntax for finite UFO models

This module is the finite-model DSL frontend. Its scope is limited to:

* `Frontend/SurfaceSyntax.lean` owns the parser grammar for the user-facing command;
* `Diagnostic/Widget.lean` owns the editor panel used to display model feedback;
* the **surface DSL** lets users write named worlds, named things, and named
  facts using UFO-friendly notation;
* the **command elaborator** parses those facts into a named AST and delegates
  name resolution, scope expansion, taxonomy expansion, table compilation, and
  finite-model construction to the pure compiler in `Compiler.lean`;
* the **semantic target** remains the trusted `UFOSignature4` kernel;
* the **certificate** is an ordinary theorem
  `Name.certified : UFOAxioms4 Name.sig`.

The command does not add new semantics.  It emits ordinary Lean declarations
for the resolved/expanded AST, the compiled finite model, and the generated
certificate, then lets Lean check them.  If the generated finite model violates
one of the encoded axioms, the `certify` step fails during
elaboration.

This file is an integration layer, not a second compiler. Parsing produces a
named source value; ordinary functions in `Compiler.lean` perform semantic
transformations; certificate modules construct proof declarations; diagnostic
modules explain a failure after the checker has decided it. Keeping those
responsibilities outside the elaborator makes the executable stages testable
and lets their correctness and cost be proved independently.

The core fact syntax is:

```lean
P(x)        -- unary UFO classification predicate
x :: T      -- UFO instantiation
T₁ ⊑ T₂     -- specialization
R(x, y)     -- binary relation fact
R(x, y, z)  -- selected ternary primitive or derived relation fact
```

Instantiation and specialization keep their UFO notation because they carry
central modeling intent.  Other predicate and relation facts use uniform
call-style syntax, including tuple-projection facts such as
`TupleProjection(tuple, 0, component)`. Missing facts default to `false`, except
that `Part` and `Overlap` include identity by default so that the common
tiny-model case satisfies extensional mereology without boilerplate.

The pure compiler also closes unary taxonomy facts conservatively.  For example,
`QuantityKind(x)` inserts the facts required by the encoded taxonomy, such as
`Kind(x)`, `Sortal(x)`, `Rigid(x)`, `QuantityType(x)`,
`SubstantialType(x)`, and `EndurantType(x)`.  This is DSL sugar over finite
data, not a change to the semantic kernel: certification still checks the
expanded tables against the original Prop-level axioms.

Definition-like relations may also be written explicitly.  They are not taken
as primitive semantic tables; `derive_relations` still computes their meaning
from the compiled model.  Explicit derived facts are instead
turned into a generated theorem `Name.assertedDerivedFacts`, so a misspecified
derived fact fails elaboration rather than being silently ignored.
Higher-arity derived facts use function-style syntax, for example
`IsPartitionedInto(Person, Employee, NonEmployee)`, because plain whitespace is
not a reliable arity separator in Lean command syntax.

A fact block may target the reserved pseudo-world `everywhere`.  The elaborator
records this as a scoped fact, and the pure compiler expands it into one copy
for every declared world. This is only syntactic sugar; the compiled finite
tables still contain ordinary world-indexed facts.
-/

open Lean Elab Command Parser

namespace LeanUfo.UFO.DSL

structure CachedModelSource where
  source : ModelSource
  tables : FactTables
  declaredName : Name
  deriving Inhabited

initialize modelSourceCache : IO.Ref (Std.HashMap Name CachedModelSource) ← IO.mkRef {}

private def checkNoReservedWorldNames (xs : Array Name) : CommandElabM Unit := do
  for x in xs do
    if x == `everywhere then
      throwError "`everywhere` is reserved for facts that hold at every declared world"

/-!
## Parser bridge

The concrete grammar in `Frontend/SurfaceSyntax.lean` accepts identifiers as
names. This layer then maps relation names to
registered primitive or derived fields.  Unknown worlds and things are checked
later by the pure resolver in `Compiler.lean`, so duplicate and scope errors are
reported from the same place regardless of which syntactic fact form was used.
-/

private def parseFact
    (_worldNames _thingNames : Array Name) (scope : NamedFactScope)
    (facts : Array NamedScopedFact) (fact : TSyntax `ufoFact) :
    CommandElabM (Array NamedScopedFact) := do
  match fact with
  | `(ufoFact| $p:ident($x:ident)) =>
      let xName := x.getId.toString
      match unaryField? p.getId with
      | some field => pure <| facts.push (.unary field xName scope)
      | none =>
          match derivedUnaryField? p.getId with
          | some field =>
              pure <| facts.push (.derived (.unary field xName) scope)
          | none => throwErrorAt p "unsupported unary UFO predicate `{p.getId}`"
  | `(ufoFact| $x:ident :: $t:ident) =>
      pure <| facts.push (.binary .inst x.getId.toString t.getId.toString scope)
  | `(ufoFact| $x:ident ⊑ $t:ident) =>
      pure <| facts.push (.binary .sub x.getId.toString t.getId.toString scope)
  | `(ufoFact| $r:ident($x:ident, $y:ident)) =>
      let xName := x.getId.toString
      let yName := y.getId.toString
      match binaryField? r.getId with
      | some field => pure <| facts.push (.binary field xName yName scope)
      | none =>
          match derivedBinaryField? r.getId with
          | some field =>
              pure <| facts.push (.derived (.binary field xName yName) scope)
          | none => throwErrorAt r "unsupported binary UFO relation `{r.getId}`"
  | `(ufoFact| $r:ident($x:ident, $y:ident, $z:ident)) =>
      let xName := x.getId.toString
      let yName := y.getId.toString
      let zName := z.getId.toString
      match ternaryField? r.getId with
      | some field => pure <| facts.push (.ternary field xName yName zName scope)
      | none =>
          match derivedTernaryField? r.getId with
          | some field =>
              pure <| facts.push (.derived (.ternary field xName yName zName) scope)
          | none => throwErrorAt r "unsupported ternary UFO relation `{r.getId}`"
  | `(ufoFact| $r:ident($x:ident, $y:ident, $z:ident, $q:ident)) =>
      let xName := x.getId.toString
      let yName := y.getId.toString
      let zName := z.getId.toString
      let qName := q.getId.toString
      match derivedQuaternaryField? r.getId with
      | some field =>
          pure <| facts.push (.derived (.quaternary field xName yName zName qName) scope)
      | none => throwErrorAt r "unsupported quaternary UFO relation `{r.getId}`"
  | `(ufoFact| TupleProjection($x:ident, $i:num, $y:ident)) =>
      pure <| facts.push (.tupleProjection x.getId.toString i.getNat y.getId.toString scope)
  | _ =>
      throwErrorAt fact "unsupported UFO fact syntax"

private def parseFactBlock
    (worldNames thingNames : Array Name)
    (facts : Array NamedScopedFact) (factBlock : TSyntax `ufoFactBlock) :
    CommandElabM (Array NamedScopedFact) := do
  match factBlock with
  | `(ufoFactBlock| given $factWorld:ident:
        $fs:ufoFact*) =>
      parseFactBlockContents worldNames thingNames facts factWorld fs
  | _ =>
      throwErrorAt factBlock "unsupported UFO `given` block"
where
  parseFactBlockContents
      (worldNames thingNames : Array Name) (facts : Array NamedScopedFact)
      (factWorld : TSyntax `ident) (fs : Array (TSyntax `ufoFact)) :
      CommandElabM (Array NamedScopedFact) := do
      let mut facts := facts
      let scope :=
        if factWorld.getId == `everywhere then
          NamedFactScope.everywhere
        else
          NamedFactScope.at factWorld.getId.toString
      for fact in fs do
        facts ← parseFact worldNames thingNames scope facts fact
      pure facts

private def parseProductFamily
    (family : TSyntax `ufoProductFamily) : CommandElabM NamedProductFamily := do
  let mut header : Array String := #[]
  let mut dims : Array String := #[]
  let mut tys : Array String := #[]
  let mut mode : Nat := 0
  let mut stack : Array Syntax := #[family.raw]
  while !stack.isEmpty do
    let stx := stack.back!
    stack := stack.pop
    match stx with
    | .atom _ val =>
        if val == "dimensions" then
          mode := 1
        else if val == "types" then
          mode := 2
    | .ident _ _ name _ =>
        match mode with
        | 0 => header := header.push name.toString
        | 1 => dims := dims.push name.toString
        | _ => tys := tys.push name.toString
    | _ =>
        let args := stx.getArgs
        for i in [:args.size] do
          stack := stack.push args[args.size - 1 - i]!
  match header[0]?, header[1]? with
  | some domain, some qualityType =>
      pure { domain, qualityType, dimensionThings := dims, typeThings := tys }
  | _, _ =>
      throwErrorAt family "unsupported UFO `product_family` block"

/--
Status classifier used by the diagnostics widget.

`completed` contains exactly the certificate fields whose generated certificate
probe succeeded and whose theorem was emitted. `failed?` records the first field
whose probe failed, if certification stopped before all fields completed.
-/
def diagnosticCertStatus (completed : Array String) (failed? : Option String)
    (field : String) : String :=
  if completed.contains field then
    "success"
  else if failed? == some field then
    "failed"
  else
    "unchecked"

private def certificationJson (completed : Array String) (failed? : Option String) : Json :=
  Json.arr <| certFields.map fun field =>
    let status := diagnosticCertStatus completed failed? field.field
    Json.mkObj [
      ("field", field.field),
      ("prop", field.prop),
      ("formula", certFormula field.field),
      ("status", status)
    ]

private def certificateReuseJson (actualReuse : Array (String × Option Name)) : Json :=
  Json.arr <| actualReuse.map fun row =>
    Json.mkObj [
      ("field", row.1),
      ("status", if row.2.isSome then "reused" else "fresh"),
      ("reusedFrom", match row.2 with
        | none => Json.null
        | some parent => Json.str s!"{parent}.{checkedTheoremName row.1}")
    ]

private def diagnosticsProps
    (model : Name) (worldNames thingNames : Array Name)
    (namedFacts : Array NamedScopedFact) (scopedFacts : Array ScopedCompiledFact)
    (expandedFacts : Array CompiledFact)
    (tables : FactTables) (stage : String)
    (completed : Array String := #[]) (failed? : Option String := none)
    (failure? : Option String := none) (failureAnalysis : Array String := #[])
    (actualReuse : Array (String × Option Name) := #[]) : Json :=
  let derivedPairs := derivedPropSummaryPairs worldNames namedFacts scopedFacts
  Json.mkObj [
    ("model", model.toString),
    ("stage", stage),
    ("failure", failure?.getD ""),
    ("failureAnalysis", stringsJson failureAnalysis),
    ("worlds", indexedNamesJson worldNames),
    ("things", indexedNamesJson thingNames),
    ("facts", stringsJson <| namedFacts.map namedFactSummary),
    ("expandedFacts", stringsJson <| expandedFacts.map (compiledFactSummary worldNames thingNames derivedPairs)),
    ("derivedProps", stringsJson tables.derivedProps),
    ("certification", certificationJson completed failed?),
    ("certificateReuse", certificateReuseJson actualReuse)
  ]

private def saveDiagnosticsWidget
    (cmdStx : Syntax) (model : Name) (worldNames thingNames : Array Name)
    (namedFacts : Array NamedScopedFact) (scopedFacts : Array ScopedCompiledFact)
    (expandedFacts : Array CompiledFact)
    (tables : FactTables) (stage : String)
    (completed : Array String := #[]) (failed? : Option String := none)
    (failure? : Option String := none) (failureAnalysis : Array String := #[])
    (actualReuse : Array (String × Option Name) := #[]) :
    CommandElabM Unit := do
  liftCoreM <| Widget.savePanelWidgetInfo ufoDiagnosticsWidget.javascriptHash
    (pure <| diagnosticsProps model worldNames thingNames namedFacts scopedFacts expandedFacts tables
      stage completed failed? failure? failureAnalysis actualReuse)
    cmdStx

private def saveFailedDiagnosticsWidget
    (cmdStx : Syntax) (model : Name) (worldNames thingNames : Array Name)
    (namedFacts : Array NamedScopedFact) (scopedFacts : Array ScopedCompiledFact)
    (expandedFacts : Array CompiledFact)
    (tables : FactTables) (stage : String)
    (completed : Array String) (failed? : Option String)
    (message : String) (failureAnalysis : Array String := #[])
    (actualReuse : Array (String × Option Name) := #[]) : CommandElabM Unit := do
  -- This boundary also accepts messages from outside the witness producer.
  -- Use its shared counted prefix copy to keep widget output within 128 rows.
  let failureAnalysis :=
    (Complexity.boundedEvidence 128 failureAnalysis).items
  saveDiagnosticsWidget cmdStx model worldNames thingNames namedFacts scopedFacts expandedFacts tables
    stage completed failed? (some message) failureAnalysis actualReuse
  let detail :=
    if failureAnalysis.isEmpty then
      message
    else
      message ++ "\n" ++ String.intercalate "\n" failureAnalysis.toList
  logErrorAt cmdStx detail

private def elabCommandString (source : String) : CommandElabM Unit := do
  match Parser.runParserCategory (← getEnv) `command source with
  | .ok stx => elabCommand stx
  | .error err => throwError "failed to parse generated UFO command:\n{err}\n\nGenerated source:\n{source}"

private def messageErrorCount (messages : MessageLog) : Nat :=
  messages.reportedPlusUnreported.foldl
    (fun count msg => if msg.severity == MessageSeverity.error then count + 1 else count)
    0

private def messageErrorTexts (messages : MessageLog) : CommandElabM (Array String) := do
  let mut out := #[]
  for msg in messages.reportedPlusUnreported do
    if msg.severity == MessageSeverity.error then
      out := out.push (← msg.toString)
  pure out

private def exceptionText (ex : Exception) : CommandElabM String := do
  match ex with
  | .error _ msg => msg.toString
  | .internal id _ => pure id.toString

private def coreMessageErrorCount : CommandElabM Nat := do
  pure <| messageErrorCount (← liftCoreM Core.getMessageLog)

private def certProfileEnabled : CommandElabM Bool := do
  match (← IO.getEnv "LEANUFO_CERT_PROFILE") with
  | some "1" | some "true" | some "TRUE" | some "yes" | some "YES" => pure true
  | _ => pure false

/--
Measure one generated certification step when `LEANUFO_CERT_PROFILE=1`.

The labels are emitted as Lean info messages so profiling works both in `lake`
and in editor elaboration.  Heartbeats are reported in thousands to match the
granularity usually used when tuning generated Lean proofs.
-/
private def profileStep (enabled : Bool) (label : String) (step : CommandElabM α) :
    CommandElabM α := do
  if enabled then
    let startMs ← IO.monoMsNow
    let startHeartbeats ← IO.getNumHeartbeats
    try
      let result ← step
      let elapsedMs := (← IO.monoMsNow) - startMs
      let elapsedHeartbeats := (← IO.getNumHeartbeats) - startHeartbeats
      logInfo m!"[lean-ufo-cert-profile] {label}: done {elapsedMs}ms {elapsedHeartbeats / 1000}hb"
      pure result
    catch e =>
      let elapsedMs := (← IO.monoMsNow) - startMs
      let elapsedHeartbeats := (← IO.getNumHeartbeats) - startHeartbeats
      logInfo m!"[lean-ufo-cert-profile] {label}: threw {elapsedMs}ms {elapsedHeartbeats / 1000}hb"
      throw e
  else
    step

private structure ElabCheckResult where
  failed : Bool
  errors : Array String

/-- Build the source inside message capture: native preparation can fail before
the remaining proof text is parsed. Its errors must follow the same fallback
and diagnostic path as errors from elaborating that text. -/
private def elabCommandStringWithReport (source : CommandElabM String) : CommandElabM ElabCheckResult := do
  let savedCommandMessages ← modifyGet fun st =>
    (st.messages, { st with messages := {} })
  let savedMessages ← liftCoreM <| modifyGetThe Core.State fun st =>
    (st.messages, { st with messages := {} })
  let mut threw := false
  let mut thrownErrors : Array String := #[]
  try
    elabCommandString (← source)
  catch e =>
    threw := true
    thrownErrors := thrownErrors.push (← exceptionText e)
  let newMessages ← liftCoreM Core.getMessageLog
  let newCommandMessages := (← get).messages
  modify fun st =>
    { st with messages := savedCommandMessages }
  liftCoreM <| modifyThe Core.State fun st =>
    { st with messages := savedMessages }
  let errors := thrownErrors ++ (← messageErrorTexts newMessages) ++ (← messageErrorTexts newCommandMessages)
  pure { failed := threw || messageErrorCount newMessages > 0 || messageErrorCount newCommandMessages > 0
         errors := errors }

private def elabCommandStringWithErrorCheck (source : CommandElabM String) : CommandElabM Bool := do
  pure (← elabCommandStringWithReport source).failed

/--
Check a generated certificate proof as a term while suppressing any messages it
produces.

This is a fast preflight check, not the authoritative certificate path, because
term elaboration can be weaker than command
elaboration for large generated finite proofs.  See `useCommandCertificateProbe`
for fields that skip this preflight and test the generated theorem command
directly.
-/
private def elabTermStringWithReport (makeSource : CommandElabM String) : CommandElabM ElabCheckResult := do
  let savedCommandMessages ← modifyGet fun st =>
    (st.messages, { st with messages := {} })
  let savedMessages ← liftCoreM <| modifyGetThe Core.State fun st =>
    (st.messages, { st with messages := {} })
  let mut threw := false
  let mut thrownErrors : Array String := #[]
  try
    let source ← makeSource
    match Parser.runParserCategory (← getEnv) `term source with
    | .ok stx =>
        liftTermElabM <| Lean.Elab.Term.withoutErrToSorry do
          let _ ← Lean.Elab.Term.elabTerm stx none
          Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    | .error err =>
        throwError "failed to parse generated UFO proof check:\n{err}\n\nGenerated source:\n{source}"
  catch e =>
    threw := true
    thrownErrors := thrownErrors.push (← exceptionText e)
  let newMessages ← liftCoreM Core.getMessageLog
  let newCommandMessages := (← get).messages
  modify fun st =>
    { st with messages := savedCommandMessages }
  liftCoreM <| modifyThe Core.State fun st =>
    { st with messages := savedMessages }
  let errors := thrownErrors ++ (← messageErrorTexts newMessages) ++ (← messageErrorTexts newCommandMessages)
  pure { failed := threw || messageErrorCount newMessages > 0 || messageErrorCount newCommandMessages > 0
         errors := errors }

private def elabTermStringWithErrorCheck (source : CommandElabM String) : CommandElabM Bool := do
  pure (← elabTermStringWithReport source).failed

private def elabTermStringStrictWithReport (makeSource : CommandElabM String) : CommandElabM ElabCheckResult := do
  let savedCommandMessages ← modifyGet fun st =>
    (st.messages, { st with messages := {} })
  let savedMessages ← liftCoreM <| modifyGetThe Core.State fun st =>
    (st.messages, { st with messages := {} })
  let mut threw := false
  let mut thrownErrors : Array String := #[]
  try
    let source ← makeSource
    match Parser.runParserCategory (← getEnv) `term source with
    | .ok stx =>
        liftTermElabM do
          let _ ← Lean.Elab.Term.elabTerm stx none
          Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    | .error err =>
        throwError "failed to parse generated UFO proof check:\n{err}\n\nGenerated source:\n{source}"
  catch e =>
    threw := true
    thrownErrors := thrownErrors.push (← exceptionText e)
  let newMessages ← liftCoreM Core.getMessageLog
  let newCommandMessages := (← get).messages
  modify fun st =>
    { st with messages := savedCommandMessages }
  liftCoreM <| modifyThe Core.State fun st =>
    { st with messages := savedMessages }
  let errors := thrownErrors ++ (← messageErrorTexts newMessages) ++ (← messageErrorTexts newCommandMessages)
  pure { failed := threw || messageErrorCount newMessages > 0 || messageErrorCount newCommandMessages > 0
         errors := errors }

private def elabTermStringStrictWithErrorCheck (source : CommandElabM String) : CommandElabM Bool := do
  pure (← elabTermStringStrictWithReport source).failed

private def certificationFailureAnalysis
    (profileEnabled : Bool) (model : Name)
    (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (tables : FactTables) (field : CertField) : CommandElabM (Array String) := do
  let counterexampleProbe ← profileStep profileEnabled s!"{model}.{field.field}.counterexample-probe" <|
    elabTermStringWithReport (liftTermElabM <|
      CertificateChecking.prepareProofSource (certAxiomCounterexampleCheck field))
  pure (certificationFailureReportCosted worldNames thingNames namedFacts tables
    field.field counterexampleProbe.failed counterexampleProbe.errors).value

private def throwResolveError : ResolveError → CommandElabM α
  | .duplicateWorld name => throwError "duplicate world name `{name}` in UFO model"
  | .duplicateThing name => throwError "duplicate thing name `{name}` in UFO model"
  | .unknownWorld name => throwError "unknown world name `{name}` in UFO model"
  | .unknownThing name => throwError "unknown thing name `{name}` in UFO model"
  | .extensionAddsWorlds =>
      throwError
        "extended UFO models cannot declare new worlds yet; add only things, facts, and product-family witnesses, or define a fresh model"
  | .extensionDisablesDerivations =>
      throwError "extended UFO models must use the same `derive_relations` setting as their parent"
  | .productFamilyArityMismatch domain qualityType dimensionCount typeCount =>
      throwError
        "product_family `{domain}` for `{qualityType}` has {dimensionCount} dimensions but {typeCount} types"
  | .conflictingTupleProjection tuple index world firstResult secondResult =>
      throwError
        "conflicting tuple projection at tuple #{tuple}, slot #{index}, world #{world}: results #{firstResult} and #{secondResult}"

/--
Emit the ordinary Lean declarations generated by a `ufo_model` command.

The generated namespace contains the expanded AST, the compiled finite tables,
the finite model, the compiled UFO signature, optional checks for user-written
derived-relation facts, one theorem per axiom field, the final bundled
`UFOAxioms4` certificate, and a `FiniteModel4.Certified` packaging theorem for
the generated finite data. These declarations are elaborated normally, so
failed certification is detected by Lean itself. The diagnostics widget is saved
once, after derived assertions and certificate checks have either completed or
stopped at the first failed generated axiom field.
-/
private def emitModel
    (cmdStx : Syntax) (model : Name) (worldNames thingNames : Array Name)
    (source : ModelSource) (namedFacts : Array NamedScopedFact)
    (scopedFacts : Array ScopedCompiledFact)
    (facts : Array CompiledFact) (productFamilies : Array ProductFamilySpec)
    (tables : FactTables) (reuseFor? : String → Option Name := fun _ => none) :
    CommandElabM Name := do
  if worldNames.isEmpty then
    throwError "a UFO model must declare at least one world"
  if thingNames.isEmpty then
    throwError "a UFO model must declare at least one thing"

  let declaredModel := (← getCurrNamespace) ++ model
  let modelIdent := mkIdent model
  let profileEnabled ← certProfileEnabled
  let initialErrors ← coreMessageErrorCount
  elabCommand (← `(command| namespace $modelIdent))
  elabCommandString (modelSourceDecl source)
  elabCommandString (modelASTSource worldNames.size thingNames.size facts productFamilies)
  elabCommandString "def tables : FactTables := compileExplicitModelAST ast"
  -- This finite coordinate proof uses the same local reduction limits as the
  -- generated checker proofs. It does not evaluate table correspondence.
  elabCommandString "set_option maxRecDepth 20000 in set_option maxHeartbeats 1000000 in theorem astWellBounded : Complexity.Production.explicitModelWellBounded ast := by decide"
  elabCommandString "def data : FiniteModel4 := tables.toFiniteModel4Cached ast.worldCount ast.thingCount (by decide) (by decide) (compiledLookups_agree ast astWellBounded) (compileExplicitModelAST_inherenceCacheValid ast) (compileExplicitModelAST_tableDimensions ast).1 (compileExplicitModelAST_tableDimensions ast).2"
  elabCommandString "abbrev sig : UFOSignature4 := FiniteModel4.toUFOSignature4 data"
  -- Construct a deferred action: the shared assertion driver below invokes
  -- it only after both the pure precheck and the derived-fact proof succeed.
  let runCertificate : CommandElabM (CertificateChecking.RegistryReport CertField) := do
    let progress ← CertificateChecking.runFields
      (fun n => pure (Complexity.Costed.tick () n).value) certFields CertField.field fun field =>
        CertificateChecking.runField
          (fun n => pure (Complexity.Costed.tick () n).value)
          (fun _ => pure (certificationFieldPrecheckCosted
            worldNames.size thingNames.size tables field.field).value)
          (fun _ =>
            CertificateChecking.run
              (fun n => pure (Complexity.Costed.tick () n).value)
              (fun _ => pure (reuseFor? field.field))
              (fun fieldReuseFrom? =>
                profileStep profileEnabled s!"{model}.{field.field}.checked-preflight" <|
                  elabTermStringStrictWithErrorCheck (liftTermElabM <|
                    CertificateChecking.prepareProofSource (checkedAxiomProofCheck field fieldReuseFrom?)))
              (fun fieldReuseFrom? =>
                profileStep profileEnabled s!"{model}.{field.field}.checked" <|
                  elabCommandStringWithErrorCheck (liftTermElabM <|
                    CertificateChecking.prepareProofSource (checkedAxiomTheorem field fieldReuseFrom?)))
              (fun _ =>
                profileStep profileEnabled s!"{model}.{field.field}.checked-fresh-fallback-preflight" <|
                  elabTermStringStrictWithErrorCheck (liftTermElabM <|
                    CertificateChecking.prepareProofSource (checkedAxiomProofCheck field none)))
              (fun _ =>
                profileStep profileEnabled s!"{model}.{field.field}.checked-fresh-fallback" <|
                  elabCommandStringWithErrorCheck (liftTermElabM <|
                    CertificateChecking.prepareProofSource (checkedAxiomTheorem field none))))
          (fun _ => pure (useCommandCertificateProbeCosted field).value)
          (fun _ =>
            profileStep profileEnabled s!"{model}.{field.field}.term-preflight" <|
              elabTermStringWithErrorCheck
                (liftTermElabM <| CertificateChecking.prepareProofSource
                  (certAxiomProofCheck worldNames.size thingNames.size tables field)))
          (fun command =>
            let label := if command then "command-probe" else "declare"
            profileStep profileEnabled s!"{model}.{field.field}.{label}" <|
              elabCommandStringWithErrorCheck
                (liftTermElabM <| CertificateChecking.prepareProofSource
                  (certAxiomTheorem worldNames.size thingNames.size tables field)))
    let reported ← CertificateChecking.reportAfterRegistry
      (fun n => pure (Complexity.Costed.tick () n).value) progress
      (certificationFailureAnalysis profileEnabled model worldNames thingNames namedFacts tables)
    pure reported
  let result ← CertificateChecking.runAfterAssertions
    (fun n => pure (Complexity.Costed.tick () n).value)
    (fun _ => pure (derivedAssertionFailure? worldNames thingNames namedFacts scopedFacts tables))
    (fun _ =>
      -- Derived assertions range over different semantic predicates. The
      -- shared fallback tactic therefore uses a conservative simp set whose
      -- relevant subset depends on the assertion. Suppress only that
      -- expected per-model lint; checker-backed certificates keep it active.
      profileStep profileEnabled s!"{model}.assertedDerivedFacts" <|
        elabCommandStringWithErrorCheck
          (pure s!"set_option maxHeartbeats 1000000 in set_option maxRecDepth 20000 in set_option linter.unusedSimpArgs false in theorem assertedDerivedFacts : {derivedFactsType tables.derivedProps} := {derivedFactsBody tables.derivedProps}"))
    (fun saved => pure (derivedAssertionFailureReportCosted saved).value)
    (fun _ => runCertificate)
  match result with
  | .failed failureAnalysis =>
    saveFailedDiagnosticsWidget cmdStx model worldNames thingNames namedFacts scopedFacts facts tables
      "derived-facts-failed" #[] none "A user-written derived relation assertion failed."
      failureAnalysis
  | .checked reported =>
    match reported with
    | .failed progress failedField failureAnalysis =>
        saveFailedDiagnosticsWidget cmdStx model worldNames thingNames namedFacts scopedFacts facts tables
          "certification-failed" progress.completed (some failedField.field)
          s!"Generated certificate theorem `{certTheoremName failedField.field}` failed."
          failureAnalysis progress.actualReuse
    | .checked progress =>
        let completed := progress.completed
        let actualReuse := progress.actualReuse
        let certifiedFailed ← profileStep profileEnabled s!"{model}.certified" <|
          elabCommandStringWithErrorCheck
            (pure s!"set_option maxHeartbeats 1000000 in set_option maxRecDepth 20000 in theorem certified : UFOAxioms4 sig := {certificateBody}")
        if certifiedFailed then
          saveFailedDiagnosticsWidget cmdStx model worldNames thingNames namedFacts scopedFacts facts tables
            "packaging-failed" completed none "The individual axiom checks completed, but final certificate packaging failed."
            #[] actualReuse
        else
          let certifiedModelFailed ← profileStep profileEnabled s!"{model}.certifiedModel" <|
            elabCommandStringWithErrorCheck
              (pure "theorem certifiedModel : FiniteModel4.Certified data := certified")
          if certifiedModelFailed then
            saveFailedDiagnosticsWidget cmdStx model worldNames thingNames namedFacts scopedFacts facts tables
              "packaging-failed" completed none "The individual axiom checks completed, but final certified model packaging failed."
              #[] actualReuse
          else if (← coreMessageErrorCount) > initialErrors then
            saveFailedDiagnosticsWidget cmdStx model worldNames thingNames namedFacts scopedFacts facts tables
              "certification-failed" completed none "Generated certification logged Lean errors; the model is not certified."
              #[] actualReuse
          else do
            let actualReuseFor? (field : String) : Option Name :=
              actualReuse.findSome? fun row =>
                if row.1 == field then row.2 else none
            profileStep profileEnabled s!"{model}.manifest" <|
              elabCommandString (certificateManifestSource declaredModel source tables actualReuseFor?)
            profileStep profileEnabled s!"{model}.widget" <|
              saveDiagnosticsWidget cmdStx model worldNames thingNames namedFacts scopedFacts facts tables
                "certified" completed none none #[] actualReuse
  elabCommand (← `(command| end $modelIdent))
  pure declaredModel

private def parseBlocksAndFamilies
    (worldNames thingNames : Array Name)
    (blocks : Array (TSyntax `ufoFactBlock))
    (families : Array (TSyntax `ufoProductFamily)) :
    CommandElabM (Array NamedScopedFact × Array NamedProductFamily) := do
  let mut namedFacts : Array NamedScopedFact := #[]
  for factBlock in blocks do
    namedFacts ← parseFactBlock worldNames thingNames namedFacts factBlock
  let mut namedProductFamilies : Array NamedProductFamily := #[]
  for family in families do
    namedProductFamilies := namedProductFamilies.push (← parseProductFamily family)
  pure (namedFacts, namedProductFamilies)

private def isCertifyFresh (cert : TSyntax `ufoCertDirective) : Bool :=
  cert.raw.getKind == ``ufoCertifyFresh

private unsafe def evalParentConst? (α : Type) (typeName constName : Name) :
    CommandElabM (Option α) := do
  let env ← getEnv
  let opts ← getOptions
  match (unsafe env.evalConstCheck α opts typeName constName) with
  | .ok value => pure (some value)
  | .error _ => pure none

private unsafe def cachedModelSourceFromEnv? (parent : Name) :
    CommandElabM (Option CachedModelSource) := do
  let sourceName := Name.str parent "source"
  let tablesName := Name.str parent "tables"
  match (← evalParentConst? ModelSource ``ModelSource sourceName),
      (← evalParentConst? FactTables ``FactTables tablesName) with
  | some source, some tables =>
      pure (some { source, tables, declaredName := parent })
  | _, _ =>
      pure none

private unsafe def resolveParentModelSource (parent : Name) :
    CommandElabM CachedModelSource := do
  let namespaceParent := (← getCurrNamespace) ++ parent
  let candidates :=
    if namespaceParent == parent then #[parent] else #[namespaceParent, parent]
  let cache ← modelSourceCache.get
  for candidate in candidates do
    if let some cached := cache.get? candidate then
      return cached
  for candidate in candidates do
    if let some cached ← cachedModelSourceFromEnv? candidate then
      return cached
  throwError
    "unknown parent UFO model `{parent}` for extension; expected `{parent}.source` and `{parent}.tables` to be available from an earlier model or an imported module"

private def makeReusePlan
    (parent? : Option CachedModelSource) (source : ModelSource) (childTables : FactTables)
    (fresh : Bool) : String → Option Name :=
  match parent? with
  | none => fun _ => none
  | some parent =>
      fun field =>
        certificateReuseSource? parent.declaredName parent.source source
          parent.tables childTables fresh field

private def emitCompiledModelSource
    (cmdStx : Syntax) (model : Name) (source : ModelSource)
    (parent? : Option CachedModelSource := none) (fresh : Bool := false) :
    CommandElabM Unit := do
  let compiled ←
    match compileModelSource source with
    | .ok compiled => pure compiled
    | .error err => throwResolveError err
  let declaredModel ←
    emitModel cmdStx model (namesFromStrings source.worlds) (namesFromStrings source.things)
      source source.facts compiled.scopedFacts compiled.expandedFacts compiled.productFamilies
      compiled.tables (makeReusePlan parent? source compiled.tables fresh)
  modelSourceCache.modify (fun cache =>
    cache.insert declaredModel { source, tables := compiled.tables, declaredName := declaredModel })

elab_rules : command
  | `(ufo_model $model:ident : UFO where
      worlds $ws:ident*
      things $ts:ident*
      $blocks:ufoFactBlock*
      $families:ufoProductFamily*
      $derive:ufoDeriveDirective
      $cert:ufoCertDirective) => do
    let cmdStx ← getRef
    let _ := derive
    let _ := cert
    let worldNames := ws.map (·.getId)
    let thingNames := ts.map (·.getId)
    checkNoReservedWorldNames worldNames
    let worldNameStrings := worldNames.map (·.toString)
    let thingNameStrings := thingNames.map (·.toString)
    let (namedFacts, namedProductFamilies) ← parseBlocksAndFamilies worldNames thingNames blocks families
    let source : ModelSource :=
      ModelSource.mk worldNameStrings thingNameStrings namedFacts namedProductFamilies true
    emitCompiledModelSource cmdStx model.getId source

  | `(ufo_model $model:ident : UFO extends $parent:ident : UFO where
      things $ts:ident*
      $blocks:ufoFactBlock*
      $families:ufoProductFamily*
      $derive:ufoDeriveDirective
      $cert:ufoCertDirective) => do
    let cmdStx ← getRef
    let _ := derive
    let _ := cert
    let parentCached ← unsafe resolveParentModelSource parent.getId
    let parentSource := parentCached.source
    let thingNames := ts.map (·.getId)
    let childThingNameStrings := thingNames.map (·.toString)
    let allThingNames := namesFromStrings parentSource.things ++ thingNames
    let worldNames := namesFromStrings parentSource.worlds
    let (namedFacts, namedProductFamilies) ← parseBlocksAndFamilies worldNames allThingNames blocks families
    let childSource : ModelSource :=
      ModelSource.mk #[] childThingNameStrings namedFacts namedProductFamilies true
    let source ←
      match extendModelSource parentSource childSource with
      | .ok source => pure source
      | .error err => throwResolveError err
    emitCompiledModelSource cmdStx model.getId source (some parentCached) (isCertifyFresh cert)

  | `(ufo_model $model:ident : UFO extends $parent:ident : UFO where
      $blocks:ufoFactBlock*
      $families:ufoProductFamily*
      $derive:ufoDeriveDirective
      $cert:ufoCertDirective) => do
    let cmdStx ← getRef
    let _ := derive
    let parentCached ← unsafe resolveParentModelSource parent.getId
    let parentSource := parentCached.source
    let worldNames := namesFromStrings parentSource.worlds
    let thingNames := namesFromStrings parentSource.things
    let (namedFacts, namedProductFamilies) ← parseBlocksAndFamilies worldNames thingNames blocks families
    let childSource : ModelSource :=
      ModelSource.mk #[] #[] namedFacts namedProductFamilies true
    let source ←
      match extendModelSource parentSource childSource with
      | .ok source => pure source
      | .error err => throwResolveError err
    emitCompiledModelSource cmdStx model.getId source (some parentCached) (isCertifyFresh cert)

  | `(export_certificate $model:ident) => do
    let modelIdent := mkIdent model.getId
    elabCommand (← `(command| namespace $modelIdent))
    elabCommandString "def exportRequested : Bool := true"
    elabCommand (← `(command| end $modelIdent))

end LeanUfo.UFO.DSL
