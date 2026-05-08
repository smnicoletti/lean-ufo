import LeanUfo.Test.Coverage.RegistryCheck
import LeanUfo.Test.Diagnostics.Rendering

/-!
Executable test driver for `lake test`.

The default profile is intentionally fast: it checks importable syntax/
diagnostic smoke fixtures, stale syntax rejection, and the axiom manifest.
Set `LEANUFO_FULL_TESTS=1` to run the slower semantic positive/negative witness
suite as well.
-/

structure ExpectedFailure where
  field : String
  file : String
  expected : String
  requireCounterexample : Bool

structure ExpectedOutput where
  label : String
  file : String
  contains : Array String := #[]
  rejects : Array String := #[]

def fastExpectedFailures : Array ExpectedFailure := #[
  ⟨"syntax", "LeanUfo/Test/Syntax/RejectedOldSyntax.lean", "unexpected token ':'", false⟩
]

def fullExpectedFailures : Array ExpectedFailure := #[
  ⟨"ax7", "LeanUfo/Test/Certification/Negative/Ax7ConcreteType.lean", "certified_ax7", true⟩,
  ⟨"ax8", "LeanUfo/Test/Certification/Negative/Ax8AbstractType.lean", "certified_ax8", true⟩,
  ⟨"ax9", "LeanUfo/Test/Certification/Negative/Ax9ConcreteAbstract.lean", "certified_ax9", true⟩,
  ⟨"ax14", "LeanUfo/Test/Certification/Negative/Ax14ConcreteNeitherEndurantNorPerdurant.lean", "certified_ax14", true⟩,
  ⟨"ax15", "LeanUfo/Test/Certification/Negative/Ax15EndurantTypeNotType.lean", "certified_ax15", true⟩,
  ⟨"ax16", "LeanUfo/Test/Certification/Negative/Ax16PerdurantTypeNotType.lean", "certified_ax16", true⟩,
  ⟨"ax17", "LeanUfo/Test/Certification/Negative/Ax17EndurantPerdurantType.lean", "certified_ax17", true⟩,
  ⟨"ax19", "LeanUfo/Test/Certification/Negative/Ax19AntiRigidRigidType.lean", "certified_ax19", true⟩,
  ⟨"ax20", "LeanUfo/Test/Certification/Negative/Ax20SemiRigidRigidType.lean", "certified_ax20", true⟩,
  ⟨"ax21", "LeanUfo/Test/Certification/Negative/Ax21EndurantNoKind.lean", "certified_ax21", true⟩,
  ⟨"ax22", "LeanUfo/Test/Certification/Negative/Ax22MultipleKinds.lean", "certified_ax22", true⟩,
  ⟨"ax23", "LeanUfo/Test/Certification/Negative/Ax23MixinSortalWithoutKind.lean", "certified_ax23", true⟩,
  ⟨"ax24", "LeanUfo/Test/Certification/Negative/Ax24NonSortalSortal.lean", "certified_ax24", true⟩,
  ⟨"ax25", "LeanUfo/Test/Certification/Negative/Ax25KindAndSubKind.lean", "certified_ax25", true⟩,
  ⟨"ax26", "LeanUfo/Test/Certification/Negative/Ax26RigidSortalNeitherKindNorSubKind.lean", "certified_ax26", true⟩,
  ⟨"ax27", "LeanUfo/Test/Certification/Negative/Ax27PhaseAndRole.lean", "certified_ax27", true⟩,
  ⟨"ax28", "LeanUfo/Test/Certification/Negative/Ax28AntiRigidSortalNeitherPhaseNorRole.lean", "certified_ax28", true⟩,
  ⟨"ax30", "LeanUfo/Test/Certification/Negative/Ax30RigidNonSortalMissingCategory.lean", "certified_ax30", true⟩,
  ⟨"ax_instEndurant", "LeanUfo/Test/Certification/Negative/AxInstEndurantTypeHasNonEndurantInstance.lean", "certified_ax_instEndurant", true⟩,
  ⟨"ax34", "LeanUfo/Test/Certification/Negative/Ax34EndurantNeitherSubstantialNorMoment.lean", "certified_ax34", true⟩,
  ⟨"ax35", "LeanUfo/Test/Certification/Negative/Ax35SubstantialAndMoment.lean", "certified_ax35", true⟩,
  ⟨"ax36", "LeanUfo/Test/Certification/Negative/Ax36SubstantialWithoutSpecificKind.lean", "certified_ax36", true⟩,
  ⟨"ax37", "LeanUfo/Test/Certification/Negative/Ax37ObjectAndCollective.lean", "certified_ax37", true⟩,
  ⟨"ax38", "LeanUfo/Test/Certification/Negative/Ax38ObjectAndQuantity.lean", "certified_ax38", true⟩,
  ⟨"ax39", "LeanUfo/Test/Certification/Negative/Ax39CollectiveAndQuantity.lean", "certified_ax39", true⟩,
  ⟨"ax40", "LeanUfo/Test/Certification/Negative/Ax40MomentWithoutSpecificKind.lean", "certified_ax40", true⟩,
  ⟨"ax41", "LeanUfo/Test/Certification/Negative/Ax41RelatorAndIntrinsicMoment.lean", "certified_ax41", true⟩,
  ⟨"ax42", "LeanUfo/Test/Certification/Negative/Ax42IntrinsicMomentWithoutModeOrQuality.lean", "certified_ax42", true⟩,
  ⟨"ax43", "LeanUfo/Test/Certification/Negative/Ax43ModeAndQuality.lean", "certified_ax43", true⟩,
  ⟨"ax45", "LeanUfo/Test/Certification/Negative/Ax45ObjectTypeKindNotObjectKind.lean", "certified_ax45", true⟩,
  ⟨"ax46", "LeanUfo/Test/Certification/Negative/Ax46EndurantWithoutSpecificKind.lean", "certified_ax46", true⟩,
  ⟨"ax48", "LeanUfo/Test/Certification/Negative/Ax48PartAntisymmetry.lean", "certified_ax48", true⟩,
  ⟨"ax49", "LeanUfo/Test/Certification/Negative/Ax49PartTransitivity.lean", "certified_ax49", true⟩,
  ⟨"ax50", "LeanUfo/Test/Certification/Negative/Ax50OverlapWithoutCommonPart.lean", "certified_ax50", true⟩,
  ⟨"ax51", "LeanUfo/Test/Certification/Negative/Ax51StrongSupplementation.lean", "certified_ax51", true⟩,
  ⟨"ax52", "LeanUfo/Test/Certification/Negative/Ax52ProperPartWithoutPart.lean", "certified_ax52", true⟩,
  ⟨"ax56", "LeanUfo/Test/Certification/Negative/Ax56ConstitutionDifferentCategory.lean", "certified_ax56", true⟩,
  ⟨"ax57", "LeanUfo/Test/Certification/Negative/Ax57ConstitutionSameKind.lean", "certified_ax57", true⟩,
  ⟨"ax60", "LeanUfo/Test/Certification/Negative/Ax60PerdurantConstitutionNecessity.lean", "certified_ax60", true⟩,
  ⟨"ax65", "LeanUfo/Test/Certification/Negative/Ax65InherenceExistingMomentWithoutBearerExistence.lean", "certified_ax65", true⟩,
  ⟨"ax66", "LeanUfo/Test/Certification/Negative/Ax66InherenceFromNonMoment.lean", "certified_ax66", true⟩,
  ⟨"ax67", "LeanUfo/Test/Certification/Negative/Ax67MomentTwoBearers.lean", "certified_ax67", true⟩,
  ⟨"ax71", "LeanUfo/Test/Certification/Negative/Ax71FoundedByWrongFoundationType.lean", "certified_ax71", true⟩,
  ⟨"ax72", "LeanUfo/Test/Certification/Negative/Ax72ExternallyDependentModeNoFoundation.lean", "certified_ax72", true⟩,
  ⟨"ax73", "LeanUfo/Test/Certification/Negative/Ax73QuaIndividualFoundationBridge.lean", "certified_ax73", true⟩,
  ⟨"ax80", "LeanUfo/Test/Certification/Negative/Ax80MediatesWithoutRelator.lean", "certified_ax80", true⟩,
  ⟨"ax81", "LeanUfo/Test/Certification/Negative/Ax81CharacterizationWrongTypes.lean", "certified_ax81", true⟩,
  ⟨"ax85", "LeanUfo/Test/Certification/Negative/Ax85QualeAndSet.lean", "certified_ax85", true⟩,
  ⟨"ax86", "LeanUfo/Test/Certification/Negative/Ax86QualityStructureNotSet.lean", "certified_ax86", true⟩,
  ⟨"ax87", "LeanUfo/Test/Certification/Negative/Ax87QualeWithoutUniqueQualityStructure.lean", "certified_ax87", true⟩,
  ⟨"ax91", "LeanUfo/Test/Certification/Negative/Ax91QualityTypeWithoutStructure.lean", "certified_ax91", true⟩,
  ⟨"ax92", "LeanUfo/Test/Certification/Negative/Ax92HasValueWrongArguments.lean", "certified_ax92", true⟩,
  ⟨"ax100", "LeanUfo/Test/Certification/Negative/Ax100DistanceNonQuales.lean", "certified_ax100", true⟩,
  ⟨"ax102", "LeanUfo/Test/Certification/Negative/Ax102ManifestsWrongTypes.lean", "certified_ax102", true⟩,
  ⟨"ax103", "LeanUfo/Test/Certification/Negative/Ax103LifeOfWithoutManifestationOverlap.lean", "certified_ax103", true⟩,
  ⟨"ax104", "LeanUfo/Test/Certification/Negative/Ax104MeetWrongTypes.lean", "certified_ax104", true⟩,
  ⟨"ax13", "LeanUfo/Test/Certification/Negative/Ax13EndurantAndPerdurant.lean", "certified_ax13", true⟩,
  ⟨"ax18", "LeanUfo/Test/Certification/Negative/Ax18AntiRigidKind.lean", "certified_ax18", true⟩,
  ⟨"ax61", "LeanUfo/Test/Certification/Negative/Ax61SymmetricConstitution.lean", "certified_ax61", true⟩,
  ⟨"ax10", "LeanUfo/Test/Certification/Negative/Ax10FutureOnlyIndividualClassification.lean", "certified_ax10", true⟩,
  ⟨"ax77", "LeanUfo/Test/Certification/Negative/Ax77RelatorFoundedBy.lean", "certified_ax77", true⟩
]

def diagnosticOutputChecks : Array ExpectedOutput := #[
  {
    label := "ax13 counterexample rendering",
    file := "LeanUfo/Test/Certification/Negative/Ax13EndurantAndPerdurant.lean",
    contains := #[
      "A finite counterexample was confirmed for ax13.",
      "Forbidden condition:",
      "Suggestion:",
      "[actual] Object(X)",
      "[actual] Perdurant(X)"
    ],
    rejects := #[
      "X : Object",
      "X : Perdurant"
    ]
  },
  {
    label := "ax87 quality diagnostic rendering",
    file := "LeanUfo/Test/Certification/Negative/Ax87QualeWithoutUniqueQualityStructure.lean",
    contains := #[
      "A finite counterexample was confirmed for ax87.",
      "Missing witness requirements:",
      "[actual] Quale(V)"
    ],
    rejects := #[
      "V : Quale"
    ]
  }
]

structure PositiveWitness where
  field : String
  target : String

def fullPositiveWitnesses : Array PositiveWitness := #[
  ⟨"all", "LeanUfo.Test.Certification.Positive.AllAxioms"⟩,
  ⟨"seed", "LeanUfo.Test.Certification.Positive.Seed"⟩,
  ⟨"ax68", "LeanUfo.Test.Certification.Positive.Ax68"⟩
]

def second? {α : Type} : List α → Option α
  | List.cons _ (List.cons x _) => some x
  | _ => none

def first? {α : Type} : List α → Option α
  | List.cons x _ => some x
  | _ => none

def quotedAfter? (marker line : String) : Option String :=
  let pieces := line.splitOn marker
  match second? pieces with
  | none => none
  | some rest =>
      match first? (rest.splitOn "\"") with
      | some field => some field
      | none => none

def registryFields (src : String) : Array String :=
  Id.run do
    let mut fields := #[]
    for line in src.splitOn "\n" do
      match quotedAfter? "⟨\"" line with
      | some field => fields := fields.push field
      | none => pure ()
    pure fields

def manifestFields (src : String) : Array String :=
  Id.run do
    let mut fields := #[]
    let mut active := false
    for line in src.splitOn "\n" do
      if line.contains "def axiomCoverageManifest" then
        active := true
      else if active && line.contains "]" then
        active := false
      else if active && line.startsWith "  \"" then
        match quotedAfter? "\"" line with
        | some field => fields := fields.push field
        | none => pure ()
    pure fields

def checkCoverageManifest : IO (Array String) := do
  let registrySrc ← IO.FS.readFile "LeanUfo/UFO/DSL/Certificate/Generation.lean"
  let manifestSrc ← IO.FS.readFile "LeanUfo/Test/Coverage/AxiomManifest.lean"
  let registry := registryFields registrySrc
  let manifest := manifestFields manifestSrc
  let mut failures := #[]
  for field in registry do
    if !manifest.contains field then
      failures := failures.push s!"manifest missing certificate field {field}"
  for field in manifest do
    if !registry.contains field then
      failures := failures.push s!"manifest has stale certificate field {field}"
  pure failures

def arrayLiteralFields (defName src : String) : Array String :=
  Id.run do
    let mut fields := #[]
    let mut active := false
    for line in src.splitOn "\n" do
      if line.contains s!"def {defName}" then
        active := true
      else if active && line.contains "]" then
        active := false
      else if active && line.contains "\"" then
        match quotedAfter? "\"" line with
        | some field => fields := fields.push field
        | none => pure ()
    pure fields

def requireDirectCoverageEnabled : IO Bool := do
  match (← IO.getEnv "LEANUFO_REQUIRE_DIRECT_WITNESSES") with
  | some "1" => pure true
  | some "true" => pure true
  | some "yes" => pure true
  | _ => pure false

def checkDirectWitnessCoverage : IO (Array String) := do
  let manifestSrc ← IO.FS.readFile "LeanUfo/Test/Coverage/AxiomManifest.lean"
  let manifest := manifestFields manifestSrc
  let directNegatives := arrayLiteralFields "directNegativeWitnessAxioms" manifestSrc
  let enforcedNegatives := arrayLiteralFields "compilerEnforcedNegativeAxioms" manifestSrc
  let blockedNegatives := arrayLiteralFields "blockedNegativeWitnessAxioms" manifestSrc
  let mut failures := #[]
  for field in manifest do
    let categoryCount :=
      (if directNegatives.contains field then 1 else 0) +
      (if enforcedNegatives.contains field then 1 else 0) +
      (if blockedNegatives.contains field then 1 else 0)
    if categoryCount == 0 then
      failures := failures.push s!"negative coverage category missing for {field}"
    if categoryCount > 1 then
      failures := failures.push s!"negative coverage category duplicated for {field}"
    if (← requireDirectCoverageEnabled) && !directNegatives.contains field then
      failures := failures.push s!"missing direct negative witness for {field}"
  pure failures

def expectedFailureFields : Array String :=
  fullExpectedFailures.map (·.field)

def expectedFailureFiles : Array String :=
  fullExpectedFailures.map (·.file)

def findLeanFiles (dir : String) : IO (Array String) := do
  let out ← IO.Process.output {
    cmd := "find"
    args := #[dir, "-type", "f", "-name", "*.lean"]
  }
  if out.exitCode == 0 then
    pure <| (out.stdout.splitOn "\n").foldl
      (fun acc line =>
        let line := line.trimAscii.toString
        if line.isEmpty then acc else acc.push line)
      #[]
  else
    pure #[]

def checkExpectedFailureRegistration : IO (Array String) := do
  let manifestSrc ← IO.FS.readFile "LeanUfo/Test/Coverage/AxiomManifest.lean"
  let directNegatives := arrayLiteralFields "directNegativeWitnessAxioms" manifestSrc
  let registeredFields := expectedFailureFields
  let registeredFiles := expectedFailureFiles
  let mut failures := #[]
  for field in directNegatives do
    if !registeredFields.contains field then
      failures := failures.push s!"direct negative witness for {field} is not registered in fullExpectedFailures"
  for field in registeredFields do
    if !directNegatives.contains field then
      failures := failures.push s!"fullExpectedFailures registers {field}, but the manifest does not classify it as a direct negative witness"
  for file in registeredFiles do
    if !(← System.FilePath.pathExists file) then
      failures := failures.push s!"registered negative fixture is missing: {file}"
  let fixtureFiles ← findLeanFiles "LeanUfo/Test/Certification/Negative"
  for file in fixtureFiles do
    if file.endsWith ".lean" && !registeredFiles.contains file then
      failures := failures.push s!"negative fixture is not registered in fullExpectedFailures: {file}"
  pure failures

def selectedAxioms : IO (Array String) := do
  match (← IO.getEnv "LEANUFO_AXIOMS") with
  | none => pure #[]
  | some raw =>
      pure <| (raw.splitOn ",").foldl
        (fun out item =>
          let item := item.trimAscii.toString
          if item.isEmpty then out else out.push item)
        #[]

def selectedContains (selected : Array String) (field : String) : Bool :=
  selected.isEmpty || selected.contains field || selected.contains "all"

def filterExpectedFailures (selected : Array String) (tests : Array ExpectedFailure) :
    Array ExpectedFailure :=
  tests.filter fun test => selectedContains selected test.field

def filterPositiveWitnesses (selected : Array String) (tests : Array PositiveWitness) :
    Array PositiveWitness :=
  if selected.isEmpty then
    tests.filter (·.field == "seed")
  else if selected.contains "all" then
    tests.filter (·.field == "all")
  else
    let direct := tests.filter fun test =>
      selectedContains selected test.field && test.field != "all" && test.field != "seed"
    let directFields := direct.map (·.field)
    let needsShared := selected.any fun field => !directFields.contains field
    if needsShared then
      direct ++ tests.filter (·.field == "all")
    else
      direct

structure NegativeCoverageCategories where
  direct : Array String
  enforced : Array String
  blocked : Array String

def negativeCoverageCategories : IO NegativeCoverageCategories := do
  let manifestSrc ← IO.FS.readFile "LeanUfo/Test/Coverage/AxiomManifest.lean"
  pure {
    direct := arrayLiteralFields "directNegativeWitnessAxioms" manifestSrc
    enforced := arrayLiteralFields "compilerEnforcedNegativeAxioms" manifestSrc
    blocked := arrayLiteralFields "blockedNegativeWitnessAxioms" manifestSrc
  }

def selectedAxiomsForReport (selected : Array String) : IO (Array String) := do
  if selected.contains "all" then
    let manifestSrc ← IO.FS.readFile "LeanUfo/Test/Coverage/AxiomManifest.lean"
    pure <| manifestFields manifestSrc
  else
    pure selected

def directPositiveFields (tests : Array PositiveWitness) : Array String :=
  (tests.filter fun test => test.field != "all" && test.field != "seed").map (·.field)

def positiveCoverageLine (directFields : Array String) (field : String) : String :=
  if directFields.contains field then
    "positive: direct fixture"
  else
    "positive: shared all-axioms certified fixture"

def negativeCoverageLine (cats : NegativeCoverageCategories) (field : String) : String :=
  if cats.direct.contains field then
    "negative: direct fixture with confirmed finite counterexample"
  else if cats.enforced.contains field then
    "negative: no direct DSL counterexample expected; compiler/finite semantics enforces it"
  else if cats.blocked.contains field then
    "negative: blocked; no managed direct counterexample witness yet"
  else
    "negative: unclassified"

def selectedCoverageReport
    (selected positiveFields : Array String) (cats : NegativeCoverageCategories) : IO String := do
  let fields ← selectedAxiomsForReport selected
  if fields.isEmpty then
    pure ""
  else
    let lines := fields.map fun field =>
      s!"- {field}: {positiveCoverageLine positiveFields field}; {negativeCoverageLine cats field}"
    pure <| "Selected axiom coverage:\n" ++ String.intercalate "\n" lines.toList

def checkExpectedFailure (test : ExpectedFailure) : IO (Array String) := do
  let out ← IO.Process.output {
    cmd := "lake"
    args := #["env", "lean", test.file]
  }
  let text := out.stdout ++ out.stderr
  if out.exitCode == 0 then
    pure #[s!"{test.file} unexpectedly succeeded"]
  else if text.contains test.expected then
    if test.requireCounterexample &&
        !text.contains s!"A finite counterexample was confirmed for {test.field}." then
      pure #[s!"{test.file} failed at `{test.expected}`, but did not confirm a finite counterexample"]
    else
      pure #[]
  else
    pure #[s!"{test.file} failed, but output did not contain `{test.expected}`"]

def checkExpectedOutput (test : ExpectedOutput) : IO (Array String) := do
  let out ← IO.Process.output {
    cmd := "lake"
    args := #["env", "lean", test.file]
  }
  let text := out.stdout ++ out.stderr
  let mut failures := #[]
  if out.exitCode == 0 then
    failures := failures.push s!"{test.label}: {test.file} unexpectedly succeeded"
  for needle in test.contains do
    if !text.contains needle then
      failures := failures.push s!"{test.label}: output did not contain `{needle}`"
  for needle in test.rejects do
    if text.contains needle then
      failures := failures.push s!"{test.label}: output still contained stale text `{needle}`"
  pure failures

def checkCommand (label cmd : String) (args : Array String) : IO (Array String) := do
  let out ← IO.Process.output { cmd := cmd, args := args }
  if out.exitCode == 0 then
    pure #[]
  else
    pure #[s!"{label} failed with exit code {out.exitCode}"]

def fullTestsEnabled : IO Bool := do
  if !(← selectedAxioms).isEmpty then
    pure true
  else
    match (← IO.getEnv "LEANUFO_FULL_TESTS") with
    | some "1" => pure true
    | some "true" => pure true
    | some "yes" => pure true
    | _ => pure false

def main : IO UInt32 := do
  let mut failures := #[]
  let selected ← selectedAxioms
  let negativeCategories ← negativeCoverageCategories
  failures := failures ++ (← checkCoverageManifest)
  failures := failures ++ (← checkDirectWitnessCoverage)
  failures := failures ++ (← checkExpectedFailureRegistration)
  for test in fastExpectedFailures do
    failures := failures ++ (← checkExpectedFailure test)
  if (← fullTestsEnabled) then
    let positiveWitnesses := filterPositiveWitnesses selected fullPositiveWitnesses
    let negativeWitnesses := filterExpectedFailures selected fullExpectedFailures
    if !selected.isEmpty && positiveWitnesses.isEmpty && negativeWitnesses.isEmpty then
      failures := failures.push
        s!"no direct semantic witness registered for selected axioms: {String.intercalate ", " selected.toList}"
    for test in positiveWitnesses do
      failures := failures ++ (← checkCommand s!"positive semantic witness {test.field}" "lake"
        #["build", test.target])
    for test in negativeWitnesses do
      failures := failures ++ (← checkExpectedFailure test)
    for test in diagnosticOutputChecks do
      if selected.isEmpty || selected.contains "all" then
        failures := failures ++ (← checkExpectedOutput test)
      else if selected.any fun field => test.file.contains s!"/{field.capitalize}" then
        failures := failures ++ (← checkExpectedOutput test)
  if failures.isEmpty then
    if !(← fullTestsEnabled) then
      IO.println "LeanUfo DSL tests passed (fast profile; set LEANUFO_FULL_TESTS=1 for semantic witness checks)"
    else if selected.isEmpty then
      IO.println "LeanUfo DSL tests passed (full profile)"
    else
      IO.println s!"LeanUfo DSL tests passed (selected axioms: {String.intercalate ", " selected.toList})"
      IO.println (← selectedCoverageReport selected (directPositiveFields fullPositiveWitnesses) negativeCategories)
    pure 0
  else
    for failure in failures do
      IO.eprintln failure
    pure 1
