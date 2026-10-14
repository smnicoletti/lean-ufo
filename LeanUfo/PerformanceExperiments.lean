import Lean

/-!
# Reproducible example and algorithm timings

`LEANUFO_PERFORMANCE_TESTS=N lake test` runs the full regression gate and then
this executable with N measured repetitions. Every source file is elaborated
in a fresh process with dependencies already built. Replicate zero is a warm-up:
its observations are retained, but excluded from averages and sample deviations.

Example summaries measure compilation through certificate or diagnostic output,
including generated proof processing. Synthetic timings measure the counted
algorithms, including their instrumentation; they do not construct certificates.
Raw observations, logs, machine information, source hashes, and summary CSV are
saved under `experiments/`. A failed outcome invalidates the experiment;
timeouts and incomplete runs are never presented as successful timing samples.
-/

namespace LeanUfo.PerformanceExperiments
open Lean System

structure ExampleCase where
  file : String
  models : Array String
  failedAxiom : Option String := none
deriving Inhabited

/-- Register outcomes explicitly: an arbitrary Lean error is not evidence of
the intended diagnostic. Directory coverage prevents omissions as examples grow. -/
def cases : Array ExampleCase := #[
  ⟨"Minimal", #["MinimalCommand"], none⟩,
  ⟨"Company", #["CompanyExample"], none⟩,
  ⟨"Role", #["RoleExample"], none⟩,
  ⟨"WoodenTable", #["WoodenTableExample"], none⟩,
  ⟨"SchoolRoles", #["SchoolRolesExample"], none⟩,
  ⟨"FlowerPropertyChange", #["FlowerPropertyChangeExample"], none⟩,
  ⟨"RedirectedWalk", #["RedirectedWalkExample"], none⟩,
  ⟨"UltimateBearer", #["UltimateBearerExample"], none⟩,
  ⟨"StudentEnrollmentMode", #["StudentEnrollmentModeExample"], none⟩,
  ⟨"GrantGoal", #["GrantGoalExample"], none⟩,
  ⟨"ColorSpaceProductFamily", #["ColorSpaceProductFamily", "ColorSpaceProductFamilyFacts"], none⟩,
  ⟨"ReuseModelExtension", #["CarBase", "CarWithWindow", "CarWithWindowFresh", "CarBaseAlias"], none⟩,
  ⟨"ReuseRoleExtension", #["PersonLifecycleBase", "PersonWithEmploymentRole", "PersonWithEmploymentRoleFresh"], none⟩,
  ⟨"ReuseModeExtension", #["PersonBearerBase", "PersonWithEnrollmentMode", "PersonWithEnrollmentModeFresh"], none⟩,
  ⟨"RelatorProbe", #["RelatorProbe"], none⟩,
  ⟨"FailedConstitution", #["FailedConstitutionExample"], some "ax61"⟩,
  ⟨"FailedFlowerTaxonomy", #["FailedFlowerTaxonomyExample"], some "ax18"⟩,
  ⟨"FailedRoleTaxonomy", #["FailedRoleTaxonomyExample"], some "ax13"⟩,
  ⟨"FailedStudentEnrollment", #["StudentEnrollment"], some "ax10"⟩,
  ⟨"FailedReuseExtension", #["ValidVehicleBaseExample", "InvalidVehicleExtensionExample"], some "ax13"⟩,
  ⟨"FailedReuseConstitutionExtension", #["ValidConstitutionBaseExample", "InvalidSymmetricConstitutionExtensionExample"], some "ax61"⟩,
  ⟨"ConceptEvolution", #[], none⟩]

def examplesDir : FilePath := "LeanUfo/UFO/DSL/ConcreteExamples"
def marker := "[lean-ufo-experiment] "

def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

def progress (message : String) : IO Unit := do
  IO.println message
  (← IO.getStdout).flush

def decode (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw <| IO.userError message

def str (row : Json) (key : String) : IO String := decode (row.getObjValAs? String key)
def nat (row : Json) (key : String) : IO Nat := decode (row.getObjValAs? Nat key)

def capture (cmd : String) (args : Array String := #[]) : IO String := do
  try
    let result ← IO.Process.output { cmd, args }
    return if result.exitCode == 0 then result.stdout.trimAscii.toString else "unavailable"
  catch _ => return "unavailable"

structure ProcessResult where
  code : UInt32
  elapsedNs : Nat
  timedOut : Bool
  text : String

def defaultTimeoutSeconds : Nat := 3600

/-- Slow hosts can raise the watchdog limit without changing the measured work.
Zero is rejected so every measured subprocess retains a finite timeout. -/
def parseTimeoutSeconds (value : Option String) : Except String Nat := do
  match value with
  | none => return defaultTimeoutSeconds
  | some text =>
    match text.toNat? with
    | some seconds =>
      if seconds > 0 then return seconds
      else throw "LEANUFO_EXPERIMENT_TIMEOUT_SECONDS must be a positive integer"
    | none => throw "LEANUFO_EXPERIMENT_TIMEOUT_SECONDS must be a positive integer"

#guard (parseTimeoutSeconds none).toOption == some 3600
#guard (parseTimeoutSeconds (some "600")).toOption == some 600
#guard (parseTimeoutSeconds (some "0")).toOption.isNone
#guard (parseTimeoutSeconds (some "-1")).toOption.isNone
#guard (parseTimeoutSeconds (some "")).toOption.isNone
#guard (parseTimeoutSeconds (some "true")).toOption.isNone

/-- Drain both pipes concurrently. The wait task timestamps process completion;
the watchdog's polling interval therefore does not quantize the measurement.
On POSIX, cancellation kills the process group, including spawned compilers. -/
def runProcess (cmd : String) (args : Array String) (log : FilePath)
    (timeoutSeconds : Nat := defaultTimeoutSeconds) : IO ProcessResult := do
  let start ← IO.monoNanosNow
  let child ← IO.Process.spawn {
    cmd, args
    stdin := .null
    stdout := .piped
    stderr := .piped
    setsid := true
    env := #[("LEANUFO_CERT_PROFILE", none), ("LEANUFO_EXPERIMENT_TIMING", some "1")] }
  let outTask ← IO.asTask child.stdout.readToEnd .dedicated
  let errTask ← IO.asTask child.stderr.readToEnd .dedicated
  let waitTask ← IO.asTask (do
    let code ← child.wait
    return (code, (← IO.monoNanosNow) - start)) .dedicated
  let mut timedOut := false
  while !(← IO.hasFinished waitTask) do
    if (← IO.monoNanosNow) - start > timeoutSeconds * 1000000000 then
      child.kill
      timedOut := true
      break
    IO.sleep 10
  let (code, elapsedNs) ← IO.ofExcept waitTask.get
  let stdout ← IO.ofExcept outTask.get
  let stderr ← IO.ofExcept errTask.get
  let text := stdout ++ "\n" ++ stderr
  IO.FS.writeFile log text
  return { code, elapsedNs, timedOut, text }

def modelRows (text : String) : IO (Array Json) := do
  let mut rows := #[]
  for line in text.splitOn "\n" do
    let parts := line.splitOn marker
    if parts.length > 1 then rows := rows.push (← decode (Json.parse parts[1]!))
  return rows

def validateModels (fixture : ExampleCase) (rows : Array Json) (result : ProcessResult) : IO Unit := do
  require (!result.timedOut) s!"{fixture.file}: exceeded the process timeout"
  require (rows.size == fixture.models.size) s!"{fixture.file}: missing or duplicate model summaries"
  for i in [:rows.size] do
    require ((← str rows[i]! "model") == fixture.models[i]!) s!"{fixture.file}: unexpected model order/name"
    let status := if fixture.failedAxiom.isSome && i + 1 == rows.size then "rejected" else "certified"
    require ((← str rows[i]! "status") == status) s!"{fixture.file}: unexpected certification outcome"
    let _ ← nat rows[i]! "elapsed_ns"
  match fixture.failedAxiom with
  | none => require (result.code == 0) s!"{fixture.file}: Lean exited with {result.code}"
  | some ax =>
    require (result.code == 1 && result.text.contains s!"A finite counterexample was confirmed for {ax}.")
      s!"{fixture.file}: expected a confirmed {ax} violation"

def syntheticSizes := #[2, 3, 5, 9, 17, 33]
def families := #["sparse", "dense", "cyclic", "product", "projection"]

def syntheticRows (text : String) : IO (Array Json) := do
  let lines := (text.splitOn "\n").filter (fun line => !line.isEmpty)
  let lines := lines.dropWhile (fun line => !line.startsWith "family,things,")
  require (!lines.isEmpty) "missing synthetic CSV header"
  let columns := lines.head!.splitOn ","
  let mut rows := #[]
  let mut seen : Array (String × Nat) := #[]
  for line in lines.tail! do
    let cells := line.splitOn ","
    require (columns.length == cells.length) "malformed synthetic CSV row"
    let fields ← (columns.zip cells).mapM fun (key, value) => do
      if #["family", "probe", "result", "probe_passed"].contains key then
        pure (key, toJson value)
      else
        let some n := value.toNat? | throw <| IO.userError s!"invalid synthetic number: {value}"
        pure (key, toJson n)
    let row := Json.mkObj fields
    let family ← str row "family"
    let things ← nat row "things"
    require (families.contains family && syntheticSizes.contains things && !seen.contains (family, things))
      "unexpected or duplicate synthetic case"
    require ((← str row "result") == "false" && (← str row "probe_passed") == "true")
      "synthetic fixture outcome changed"
    seen := seen.push (family, things)
    rows := rows.push row
  require (rows.size == families.size * syntheticSizes.size) "missing synthetic cases"
  return rows

structure Statistics where
  mean : Float
  sd : Option Float
  median : Float
  minimum : Nat
  maximum : Nat

def statistics (values : Array Nat) : Statistics := Id.run do
  let sorted := values.qsort (· < ·)
  let count := values.size
  let mean := (values.foldl (· + ·.toFloat) 0) / count.toFloat
  let variance := values.foldl (fun total n => total + (n.toFloat - mean) * (n.toFloat - mean)) 0
  let median := if count % 2 == 0 then
      (sorted[count / 2 - 1]!.toFloat + sorted[count / 2]!.toFloat) / 2
    else sorted[count / 2]!.toFloat
  return {
    mean, median
    sd := if count > 1 then some (Float.sqrt (variance / (count - 1).toFloat)) else none
    minimum := sorted[0]!
    maximum := sorted[count - 1]! }

def csvCell (value : String) : String := "\"" ++ value.replace "\"" "\"\"" ++ "\""

structure Group where
  key : Array String
  values : Array Nat

def addSample (groups : Array Group) (key : Array String) (value : Nat) : Array Group :=
  match groups.findIdx? (·.key == key) with
  | none => groups.push ⟨key, #[value]⟩
  | some i => groups.modify i fun group => { group with values := group.values.push value }

def summaryCSV (rows : Array Json) : IO String := do
  let mut groups := #[]
  for row in rows do
    if (← nat row "repetition") == 0 then continue
    let kind ← str row "kind"
    if kind == "model" then
      groups := addSample groups #[kind, ← str row "case", ← str row "model",
        ← str row "status", ← str row "mode", "compile_to_result"] (← nat row "elapsed_ns")
    else if kind == "file" then
      let status ← str row "status"
      if status != "invalid" && status != "timeout" then
        groups := addSample groups #[kind, ← str row "case", "", status, "", "process"] (← nat row "elapsed_ns")
    else if kind == "synthetic" then
      for stage in #["compiler", "model", "checker", "probe"] do
        groups := addSample groups #[kind, ← str row "family", toString (← nat row "things"),
          "probe-passed/model-rejected", "instrumented", stage] (← nat row (stage ++ "_ns"))
  let mut text := "kind,case,model_or_size,status,mode,stage,runs,mean_ns,sd_ns,median_ns,min_ns,max_ns\n"
  for group in groups do
    let s := statistics group.values
    let fields := group.key ++ #[toString group.values.size, toString s.mean,
      s.sd.map toString |>.getD "", toString s.median, toString s.minimum, toString s.maximum]
    text := text ++ String.intercalate "," (fields.toList.map csvCell) ++ "\n"
  return text

def writeSummary (output : FilePath) (rows : Array Json) : IO Unit := do
  IO.FS.writeFile (output / "summary.csv") (← summaryCSV rows)

def record (output : FilePath) (row : Json) : IO Unit :=
  IO.FS.withFile (output / "raw.jsonl") .append fun file => file.putStrLn row.compress

def enrich (row : Json) (fields : List (String × Json)) : IO Json := do
  let object ← decode row.getObj?
  return Json.mkObj (object.toList ++ fields)

def machine : IO Json := do
  let mut fields := [("system", toJson (← capture "uname" #["-smr"])),
    ("lean", toJson (← capture "lake" #["env", "lean", "--version"]))]
  if System.Platform.isOSX then
    fields := fields ++ [("os_version", toJson (← capture "sw_vers" #["-productVersion"]))]
    for key in #["machdep.cpu.brand_string", "hw.memsize", "hw.physicalcpu", "hw.logicalcpu",
        "hw.perflevel0.physicalcpu", "hw.perflevel1.physicalcpu"] do
      fields := fields ++ [(key, toJson (← capture "sysctl" #["-n", key]))]
  else if System.Platform.isLinux then
    for name in #["cpuinfo", "meminfo"] do
      let contents ← IO.FS.readFile (FilePath.mk "/proc" / name)
      let useful := (contents.splitOn "\n").find? fun line =>
        line.startsWith "model name" || line.startsWith "MemTotal"
      fields := fields ++ [(name, toJson (useful.getD "unavailable"))]
    for path in #["/etc/os-release", "/sys/fs/cgroup/memory.max", "/sys/fs/cgroup/cpu.max",
        "/sys/fs/cgroup/cpuset.cpus.effective"] do
      let contents ← try IO.FS.readFile path catch _ => pure "unavailable"
      fields := fields ++ [(path, toJson contents.trimAscii.toString)]
    fields := fields ++ [("container_source", toJson ((← IO.getEnv "ALIEN_SOURCE_REVISION").getD "not supplied")),
      ("lean_threads", toJson ((← IO.getEnv "LEAN_NUM_THREADS").getD "default"))]
  return Json.mkObj fields

/-- Hash source contents independently of Git tracking, including new modules.
`git hash-object` also works in an unpacked source archive without Git history. -/
def sourceSnapshot : IO Json := do
  let paths ← FilePath.walkDir "LeanUfo"
  let paths := paths.filter (·.extension == some "lean") |>.map (·.toString)
  let paths := (paths ++ #["LeanUfoTest.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain"]).qsort (· < ·)
  let hashes ← capture "git" (#["hash-object", "--"] ++ paths)
  require (hashes != "unavailable") "git hash-object is required to record experiment sources"
  let hashes := hashes.splitOn "\n"
  require (hashes.length == paths.size) "source hashing returned an incomplete manifest"
  return Json.mkObj (paths.toList.zip hashes |>.map fun (path, digest) => (path, toJson digest))

def validateCoverage : IO Unit := do
  let actual := (← examplesDir.readDir).filter (·.path.extension == some "lean")
  let actual := actual.map (fun entry => entry.fileName.dropEnd 5 |>.toString)
  require (actual.size == cases.size && actual.all (fun name => cases.any (·.file == name)))
    "register all files in ConcreteExamples before running experiments"

def selfTest : IO Unit := do
  let s := statistics #[10, 20, 30]
  require (s.mean == 20 && s.sd == some 10 && s.median == 20) "statistics regression"
  require ((statistics #[10]).sd.isNone) "one observation must not claim a standard deviation"
  let even := statistics #[3, 1]
  require (even.median == 2 && even.minimum == 1 && even.maximum == 3) "even median/range regression"
  let rows ← modelRows ("info: " ++ marker ++ "{\"model\":\"MinimalCommand\",\"status\":\"certified\",\"elapsed_ns\":1}")
  let result : ProcessResult := ⟨0, 1, false, ""⟩
  validateModels cases[0]! rows result
  let rejected ← try validateModels cases[0]! #[] result; pure false catch _ => pure true
  require rejected "missing timing summaries must fail validation"
  let failed ← modelRows (marker ++ "{\"model\":\"StudentEnrollment\",\"status\":\"rejected\",\"elapsed_ns\":1}")
  let rejected ← try validateModels cases[18]! failed ⟨1, 1, false, "type error"⟩; pure false catch _ => pure true
  require rejected "an arbitrary error must not count as an expected counterexample"
  let rejected ← try validateModels cases[0]! rows { result with timedOut := true }; pure false catch _ => pure true
  require rejected "a timeout must invalidate even a complete model summary"
  let header := "family,things,result,probe_passed,compiler_ns,model_ns,checker_ns,probe_ns\n"
  let mut body := ""
  for family in families do
    for size in syntheticSizes do
      body := body ++ s!"{family},{size},false,true,1,2,3,4\n"
  require ((← syntheticRows (header ++ body)).size == 30) "synthetic parser regression"
  for malformed in #[header, header ++ body ++ "sparse,2,false,true,1,2,3,4\n",
      (header ++ body).replace "false,true" "true,true"] do
    let rejected ← try discard (syntheticRows malformed); pure false catch _ => pure true
    require rejected "incomplete, duplicate, or changed synthetic outcomes must fail validation"

def run (runs : Nat) : IO UInt32 := do
  require (runs > 0) "the repetition count must be positive"
  let timeoutSeconds ← decode (parseTimeoutSeconds (← IO.getEnv "LEANUFO_EXPERIMENT_TIMEOUT_SECONDS"))
  let buildTimeoutSeconds := max 1800 timeoutSeconds
  selfTest
  validateCoverage
  let stamp ← capture "date" #["-u", "+%Y%m%dT%H%M%SZ"]
  let root := FilePath.mk ((← IO.getEnv "LEANUFO_EXPERIMENT_DIR").getD "experiments")
  let output : FilePath := root / s!"{stamp}-{← IO.monoNanosNow}"
  IO.FS.createDirAll output
  progress s!"Experiment output: {output}"
  let snapshot ← sourceSnapshot
  let metadata := Json.mkObj [
    ("schema", toJson (1 : Nat)), ("runs", toJson runs), ("warmups", toJson (1 : Nat)),
    ("timeout_seconds", toJson timeoutSeconds),
    ("build_timeout_seconds", toJson buildTimeoutSeconds), ("machine", ← machine),
    ("commit", toJson (← capture "git" #["rev-parse", "HEAD"])),
    ("worktree_status", toJson (← capture "git" #["status", "--short"])),
    ("source_git_blob_hashes", snapshot), ("synthetic_sizes", toJson syntheticSizes),
    ("protocol", toJson "Sequential fresh processes, prebuilt dependencies, one retained but unreported warm-up; no OS cache flushing. Model timing: compilation through certificate/diagnostic data, excluding surface parsing/parent merging and React rendering. File timing: lake env startup, imports, parsing, all commands. Synthetic timing: counted implementation, including instrumentation and probe fixture validation. Source declaration order is unchanged; reuse/fresh times are not a controlled speedup comparison.")]
  IO.FS.writeFile (output / "metadata.json") metadata.pretty
  let build ← runProcess "lake" #["build", "LeanUfo.UFO.DSL.Syntax", "complexity-benchmarks"]
    (output / "build.log") buildTimeoutSeconds
  require (build.code == 0 && !build.timedOut) s!"dependency build failed; inspect {output}/build.log"
  let executable := cases.filter (! ·.models.isEmpty)
  let mut observations := #[]
  let mut errors : Array String := #[]
  let mut reference : Array Json := #[]
  for repetition in [:runs + 1] do
    -- Rotate file order between repetitions; never rearrange declarations in
    -- a source file, because extensions require their earlier parent models.
    for offset in [:executable.size] do
      let fixture := executable[(offset + repetition) % executable.size]!
      progress s!"[{repetition}/{runs}] {fixture.file}"
      let log := output / s!"{repetition}-{fixture.file}.log"
      let result ← runProcess "lake" #["env", "lean", (examplesDir / (fixture.file ++ ".lean")).toString] log timeoutSeconds
      let mut status := if result.timedOut then "timeout" else "invalid"
      try
        let rows ← modelRows result.text
        validateModels fixture rows result
        status := if fixture.failedAxiom.isSome then "expected-rejection" else "certified"
        for row in rows do
          let row ← enrich row [("kind", toJson "model"), ("case", toJson fixture.file), ("repetition", toJson repetition)]
          record output row
          observations := observations.push row
      catch e => errors := errors.push s!"run {repetition}: {e}"
      let row := Json.mkObj [("kind", toJson "file"), ("case", toJson fixture.file),
        ("repetition", toJson repetition), ("status", toJson status), ("exit_code", toJson result.code.toNat),
        ("elapsed_ns", toJson result.elapsedNs), ("log", toJson log.toString)]
      record output row
      observations := observations.push row
    let result ← runProcess ".lake/build/bin/complexity-benchmarks" #["--extended"] (output / s!"{repetition}-synthetic.log") timeoutSeconds
    try
      require (result.code == 0 && !result.timedOut) "synthetic process failed or timed out"
      let rows ← syntheticRows result.text
      let mut deterministic := #[]
      for row in rows do
        let object ← decode row.getObj?
        deterministic := deterministic.push <| Json.mkObj (object.toList.filter fun (key, _) => !key.endsWith "_ns")
      if repetition == 0 then reference := deterministic
      else require (deterministic == reference) "synthetic counts or fixture metadata changed between runs"
      for row in rows do
        let row ← enrich row [("kind", toJson "synthetic"), ("repetition", toJson repetition)]
        record output row
        observations := observations.push row
    catch e =>
      errors := errors.push s!"run {repetition}: {e}"
      record output <| Json.mkObj [("kind", toJson "synthetic-error"), ("repetition", toJson repetition),
        ("timeout", toJson result.timedOut), ("exit_code", toJson result.code.toNat)]
    writeSummary output observations
    if !errors.isEmpty then break
  record output <| Json.mkObj [("kind", toJson "coverage"), ("case", toJson "ConceptEvolution"),
    ("status", toJson "unsupported"), ("reason", toJson "documentation only; no executable model")]
  if (← sourceSnapshot) != snapshot then
    errors := errors.push "experiment sources changed during measurement; do not use these results"
  IO.FS.writeFile (output / "result.json") <| (Json.mkObj [
    ("valid", toJson errors.isEmpty), ("errors", toJson errors), ("requested_runs", toJson runs)]).pretty
  progress s!"{if errors.isEmpty then "PASS" else "FAIL"}: {output}"
  for error in errors do IO.eprintln error
  -- The test driver uses this handoff to render this exact run, independent
  -- of directory names or other saved experiments in the same output root.
  if errors.isEmpty then
    if let some destination ← IO.getEnv "LEANUFO_EXPERIMENT_RESULT_PATH" then
      IO.FS.writeFile destination (← IO.FS.realPath output).toString
  return if errors.isEmpty then 0 else 1

def main (args : List String) : IO UInt32 := do
  if args == ["--self-test"] then
    LeanUfo.PerformanceExperiments.selfTest
    return 0
  let [count] := args | throw <| IO.userError "usage: performance-experiments N (or --self-test)"
  let some runs := count.toNat? | throw <| IO.userError "N must be a positive integer"
  LeanUfo.PerformanceExperiments.run runs

end LeanUfo.PerformanceExperiments
