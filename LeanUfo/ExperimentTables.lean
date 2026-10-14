import LeanUfo.PerformanceExperiments

/-!
# Tables from a completed experiment

This executable checks the recorded outcomes, raw observations, process logs,
and recomputed statistics before rendering tables. It never runs experiments.
Warm-up observations remain available for validation but do not enter statistics.
The templates under `docs/experiment-tables/` contain presentation and case names;
all measurements come from the selected run. The same generated fragments can
be included in a manuscript and in the standalone report.

Validation detects incomplete or inconsistent data, not malicious fabrication.
The metadata identifies the measured sources, which can differ from the current
checkout used to render a historical run. Rendering does not relabel that run.
-/

namespace LeanUfo.ExperimentTables
open Lean System PerformanceExperiments

def readJson (path : FilePath) : IO Json := do
  decode (Json.parse (← IO.FS.readFile path))

def sameFields (a b : Json) (keys : Array String) : IO Unit := do
  for key in keys do
    require ((← decode (a.getObjVal? key)) == (← decode (b.getObjVal? key)))
      s!"recorded field differs from its source: {key}"

def exactlyOne (rows : Array Json) (message : String) : IO Json := do
  require (rows.size == 1) s!"expected one {message}, found {rows.size}"
  return rows[0]!

def select (rows : Array Json) (fields : List (String × Json)) : Array Json :=
  rows.filter fun row => fields.all fun (key, value) => (row.getObjVal? key).toOption == some value

structure Dataset where
  directory : FilePath
  metadata : Json
  runs : Nat
  rows : Array Json

/-- Reconstruct the observation inventory from independently saved process logs.
An arbitrary error cannot stand in for a confirmed axiom violation. Every round,
including the warm-up, must contain exactly the registered cases. -/
def loadDataset (directory : FilePath) : IO Dataset := do
  let result ← readJson (directory / "result.json")
  require ((← decode (result.getObjValAs? Bool "valid"))) "experiment did not pass validation"
  require ((← decode (result.getObjValAs? (Array Json) "errors")).isEmpty) "experiment contains errors"
  let metadata ← readJson (directory / "metadata.json")
  let runs ← nat metadata "runs"
  require (runs > 0 && (← nat result "requested_runs") == runs) "invalid repetition count"
  require ((← nat metadata "schema") == 1 && (← nat metadata "warmups") == 1)
    "unsupported experiment schema or warm-up protocol"
  let lines := (← IO.FS.readFile (directory / "raw.jsonl")).splitOn "\n"
  let raw ← (lines.filter (! ·.isEmpty)).toArray.mapM fun line => decode (Json.parse line)
  let executable := cases.filter (! ·.models.isEmpty)
  let expectedModels := executable.foldl (fun n fixture => n + fixture.models.size) 0
  let perRound := expectedModels + executable.size + families.size * syntheticSizes.size
  require (raw.size == perRound * (runs + 1) + 1) "missing or surplus raw observations"
  let coverage ← exactlyOne (select raw [("kind", toJson "coverage")]) "coverage record"
  require ((← str coverage "case") == "ConceptEvolution" && (← str coverage "status") == "unsupported")
    "unsupported-case coverage changed"
  let rows := raw.filter fun row => (row.getObjValAs? String "kind").toOption != some "coverage"
  for row in rows do
    require ((← nat row "repetition") ≤ runs) "observation outside the requested repetitions"
  for repetition in [:runs + 1] do
    let round := select rows [("repetition", toJson repetition)]
    require (round.size == perRound) "incomplete repetition"
    for fixture in executable do
      let records := select round [("case", toJson fixture.file)]
      let file ← exactlyOne (select records [("kind", toJson "file")]) fixture.file
      let models := select records [("kind", toJson "model")]
      let log ← IO.FS.readFile (directory / s!"{repetition}-{fixture.file}.log")
      let logged ← modelRows log
      let exitCode ← nat file "exit_code"
      require (exitCode ≤ 1) "unexpected process exit code"
      validateModels fixture logged ⟨exitCode.toUInt32, ← nat file "elapsed_ns", false, log⟩
      require (models.size == fixture.models.size) "incomplete model observations"
      let expectedStatus := if fixture.failedAxiom.isSome then "expected-rejection" else "certified"
      require ((← str file "status") == expectedStatus) "unexpected file outcome"
      for i in [:logged.size] do
        let model ← exactlyOne (select models [("model", toJson fixture.models[i]!)]) fixture.models[i]!
        sameFields model logged[i]! #["model", "status", "mode", "worlds", "things", "facts", "elapsed_ns"]
        let baseline ← exactlyOne (select rows [("kind", toJson "model"),
          ("model", toJson fixture.models[i]!), ("repetition", toJson (0 : Nat))]) "model baseline"
        sameFields model baseline #["status", "mode", "worlds", "things", "facts"]
    let logged ← syntheticRows (← IO.FS.readFile (directory / s!"{repetition}-synthetic.log"))
    for entry in logged do
      let family ← str entry "family"
      let things ← nat entry "things"
      let query := [("kind", toJson "synthetic"), ("family", toJson family), ("things", toJson things)]
      let row ← exactlyOne (select round query) s!"{family}/{things}"
      let baseline ← exactlyOne (select rows (query ++ [("repetition", toJson (0 : Nat))])) "synthetic baseline"
      let keys := (← decode entry.getObj?).toList.map Prod.fst |>.toArray
      sameFields row entry keys
      sameFields row baseline (keys.filter (! ·.endsWith "_ns"))
  require ((← IO.FS.readFile (directory / "summary.csv")) == (← summaryCSV rows))
    "summary.csv does not match statistics recomputed from raw observations"
  return ⟨directory, metadata, runs, rows⟩

def decimal (value : Float) (places : Nat) : String := Id.run do
  let scale := 10 ^ places
  let rounded := (Float.floor (value * scale.toFloat + 0.5)).toUInt64.toNat
  if places == 0 then return toString rounded
  let fraction := toString (rounded % scale)
  return toString (rounded / scale) ++ "." ++ String.ofList (List.replicate (places - fraction.length) '0') ++ fraction

/-- Keep two significant digits of the sample deviation and match the mean's
decimal places. A single run cannot supply a deviation estimate. -/
def timing (values : Array Nat) (unit : Float) : String := Id.run do
  let s := statistics values
  let some sd := s.sd | do
    let mut places := 0
    while places < 6 && s.mean / unit * (10 ^ places).toFloat < 100 do
      places := places + 1
    return "$" ++ decimal (s.mean / unit) places ++ "$ (SD n/a)"
  let mut places := 0
  while places < 6 && sd / unit * (10 ^ places).toFloat < 10 do
    places := places + 1
  return "$" ++ decimal (s.mean / unit) places ++ " \\pm " ++ decimal (sd / unit) places ++ "$"

def grouped (n : Nat) : String :=
  String.ofList <| (toString n).toList.reverse.zipIdx.foldl (fun acc (c, i) =>
    c :: (if i > 0 && i % 3 == 0 then '\\' :: ',' :: acc else acc)) []

def texEscape (text : String) : String :=
  String.join <| text.toList.map fun c => match c with
  | '\\' => "\\textbackslash{}" | '{' => "\\{" | '}' => "\\}"
  | '$' => "\\$" | '&' => "\\&" | '#' => "\\#" | '_' => "\\_"
  | '%' => "\\%" | '~' => "\\textasciitilde{}" | '^' => "\\textasciicircum{}"
  | '\n' => " " | '\r' => " " | _ => String.singleton c

def measured (data : Dataset) (fields : List (String × Json)) : Array Json :=
  select data.rows fields |>.filter fun row => (row.getObjValAs? Nat "repetition").toOption != some 0

def measuredTimes (data : Dataset) (fields : List (String × Json)) (key : String) : IO (Array Nat) := do
  let rows := measured data fields
  require (rows.size == data.runs) "table selector does not match all repetitions"
  rows.mapM fun row => nat row key

def token (data : Dataset) (name : String) : IO String := do
  match name.splitOn ":" with
  | ["summary", key] =>
    let mut successes : Array Float := #[]
    let mut failures : Array Float := #[]
    for fixture in cases do
      for model in fixture.models do
        let values ← measuredTimes data [("kind", toJson "model"), ("model", toJson model)] "elapsed_ns"
        let mean := (statistics values).mean / 1000000000
        if fixture.failedAxiom.isSome && model == fixture.models.back! then
          failures := failures.push mean
        else successes := successes.push mean
    let range := fun values =>
      let sorted := values.qsort (· < ·)
      decimal sorted[0]! 3 ++ "--" ++ decimal sorted.back! (if sorted.back! > 1 then 1 else 3) ++ "\\,s"
    match key with
    | "successes" => return toString successes.size
    | "failures" => return toString failures.size
    | "under-second" => return toString (successes.filter (· < 1)).size
    | "success-range" => return range successes
    | "failure-range" => return range failures
    | "reuse" =>
      let mut faster := 0
      for (reuse, fresh) in #[ ("CarWithWindow", "CarWithWindowFresh"),
          ("PersonWithEmploymentRole", "PersonWithEmploymentRoleFresh"),
          ("PersonWithEnrollmentMode", "PersonWithEnrollmentModeFresh") ] do
        let r ← measuredTimes data [("kind", toJson "model"), ("model", toJson reuse)] "elapsed_ns"
        let f ← measuredTimes data [("kind", toJson "model"), ("model", toJson fresh)] "elapsed_ns"
        if (statistics r).mean < (statistics f).mean then faster := faster + 1
      return if faster == 0 then "No observed speedup over fresh checking."
        else s!"{faster}/3 faster; declaration order uncontrolled."
    | _ => throw <| IO.userError s!"unknown summary: {key}"
  | ["model", model] => return timing (← measuredTimes data
      [("kind", toJson "model"), ("model", toJson model)] "elapsed_ns") 1000000000
  | ["file", file] => return timing (← measuredTimes data
      [("kind", toJson "file"), ("case", toJson file)] "elapsed_ns") 1000000000
  | [field, model] =>
    require (#["worlds", "things", "mode"].contains field) s!"unknown token: {name}"
    let row ← exactlyOne (select data.rows [("kind", toJson "model"),
      ("model", toJson model), ("repetition", toJson (0 : Nat))]) name
    if field == "mode" then
      match (← str row field) with
      | "base" => return "B" | "reuse-enabled" => return "R" | "fresh" => return "F"
      | other => throw <| IO.userError s!"unknown checking mode: {other}"
    return toString (← nat row field)
  | ["synthetic", family, size, stage] =>
    let some things := size.toNat? | throw <| IO.userError s!"invalid size in {name}"
    require (#["compiler", "model", "checker", "probe"].contains stage) s!"unknown stage: {stage}"
    return timing (← measuredTimes data [("kind", toJson "synthetic"),
      ("family", toJson family), ("things", toJson things)] (stage ++ "_ns"))
      (if stage == "model" then 1000 else 1000000)
  | ["count", family, size] =>
    let some things := size.toNat? | throw <| IO.userError s!"invalid size in {name}"
    let row ← exactlyOne (select data.rows [("kind", toJson "synthetic"),
      ("family", toJson family), ("things", toJson things), ("repetition", toJson (0 : Nat))]) name
    return "$" ++ grouped (← nat row "probe_cost") ++ "$"
  | _ => throw <| IO.userError s!"unknown table token: {name}"

def substitute (data : Dataset) (template : String) : IO String := do
  -- A delimiter distinct from TeX braces avoids interpreting nested macro
  -- arguments as placeholders. Odd-indexed pieces are the requested values.
  let parts := (template.splitOn "@@").toArray
  require (parts.size % 2 == 1) "unclosed table token"
  let mut result := ""
  for i in [:parts.size] do
    let piece ← if i % 2 == 0 then pure parts[i]! else token data parts[i]!
    result := result ++ piece
  require (!(result.contains "@@")) "unexpanded table token"
  return result

def tableNames := #["evaluation-overview", "source-cases", "largest-inputs", "model-times", "file-times", "operation-counts", "synthetic-times"]

def writeTables (data : Dataset) (output : FilePath) : IO Unit := do
  IO.FS.createDirAll output
  IO.FS.writeFile (output / "report-result.json") "{\"valid\":false}"
  for name in tableNames do
    let template ← IO.FS.readFile (FilePath.mk "docs/experiment-tables" / (name ++ ".tex"))
    IO.FS.writeFile (output / (name ++ ".tex")) (← substitute data template)
  let system ← decode (data.metadata.getObjVal? "machine")
  let intro := "\\section*{ALIEN experiment tables}\n" ++
    "Dataset: \\texttt{" ++ texEscape (data.directory.fileName.getD "run") ++ "}.\\par\n" ++
    s!"{data.runs} measured repetitions after one excluded warm-up. " ++
    "Entries report means and sample standard deviations; a single measured run has no deviation estimate.\\par\n" ++
    "Recorded system: " ++ texEscape (← str system "system") ++ ".\\par\n" ++
    "Certification timings include proof processing. Synthetic inputs are expected to fail aggregate checking; " ++
    "their targeted operations run independently. These timings do not measure successful certification. " ++
    "Source hashes and the measurement protocol remain in the unchanged metadata.json.\n"
  let preamble := "\\documentclass[10pt]{article}\n\\usepackage[T1]{fontenc}\n" ++
    "\\usepackage[textwidth=122mm,textheight=193mm]{geometry}\n" ++
    "\\usepackage{amsmath,booktabs,array,tabularx,longtable,hyperref}\n" ++
    "\\newcolumntype{Y}{>{\\raggedright\\arraybackslash}X}\n" ++
    "\\newcommand{\\code}[1]{\\texttt{#1}}\n" ++
    "\\newcommand{\\ufocat}[1]{\\textsf{#1}}\n\\begin{document}\n\\raggedbottom\n"
  let inputs := String.join (tableNames.toList.map fun name => "\\input{" ++ name ++ "}\n\\clearpage\n")
  IO.FS.writeFile (output / "tables.tex") (preamble ++ intro ++ inputs ++ "\\end{document}\n")
  -- Preserve provenance even when the output is outside the selected run.
  IO.FS.writeFile (output / "measurement-metadata.json") data.metadata.pretty
  IO.FS.writeFile (output / "report-provenance.json") <| (Json.mkObj [
    ("dataset", toJson data.directory.toString), ("runs", toJson data.runs),
    ("renderer_source_hashes", ← sourceSnapshot),
    ("validation", toJson "Expected inventory, log agreement, stable case metadata/counts, and recomputed summary CSV.")]).pretty
  for pass in [:2] do
    let result ← IO.Process.output {
      cmd := "pdflatex"
      cwd := some output
      args := #["-no-shell-escape", "-interaction=nonstopmode", "-halt-on-error", "tables.tex"] }
    IO.FS.writeFile (output / s!"pdflatex-{pass + 1}.log") (result.stdout ++ result.stderr)
    require (result.exitCode == 0) s!"PDF generation failed; inspect {output}/pdflatex-{pass + 1}.log"
  progress s!"Validated tables and PDF: {output}/tables.pdf"
  IO.FS.writeFile (output / "report-result.json") "{\"valid\":true}"

def latestDataset : IO FilePath := do
  let root := FilePath.mk ((← IO.getEnv "LEANUFO_EXPERIMENT_DIR").getD "experiments")
  require (← root.isDir) "no experiments directory; specify --input RUN"
  let mut candidates : Array FilePath := #[]
  for entry in (← root.readDir) do
    if (← (entry.path / "metadata.json").pathExists) then candidates := candidates.push entry.path
  require (!candidates.isEmpty) "no experiment metadata found; run experiments or specify --input RUN"
  return (candidates.qsort (fun a b => a.toString < b.toString)).back!

def selfTest : IO Unit := do
  PerformanceExperiments.selfTest
  require (decimal 1.735 3 == "1.735" && decimal 0.005 3 == "0.005") "decimal formatting"
  require (grouped 631784 == "631\\,784") "grouped operation count"
  require (timing #[10] 1 == "$10.0$ (SD n/a)") "single-run reporting"
  require (timing #[800] 1000000 == "$0.000800$ (SD n/a)") "small single-run timing"
  require (timing #[10, 20, 30] 1 == "$20 \\pm 10$") "sample deviation reporting"
  require (texEscape "a_b%" == "a\\_b\\%") "TeX escaping"
  let bad ← try discard (exactlyOne #[] "test"); pure false catch _ => pure true
  require bad "missing observations must be rejected"
  let dummy : Dataset := ⟨"unused", Json.null, 1, #[]⟩
  require ((← substitute dummy "\\foo{{nested}}") == "\\foo{{nested}}") "TeX brace preservation"
  let bad ← try discard (substitute dummy "@@unclosed"); pure false catch _ => pure true
  require bad "unclosed template tokens must fail"

/-- Exercise failure paths on temporary copies, never on the reference run.
The one-run fixture verifies that SD is unavailable rather than reported as zero. -/
def testDataset (directory : FilePath) : IO Unit := do
  let original ← loadDataset directory
  IO.FS.withTempDir fun temporary => do
    for entry in (← directory.readDir) do
      if #[some "json", some "jsonl", some "csv", some "log"].contains entry.path.extension then
        IO.FS.writeFile (temporary / entry.fileName) (← IO.FS.readFile entry.path)
    discard (loadDataset temporary)
    for (name, replacement) in #[("result.json", "{\"valid\":false}"),
        ("summary.csv", "stale summary"), ("raw.jsonl", ""),
        ("1-FailedStudentEnrollment.log", "unrelated type error")] do
      let path := temporary / name
      let saved ← IO.FS.readFile path
      IO.FS.writeFile path replacement
      let rejected ← try discard (loadDataset temporary); pure false catch _ => pure true
      require rejected s!"corruption was accepted: {name}"
      IO.FS.writeFile path saved
    let single := original.rows.filter fun row =>
      ((row.getObjValAs? Nat "repetition").toOption.getD 2) ≤ 1
    let coverage := Json.mkObj [("kind", toJson "coverage"), ("case", toJson "ConceptEvolution"),
      ("status", toJson "unsupported")]
    IO.FS.writeFile (temporary / "metadata.json") ((original.metadata.setObjValAs! "runs" (1 : Nat)).pretty)
    IO.FS.writeFile (temporary / "result.json")
      "{\"valid\":true,\"errors\":[],\"requested_runs\":1}"
    let raw := String.join ((single.push coverage).toList.map (fun row => row.compress ++ "\n"))
    IO.FS.writeFile (temporary / "raw.jsonl") raw
    IO.FS.writeFile (temporary / "summary.csv") (← summaryCSV single)
    let one ← loadDataset temporary
    require ((← token one "model:MinimalCommand").contains "SD n/a") "one-run deviation"
    let duplicate := single.set! 1 single[0]!
    IO.FS.writeFile (temporary / "raw.jsonl")
      (String.join ((duplicate.push coverage).toList.map (fun row => row.compress ++ "\n")))
    let rejected ← try discard (loadDataset temporary); pure false catch _ => pure true
    require rejected "duplicate observations must fail even with the expected row count"
  progress "PASS: complete, one-run, missing, duplicate, invalid, stale-summary and mismatched-log datasets"

end LeanUfo.ExperimentTables

open LeanUfo.ExperimentTables in
def main (args : List String) : IO UInt32 := do
    if args == ["--self-test"] then selfTest; return 0
    if let ["--test-data", path] := args then testDataset path; return 0
    let mut input : Option System.FilePath := none
    let mut output : Option System.FilePath := none
    let mut rest := args
    while !rest.isEmpty do
      match rest with
      | "--input" :: path :: tail => input := some path; rest := tail
      | "--output" :: path :: tail => output := some path; rest := tail
      | _ => throw <| IO.userError "usage: experiment-tables [--input RUN] [--output DIR] (or --self-test)"
    selfTest
    let directory ← match input with | some path => pure path | none => latestDataset
    let data ← loadDataset directory
    writeTables data (output.getD (directory / "tables"))
    return 0
