import Lean
import Lean.Util.Path
import LeanUfo.UFO.DSL.Compiler.AST

open Lean

namespace LeanUfo.CertificateCli

def nameParent? : Name → Option Name
  | .str parent _ => some parent
  | .num parent _ => some parent
  | .anonymous => none

def nameLast? : Name → Option String
  | .str _ last => some last
  | .num _ n => some (toString n)
  | .anonymous => none

def jsonNullOrString : Option String → Json
  | none => Json.null
  | some value => Json.str value

def addExportMetadata
    (manifest : LeanUfo.UFO.DSL.CertificateManifest)
    (gitCommit gitTag sourceDigest finiteModelDigest : Option String) :
    LeanUfo.UFO.DSL.CertificateManifest :=
  { manifest with
    gitCommit := gitCommit
    gitTag := gitTag
    sourceDigest := sourceDigest
    finiteModelDigest := finiteModelDigest }

def runGit (args : Array String) : IO (Option String) := do
  let out ← IO.Process.output { cmd := "git", args := args }
  if out.exitCode == 0 then
    let value := out.stdout.trimAscii.toString
    if value.isEmpty then pure none else pure (some value)
  else
    pure none

def currentGitCommit : IO (Option String) :=
  runGit #["rev-parse", "HEAD"]

def currentGitTag : IO (Option String) :=
  runGit #["describe", "--tags", "--exact-match", "HEAD"]

def sanitizeFileStem (s : String) : String :=
  s.map fun c =>
    if c.isAlphanum then c else '-'

def firstToken (s : String) : Option String :=
  s.trimAscii.toString.splitOn " " |>.head?

def sha256OfString (label content : String) : IO String := do
  let file : System.FilePath := s!"/private/tmp/lean-ufo-{sanitizeFileStem label}.sha-input"
  IO.FS.writeFile file content
  let shasum ← IO.Process.output { cmd := "shasum", args := #["-a", "256", file.toString] }
  if shasum.exitCode == 0 then
    match firstToken shasum.stdout with
    | some digest => pure s!"sha256:{digest}"
    | none => throw <| IO.userError "shasum produced empty output"
  else
    let sha256sum ← IO.Process.output { cmd := "sha256sum", args := #[file.toString] }
    if sha256sum.exitCode == 0 then
      match firstToken sha256sum.stdout with
      | some digest => pure s!"sha256:{digest}"
      | none => throw <| IO.userError "sha256sum produced empty output"
    else
      throw <| IO.userError
        s!"could not compute SHA-256 digest; shasum failed with:\n{shasum.stderr}\nsha256sum failed with:\n{sha256sum.stderr}"

def evalExpressionTextViaLean
    (moduleString modelString suffix expression : String) : IO String := do
  let tmp : System.FilePath :=
    ("/private/tmp" : System.FilePath) /
      s!"lean-ufo-text-{sanitizeFileStem moduleString}-{sanitizeFileStem modelString}-{sanitizeFileStem suffix}.lean"
  let source :=
    s!"import {moduleString}\n" ++
    s!"#eval IO.println ({expression})\n"
  IO.FS.writeFile tmp source
  let out ← IO.Process.output { cmd := "lake", args := #["env", "lean", tmp.toString] }
  if out.exitCode == 0 then
    pure out.stdout
  else
    throw <| IO.userError s!"failed to evaluate {suffix} text for {modelString}:\n{out.stderr}"

def modelSourceTextViaLean (moduleString modelString : String) : IO String :=
  evalExpressionTextViaLean moduleString modelString "source"
    s!"reprStr {modelString}.source"

def finiteModelTextViaLean (moduleString modelString : String) : IO String :=
  evalExpressionTextViaLean moduleString modelString "tables"
    ("reprStr " ++ modelString ++ ".tables.unary ++ \"\\n\" ++ " ++
      "reprStr " ++ modelString ++ ".tables.binary ++ \"\\n\" ++ " ++
      "reprStr " ++ modelString ++ ".tables.ternary ++ \"\\n\" ++ " ++
      "reprStr " ++ modelString ++ ".tables.tupleProjection ++ \"\\n\" ++ " ++
      "reprStr " ++ modelString ++ ".tables.productFamilies ++ \"\\n\" ++ " ++
      "reprStr " ++ modelString ++ ".tables.derivedProps")

def modelDigestsViaLean (moduleString modelString : String) :
    IO (String × String) := do
  let sourceText ← modelSourceTextViaLean moduleString modelString
  let tablesText ← finiteModelTextViaLean moduleString modelString
  let sourceDigest ← sha256OfString s!"{moduleString}-{modelString}-source" sourceText
  let finiteModelDigest ← sha256OfString s!"{moduleString}-{modelString}-tables" tablesText
  pure (sourceDigest, finiteModelDigest)

def parseModuleName (s : String) : Name :=
  s.toName

def lakeSearchPath : IO SearchPath := do
  let cwd ← IO.currentDir
  let mut paths : Array System.FilePath := #[cwd / ".lake" / "build" / "lib" / "lean"]
  let packagesDir := cwd / ".lake" / "packages"
  if (← packagesDir.pathExists) then
    for entry in (← packagesDir.readDir) do
      let packageLeanLib := entry.path / ".lake" / "build" / "lib" / "lean"
      if (← packageLeanLib.pathExists) then
        paths := paths.push packageLeanLib
  pure paths.toList

unsafe def loadModule (module : Name) : IO Environment := do
  initSearchPath (← findSysroot) (← lakeSearchPath)
  importModules #[{ module := module, importAll := true, isMeta := true }] {}

unsafe def evalManifest? (env : Environment) (declName : Name) :
    IO (Option LeanUfo.UFO.DSL.CertificateManifest) := do
  match (unsafe env.evalConstCheck LeanUfo.UFO.DSL.CertificateManifest {}
      ``LeanUfo.UFO.DSL.CertificateManifest declName) with
  | .ok manifest => pure (some manifest)
  | .error _ => pure none

unsafe def evalExportRequested? (env : Environment) (modelName : Name) : IO Bool := do
  let declName := Name.str modelName "exportRequested"
  match (unsafe env.evalConstCheck Bool {} ``Bool declName) with
  | .ok value => pure value
  | .error _ => pure false

unsafe def moduleManifests (env : Environment) :
    IO (Array (Name × LeanUfo.UFO.DSL.CertificateManifest × Bool)) := do
  let mut out := #[]
  for (declName, _info) in env.constants.toList do
    if nameLast? declName == some "certificateManifest" then
      match nameParent? declName, (← evalManifest? env declName) with
      | some modelName, some manifest =>
          let requested ← evalExportRequested? env modelName
          out := out.push (modelName, manifest, requested)
      | _, _ => pure ()
  pure out

def moduleSourcePath (moduleName : Name) : System.FilePath :=
  let rel := moduleName.toString.replace "." "/"
  (rel ++ ".lean")

private def firstIdentifierAfter (pfx line : String) : Option String :=
  if !line.trimAscii.toString.startsWith pfx then
    none
  else
    let rest := (line.trimAscii.toString.drop pfx.length).trimAscii.toString
    rest.splitOn " " |>.head?

def sourceExportMarkers (content : String) : Array String :=
  content.splitOn "\n" |>.foldl (init := #[]) fun acc line =>
    match firstIdentifierAfter "export_certificate " line with
    | some name => acc.push name
    | none => acc

def sourceModelNames (content : String) : Array String :=
  content.splitOn "\n" |>.foldl (init := #[]) fun acc line =>
    match firstIdentifierAfter "ufo_model " line with
    | some name => acc.push name
    | none => acc

unsafe def manifestByModel? (env : Environment) (model : Name) :
    IO (Option LeanUfo.UFO.DSL.CertificateManifest) :=
  evalManifest? env (Name.str model "certificateManifest")

unsafe def moduleManifestsFromSource (env : Environment) (moduleName : Name) :
    IO (Array (Name × LeanUfo.UFO.DSL.CertificateManifest × Bool)) := do
  let path := moduleSourcePath moduleName
  if !(← path.pathExists) then
    pure #[]
  else
    let content ← IO.FS.readFile path
    let markers := sourceExportMarkers content
    let candidateNames := if markers.isEmpty then sourceModelNames content else markers
    let mut out := #[]
    for modelString in candidateNames do
      let model := modelString.toName
      match (← manifestByModel? env model) with
      | some manifest => out := out.push (model, manifest, markers.contains modelString)
      | none => pure ()
    pure out

def usageExport : String :=
  "usage: lake exe export-certificates --module Module.Name --out certificates/"

def usageValidate : String :=
  "usage: lake exe validate-certificate manifest.json --module Module.Name [--structure-only]"

partial def parseFlagValue (flag : String) : List String → Option String
  | [] => none
  | x :: y :: xs => if x == flag then some y else parseFlagValue flag (y :: xs)
  | [_] => none

def ensureDir (path : System.FilePath) : IO Unit :=
  IO.FS.createDirAll path

def manifestFileName (manifest : LeanUfo.UFO.DSL.CertificateManifest) : String :=
  manifest.modelName ++ ".certificate.json"

end LeanUfo.CertificateCli
