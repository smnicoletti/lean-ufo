import Lean
import Lean.Util.Path
import LeanUfo.UFO.DSL.Compiler.AST

open Lean

namespace LeanUfo.CertificateCli

/-- Parse one complete Lean identifier without importing the target module.
Whitespace and comments outside escaped components are rejected, so attaching
a field suffix cannot change how the generated command is parsed. -/
def parseLeanName (text : String) : IO Name := do
  let env ← mkEmptyEnvironment
  let input := Parser.mkInputContext text "<certificate name>" (normalizeLineEndings := false)
  let state := (Parser.rawIdentFn (includeWhitespace := false)).run input
    { env, options := {} } {} (Parser.mkParserState text)
  unless !state.hasError && state.pos == text.rawEndPos && state.stxStack.size == 1 do
    throw <| IO.userError "expected one complete Lean identifier"
  match state.stxStack.back with
  | .ident _ _ name _ => pure name
  | _ => throw <| IO.userError "expected one complete Lean identifier"

/-- Render every component as an escaped identifier. Lean's `Name.toString`
also prints pseudo-syntax (including names beginning with `#` or `?`), so it
cannot serve as a source-code escaping boundary for manifest data. -/
def leanNameSource : Name → Except String String
  | .str parent part => do
      let some escaped := Name.escapePart part (force := true)
        | throw "name component cannot be represented as a Lean identifier"
      match parent with
      | .anonymous => pure escaped
      | _ => return (← leanNameSource parent) ++ "." ++ escaped
  | _ => .error "expected a nonempty Lean name with string components"

def identifierSource (text : String) : IO String := do
  match leanNameSource (← parseLeanName text) with
  | .ok source => pure source
  | .error message => throw <| IO.userError message

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

def tempDir : IO System.FilePath := do
  match (← IO.getEnv "TMPDIR") with
  | some dir =>
      if dir.isEmpty then pure ("/tmp" : System.FilePath) else pure dir
  | none =>
      match (← IO.getEnv "TEMP") with
      | some dir =>
          if dir.isEmpty then pure ("/tmp" : System.FilePath) else pure dir
      | none =>
          match (← IO.getEnv "TMP") with
          | some dir =>
              if dir.isEmpty then pure ("/tmp" : System.FilePath) else pure dir
          | none => pure ("/tmp" : System.FilePath)

def firstToken (s : String) : Option String :=
  s.trimAscii.toString.splitOn " " |>.head?

def sha256OfString (content : String) : IO String := IO.FS.withTempFile fun handle file => do
  handle.putStr content
  handle.flush
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

def leanProcessEnv : IO (Array (String × Option String)) := do
  pure #[("LEAN_PATH", some (System.SearchPath.toString (← lakeSearchPath)))]

/-- Execute generated source in a private temporary directory. Callers must
render external identifiers before constructing `source`. A fresh directory
prevents concurrent exports or rechecks from replacing each other's scripts. -/
def runLeanScript (source : String) : IO IO.Process.Output :=
  IO.FS.withTempDir fun dir => do
    let script := dir / "certificate.lean"
    IO.FS.writeFile script source
    IO.Process.output { cmd := "lean", args := #[script.toString], env := (← leanProcessEnv) }

private def evalExpressionTextViaLean
    (moduleString modelString suffix expression : String) : IO String := do
  let source :=
    s!"import {moduleString}\n" ++
    s!"#eval IO.println ({expression})\n"
  let out ← runLeanScript source
  if out.exitCode == 0 then
    pure out.stdout
  else
    throw <| IO.userError s!"failed to evaluate {suffix} text for {modelString}:\n{out.stderr}"

def modelSourceTextViaLean (moduleString modelString : String) : IO String := do
  let moduleSource ← identifierSource moduleString
  let modelSource ← identifierSource modelString
  evalExpressionTextViaLean moduleSource modelString "source"
    s!"reprStr {modelSource}.source"

def finiteModelTextViaLean (moduleString modelString : String) : IO String := do
  let moduleSource ← identifierSource moduleString
  let modelSource ← identifierSource modelString
  evalExpressionTextViaLean moduleSource modelString "tables"
    ("reprStr " ++ modelSource ++ ".tables.unary ++ \"\\n\" ++ " ++
      "reprStr " ++ modelSource ++ ".tables.binary ++ \"\\n\" ++ " ++
      "reprStr " ++ modelSource ++ ".tables.ternary ++ \"\\n\" ++ " ++
      "reprStr " ++ modelSource ++ ".tables.tupleProjection ++ \"\\n\" ++ " ++
      "reprStr " ++ modelSource ++ ".tables.productFamilies ++ \"\\n\" ++ " ++
      "reprStr " ++ modelSource ++ ".tables.derivedProps")

def modelDigestsViaLean (moduleString modelString : String) :
    IO (String × String) := do
  let sourceText ← modelSourceTextViaLean moduleString modelString
  let tablesText ← finiteModelTextViaLean moduleString modelString
  let sourceDigest ← sha256OfString sourceText
  let finiteModelDigest ← sha256OfString tablesText
  pure (sourceDigest, finiteModelDigest)

def parseModuleName (s : String) : Name :=
  s.toName

unsafe def loadModule (module : Name) : IO Environment := do
  unsafe enableInitializersExecution
  initSearchPath (← findSysroot) (← lakeSearchPath)
  importModules #[{ module := module, importAll := true, isMeta := true }] {} (loadExts := true)

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

/-!
Manifest discovery reads declarations from the compiled Lean module. This
avoids treating comments as commands and preserves the namespace that Lean
assigned to each model. The module-index check excludes manifests imported
from dependencies.
-/
unsafe def moduleManifests (env : Environment) (moduleName : Name) :
    IO (Array (Name × LeanUfo.UFO.DSL.CertificateManifest × Bool)) := do
  let some moduleIdx := env.getModuleIdx? moduleName
    | throw <| IO.userError s!"could not find loaded module `{moduleName}`"
  let mut out := #[]
  for (declName, _info) in env.constants.toList do
    if env.getModuleIdxFor? declName == some moduleIdx &&
        nameLast? declName == some "certificateManifest" then
      match nameParent? declName, (← evalManifest? env declName) with
      | some modelName, some manifest =>
          let requested ← evalExportRequested? env modelName
          out := out.push (modelName, manifest, requested)
      | _, _ => pure ()
  pure <| out.qsort fun left right => left.1.toString < right.1.toString

unsafe def manifestByModel? (env : Environment) (model : Name) :
    IO (Option LeanUfo.UFO.DSL.CertificateManifest) :=
  evalManifest? env (Name.str model "certificateManifest")

def selectModuleManifests
    (manifests : Array (Name × LeanUfo.UFO.DSL.CertificateManifest × Bool)) :
    Array (Name × LeanUfo.UFO.DSL.CertificateManifest × Bool) :=
  let requested := manifests.filter fun entry => entry.2.2
  if requested.isEmpty then manifests else requested

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
