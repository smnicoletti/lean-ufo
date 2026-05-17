import Lean
import LeanUfo.CertificateCli

open Lean
open LeanUfo.CertificateCli

namespace LeanUfo.ExportCertificates

private def leanStringTerm (s : String) : String :=
  reprStr s

private def optionStringTerm : Option String → String
  | none => "none"
  | some s => "some " ++ leanStringTerm s

private def evalManifestJsonViaLean
    (moduleString modelString : String) (gitCommit gitTag : Option String)
    (sourceDigest finiteModelDigest : String) :
    IO String := do
  let tmp ← tempFilePath s!"export-{moduleString}-{modelString}" "lean"
  let source :=
    s!"import {moduleString}\n" ++
    "#eval IO.println (({ " ++ modelString ++ ".certificateManifest with " ++
    s!"gitCommit := {optionStringTerm gitCommit}, " ++
    s!"gitTag := {optionStringTerm gitTag}, " ++
    s!"sourceDigest := some {leanStringTerm sourceDigest}, " ++
    s!"finiteModelDigest := some {leanStringTerm finiteModelDigest}" ++
    " }).toJson.pretty 100)\n"
  IO.FS.writeFile tmp source
  let out ← IO.Process.output { cmd := "lake", args := #["env", "lean", tmp.toString] }
  if out.exitCode == 0 then
    pure out.stdout
  else
    throw <| IO.userError s!"failed to evaluate manifest for {modelString}:\n{out.stderr}"

unsafe def main (args : List String) : IO UInt32 := do
  let some moduleString := parseFlagValue "--module" args
    | IO.eprintln usageExport; return 2
  let some outString := parseFlagValue "--out" args
    | IO.eprintln usageExport; return 2
  let moduleName := parseModuleName moduleString
  let outDir : System.FilePath := outString
  ensureDir outDir
  let path := moduleSourcePath moduleName
  if !(← path.pathExists) then
    IO.eprintln s!"cannot find source file for module {moduleName}: expected {path}"
    return 1
  let content ← IO.FS.readFile path
  let markers := sourceExportMarkers content
  let models := if markers.isEmpty then sourceModelNames content else markers
  if models.isEmpty then
    IO.eprintln s!"no certificate manifests found in module {moduleName}"
    return 1
  let gitCommit ← currentGitCommit
  let gitTag ← currentGitTag
  for modelString in models do
    let (sourceDigest, finiteModelDigest) ← modelDigestsViaLean moduleString modelString
    let json ← evalManifestJsonViaLean moduleString modelString gitCommit gitTag
      sourceDigest finiteModelDigest
    let file := outDir / s!"{modelString}.certificate.json"
    IO.FS.writeFile file json
    IO.println s!"wrote {file}"
  return 0

end LeanUfo.ExportCertificates

unsafe def main (args : List String) : IO UInt32 :=
  LeanUfo.ExportCertificates.main args
