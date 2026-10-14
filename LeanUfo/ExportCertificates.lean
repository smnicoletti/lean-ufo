import Lean
import LeanUfo.CertificateCli

open Lean
open LeanUfo.CertificateCli

namespace LeanUfo.ExportCertificates

unsafe def main (args : List String) : IO UInt32 := do
  let some moduleString := parseFlagValue "--module" args
    | IO.eprintln usageExport; return 2
  let some outString := parseFlagValue "--out" args
    | IO.eprintln usageExport; return 2
  let moduleName ← parseLeanName moduleString
  let outDir : System.FilePath := outString
  ensureDir outDir
  let env ← loadModule moduleName
  let manifests := selectModuleManifests (← moduleManifests env moduleName)
  if manifests.isEmpty then
    IO.eprintln s!"no certificate manifests found in module {moduleName}"
    return 1
  let gitCommit ← currentGitCommit
  let gitTag ← currentGitTag
  for (modelName, manifest, _requested) in manifests do
    let modelString := modelName.toString
    let (sourceDigest, finiteModelDigest) ← modelDigestsViaLean moduleString modelString
    let exported := addExportMetadata manifest gitCommit gitTag
      (some sourceDigest) (some finiteModelDigest)
    let file := outDir / manifestFileName exported
    IO.FS.writeFile file (exported.toJson.pretty 100 ++ "\n")
    IO.println s!"wrote {file}"
  return 0

end LeanUfo.ExportCertificates

unsafe def main (args : List String) : IO UInt32 :=
  LeanUfo.ExportCertificates.main args
