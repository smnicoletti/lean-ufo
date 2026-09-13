import Lean
import LeanUfo.CertificateCli
import LeanUfo.CertificateValidation

open Lean
open LeanUfo.CertificateCli
open LeanUfo.CertificateValidation

namespace LeanUfo.ValidateCertificate

def hasFlag (flag : String) : List String → Bool
  | [] => false
  | List.cons x xs => x == flag || hasFlag flag xs

def positionalArgs : List String → List String
  | [] => []
  | List.cons "--structure-only" xs => positionalArgs xs
  | List.cons "--module" (List.cons _ xs) => positionalArgs xs
  | List.cons x xs => List.cons x (positionalArgs xs)

def getString (json : Json) (field : String) : Except String String :=
  requireString json field

private def compareDigest (label manifestValue rebuiltValue : String) : Except String Unit := do
  if manifestValue == rebuiltValue then
    pure ()
  else
    throw s!"{label} mismatch: manifest has `{manifestValue}`, rebuilt module has `{rebuiltValue}`"

unsafe def recheckWithModule (json : Json) (moduleString : String) : IO (Except String Unit) := do
  let modelName ←
    match getString json "model" with
    | .ok value => pure value
    | .error err => return .error err
  let finals ←
    match json.getObjVal? "finalTheorems" with
    | .ok value => pure value
    | .error err => return .error err
  let certifiedName ←
    match requireString finals "certified" with
    | .ok value => pure value
    | .error err => return .error err
  let certifiedModelName ←
    match requireString finals "certifiedModel" with
    | .ok value => pure value
    | .error err => return .error err
  let rows ←
    match validateCertificateRows json with
    | .ok value => pure value
    | .error err => return .error err
  -- Parse and render every executable name before any build or Lean subprocess.
  -- The original theorem strings remain data for exact manifest comparisons.
  let sources ← try
      let mut rowChecks := ""
      for row in rows do
        let theoremSource ← identifierSource row.theoremName
        let checkedSource ← identifierSource row.checkedTheoremName
        rowChecks := rowChecks ++ s!"#check {theoremSource}\n#check {checkedSource}\n"
        if let some reusedFrom := row.reusedFrom then
          rowChecks := rowChecks ++ s!"#check {← identifierSource reusedFrom}\n"
      pure <| Except.ok (← identifierSource moduleString, ← identifierSource modelName,
        ← identifierSource certifiedName, ← identifierSource certifiedModelName, rowChecks)
    catch e => pure <| Except.error s!"invalid certificate declaration name: {e.toString}"
  let (moduleSource, modelSource, certifiedSource, certifiedModelSource, rowChecks) ←
    match sources with
    | .ok names => pure names
    | .error err => return .error err
  let build ← IO.Process.output { cmd := "lake", args := #["build", moduleString] }
  if build.exitCode != 0 then
    return .error s!"lake build {moduleString} failed:\n{build.stderr}"
  let sourceHash ←
    match getString json "sourceHash" with
    | .ok value => pure value
    | .error err => return .error err
  let finiteModelHash ←
    match getString json "finiteModelHash" with
    | .ok value => pure value
    | .error err => return .error err
  let sourceDigest ←
    match requireSha256Digest json "sourceDigest" with
    | .ok value => pure value
    | .error err => return .error err
  let finiteModelDigest ←
    match requireSha256Digest json "finiteModelDigest" with
    | .ok value => pure value
    | .error err => return .error err
  let axiomPackage ←
    match getString json "ufoAxiomPackage" with
    | .ok value => pure value
    | .error err => return .error err
  let rebuiltDigests ←
    try
      let (rebuiltSourceDigest, rebuiltFiniteModelDigest) ← modelDigestsViaLean moduleString modelName
      pure <| Except.ok (rebuiltSourceDigest, rebuiltFiniteModelDigest)
    catch e =>
      pure <| Except.error s!"could not recompute SHA-256 digests: {e.toString}"
  let (rebuiltSourceDigest, rebuiltFiniteModelDigest) ←
    match rebuiltDigests with
    | .ok values => pure values
    | .error err => return .error err
  match compareDigest "sourceDigest" sourceDigest rebuiltSourceDigest with
  | .ok _ => pure ()
  | .error err => return .error err
  match compareDigest "finiteModelDigest" finiteModelDigest rebuiltFiniteModelDigest with
  | .ok _ => pure ()
  | .error err => return .error err
  let moduleName ← parseLeanName moduleString
  let modelNameParsed ← parseLeanName modelName
  let env ← loadModule moduleName
  let some rebuiltManifest ← manifestByModel? env modelNameParsed
    | return .error s!"rebuilt module has no certificate manifest for `{modelName}`"
  match compareRebuiltManifest json rebuiltManifest with
  | .ok _ => pure ()
  | .error err => return .error err
  -- The rebuilt manifest fixes the expected row contents; these checks then
  -- confirm that each referenced proof declaration exists in the module.
  let script :=
    s!"import {moduleSource}\n" ++
    s!"#check ({certifiedSource} : UFOAxioms4 {modelSource}.sig)\n" ++
    s!"#check ({certifiedModelSource} : LeanUfo.UFO.DSL.FiniteModel4.Certified {modelSource}.data)\n" ++
    s!"example : {modelSource}.certificateManifest.sourceHash = {reprStr sourceHash} := by native_decide\n" ++
    s!"example : {modelSource}.certificateManifest.finiteModelHash = {reprStr finiteModelHash} := by native_decide\n" ++
    s!"example : {modelSource}.certificateManifest.certifiedTheorem = {reprStr certifiedName} := by native_decide\n" ++
    s!"example : {modelSource}.certificateManifest.certifiedModelTheorem = {reprStr certifiedModelName} := by native_decide\n" ++
    s!"example : {modelSource}.certificateManifest.axiomPackage = {reprStr axiomPackage} := by native_decide\n" ++
    rowChecks
  let out ← runLeanScript script
  if out.exitCode == 0 then
    return .ok ()
  else
    return .error s!"Lean recheck script failed:\n{out.stdout}\n{out.stderr}"

def main (args : List String) : IO UInt32 := do
  match positionalArgs args with
  | [pathString] =>
      let content ← IO.FS.readFile pathString
      match Json.parse content with
      | .error err =>
          IO.eprintln s!"invalid JSON: {err}"
          return 1
      | .ok json =>
          match validateJson json with
          | .ok _ =>
              if hasFlag "--structure-only" args then
                IO.println s!"valid certificate manifest structure: {pathString}"
                IO.println "proof not rechecked because `--structure-only` was requested"
                return 0
              else
                match parseFlagValue "--module" args with
                | none =>
                    IO.eprintln "validation rechecks Lean proof declarations by default; pass `--module Module.Name` or use `--structure-only` for JSON-only validation"
                    return 2
                | some moduleString =>
                    match (← unsafe recheckWithModule json moduleString) with
                    | .ok _ =>
                        IO.println s!"valid certificate manifest and Lean proof recheck: {pathString}"
                        return 0
                    | .error err =>
                        IO.eprintln s!"certificate recheck failed: {err}"
                        return 1
          | .error err =>
              IO.eprintln s!"invalid certificate manifest: {err}"
              return 1
  | _ =>
      IO.eprintln usageValidate
      return 2

end LeanUfo.ValidateCertificate

def main (args : List String) : IO UInt32 :=
  LeanUfo.ValidateCertificate.main args
