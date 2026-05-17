import Lean
import LeanUfo.CertificateCli

open Lean
open LeanUfo.CertificateCli

namespace LeanUfo.ValidateCertificate

def hasFlag (flag : String) : List String → Bool
  | [] => false
  | x :: xs => x == flag || hasFlag flag xs

def positionalArgs : List String → List String
  | [] => []
  | "--structure-only" :: xs => positionalArgs xs
  | "--module" :: _ :: xs => positionalArgs xs
  | x :: xs => x :: positionalArgs xs

def requireString (json : Json) (field : String) : Except String String := do
  let value ← json.getObjVal? field
  let text ← value.getStr?
  if text.isEmpty then
    throw s!"field `{field}` is empty"
  pure text

def requireNonPlaceholderVersion (version : String) : Except String Unit := do
  if version == "unreleased" then
    throw "field `artifactVersion` still uses the old `unreleased` placeholder"
  else
    pure ()

def requireSha256Digest (_json : Json) (field : String) : Except String String := do
  let value ← requireString _json field
  if value.startsWith "sha256:" && value.length == "sha256:".length + 64 then
    pure value
  else
    throw s!"field `{field}` is not a SHA-256 digest"

def requireObject (_json : Json) (field : String) (value : Json) : Except String Unit := do
  match value with
  | .obj _ => pure ()
  | _ => throw s!"field `{field}` is not an object"

def requireArray (_json : Json) (field : String) (value : Json) : Except String Unit := do
  match value with
  | .arr xs =>
      if xs.isEmpty then
        throw s!"field `{field}` is an empty array"
      else
        pure ()
  | _ => throw s!"field `{field}` is not an array"

def validateJson (json : Json) : Except String Unit := do
  discard <| requireString json "model"
  discard <| requireString json "artifact"
  let artifactVersion ← requireString json "artifactVersion"
  requireNonPlaceholderVersion artifactVersion
  discard <| requireString json "leanVersion"
  discard <| requireString json "ufoAxiomPackage"
  discard <| requireSha256Digest json "sourceDigest"
  discard <| requireSha256Digest json "finiteModelDigest"
  discard <| requireString json "sourceHash"
  discard <| requireString json "finiteModelHash"
  let checker ← json.getObjVal? "checker"
  requireObject json "checker" checker
  discard <| requireString checker "name"
  discard <| requireString checker "version"
  let certs ← json.getObjVal? "certificates"
  requireArray json "certificates" certs
  let finals ← json.getObjVal? "finalTheorems"
  requireObject json "finalTheorems" finals
  discard <| requireString finals "certified"
  discard <| requireString finals "certifiedModel"

def getString (json : Json) (field : String) : Except String String :=
  requireString json field

def declarationExists (env : Environment) (declName : Name) : Bool :=
  env.find? declName |>.isSome

def compareField (label expected actual : String) : Except String Unit := do
  if expected == actual then
    pure ()
  else
    throw s!"{label} mismatch: manifest has `{expected}`, rebuilt module has `{actual}`"

unsafe def recheckWithModule (json : Json) (moduleString : String) : IO (Except String Unit) := do
  let modelName ←
    match getString json "model" with
    | .ok value => pure value
    | .error err => return .error err
  let build ← IO.Process.output { cmd := "lake", args := #["build", moduleString] }
  if build.exitCode != 0 then
    return .error s!"lake build {moduleString} failed:\n{build.stderr}"
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
  match compareField "sourceDigest" sourceDigest rebuiltSourceDigest with
  | .ok _ => pure ()
  | .error err => return .error err
  match compareField "finiteModelDigest" finiteModelDigest rebuiltFiniteModelDigest with
  | .ok _ => pure ()
  | .error err => return .error err
  let tmp ← tempFilePath s!"recheck-{moduleString}-{modelName}" "lean"
  let script :=
    s!"import {moduleString}\n" ++
    s!"#check ({certifiedName} : UFOAxioms4 {modelName}.sig)\n" ++
    s!"#check ({certifiedModelName} : LeanUfo.UFO.DSL.FiniteModel4.Certified {modelName}.data)\n" ++
    s!"example : {modelName}.certificateManifest.sourceHash = {reprStr sourceHash} := by native_decide\n" ++
    s!"example : {modelName}.certificateManifest.finiteModelHash = {reprStr finiteModelHash} := by native_decide\n" ++
    s!"example : {modelName}.certificateManifest.certifiedTheorem = {reprStr certifiedName} := by native_decide\n" ++
    s!"example : {modelName}.certificateManifest.certifiedModelTheorem = {reprStr certifiedModelName} := by native_decide\n" ++
    s!"example : {modelName}.certificateManifest.axiomPackage = {reprStr axiomPackage} := by native_decide\n"
  IO.FS.writeFile tmp script
  let out ← IO.Process.output { cmd := "lake", args := #["env", "lean", tmp.toString] }
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
