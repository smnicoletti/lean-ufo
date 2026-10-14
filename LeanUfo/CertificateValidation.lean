import LeanUfo.UFO.DSL.Certificate.Generation

/-!
# Certificate manifest validation

This module owns the pure validation rules for exported certificate manifests.
It checks every per-axiom row against the fixed certificate registry and can
compare the exported provenance with the manifest rebuilt from a Lean module.
The command-line wrapper performs the filesystem and Lean-process work.
-/

open Lean

namespace LeanUfo.CertificateValidation

open LeanUfo.UFO.DSL

structure CertificateRow where
  field : String
  status : CertificateReuseStatus
  theoremName : String
  checkedTheoremName : String
  reusedFrom : Option String
  deriving Repr, Inhabited

def requireString (json : Json) (field : String) : Except String String := do
  let value ← json.getObjVal? field
  let text ← value.getStr?
  if text.isEmpty then
    throw s!"field `{field}` is empty"
  pure text

def requireOptionalString (json : Json) (field : String) : Except String (Option String) := do
  match ← json.getObjVal? field with
  | .null => pure none
  | value =>
      let text ← value.getStr?
      if text.isEmpty then
        throw s!"field `{field}` is empty"
      pure (some text)

def requireNonPlaceholderVersion (version : String) : Except String Unit := do
  if version == "unreleased" then
    throw "field `artifactVersion` still uses the old `unreleased` placeholder"
  else
    pure ()

def requireSha256Digest (json : Json) (field : String) : Except String String := do
  let value ← requireString json field
  let hexadecimal := value.toList.drop "sha256:".length
  if value.startsWith "sha256:" && hexadecimal.length == 64 &&
      hexadecimal.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) then
    pure value
  else
    throw s!"field `{field}` is not a SHA-256 digest"

def requireObject (field : String) (value : Json) : Except String Unit := do
  match value with
  | .obj _ => pure ()
  | _ => throw s!"field `{field}` is not an object"

def parseReuseStatus (value : String) : Except String CertificateReuseStatus :=
  match value with
  | "fresh" => pure .fresh
  | "reused" => pure .reused
  | "notReusable" => pure .notReusable
  | _ => throw s!"unknown certificate status `{value}`"

def parseCertificateRow (json : Json) : Except String CertificateRow := do
  requireObject "certificate entry" json
  let field ← requireString json "field"
  let status ← parseReuseStatus (← requireString json "status")
  let theoremName ← requireString json "leanTheorem"
  let checkedTheoremName ← requireString json "checkTheorem"
  let reusedFrom ← requireOptionalString json "reusedFrom"
  match status, reusedFrom with
  | .reused, none => throw s!"certificate `{field}` is reused but has no `reusedFrom` theorem"
  | .fresh, some _ => throw s!"certificate `{field}` is fresh but has a `reusedFrom` theorem"
  | .notReusable, some _ =>
      throw s!"certificate `{field}` is not reusable but has a `reusedFrom` theorem"
  | _, _ => pure { field, status, theoremName, checkedTheoremName, reusedFrom }

def certificateRows (json : Json) : Except String (Array CertificateRow) := do
  let value ← json.getObjVal? "certificates"
  let entries ← value.getArr?
  if entries.isEmpty then
    throw "field `certificates` is an empty array"
  entries.mapM parseCertificateRow

private def expectedFieldNames : Array String :=
  certFields.map CertField.field

/--
Check that the manifest has exactly one well-formed row for every field in the
fixed certificate registry. Row order is not significant, but the registry
itself determines completeness; a duplicate therefore cannot hide a missing
field.
-/
def validateCertificateRows (json : Json) : Except String (Array CertificateRow) := do
  let rows ← certificateRows json
  let expected := expectedFieldNames
  if rows.size != expected.size then
    throw s!"field `certificates` has {rows.size} entries; expected {expected.size}"
  let mut seen : Array String := #[]
  for row in rows do
    unless expected.contains row.field do
      throw s!"certificate entry has unknown field `{row.field}`"
    if seen.contains row.field then
      throw s!"certificate entry for `{row.field}` is duplicated"
    seen := seen.push row.field
  for field in expected do
    unless seen.contains field do
      throw s!"certificate entry for `{field}` is missing"
  pure rows

def validateJson (json : Json) : Except String Unit := do
  discard <| requireString json "model"
  discard <| requireString json "artifact"
  let artifactVersion ← requireString json "artifactVersion"
  requireNonPlaceholderVersion artifactVersion
  discard <| requireString json "leanVersion"
  discard <| requireOptionalString json "gitCommit"
  discard <| requireOptionalString json "gitTag"
  discard <| requireString json "ufoAxiomPackage"
  discard <| requireString json "sourceFingerprint"
  discard <| requireString json "finiteModelFingerprint"
  discard <| requireSha256Digest json "sourceDigest"
  discard <| requireSha256Digest json "finiteModelDigest"
  discard <| requireString json "sourceHash"
  discard <| requireString json "finiteModelHash"
  let checker ← json.getObjVal? "checker"
  requireObject "checker" checker
  discard <| requireString checker "name"
  discard <| requireString checker "version"
  discard <| validateCertificateRows json
  let finals ← json.getObjVal? "finalTheorems"
  requireObject "finalTheorems" finals
  discard <| requireString finals "certified"
  discard <| requireString finals "certifiedModel"

private def compareField (label expected actual : String) : Except String Unit := do
  if expected == actual then
    pure ()
  else
    throw s!"{label} mismatch: manifest has `{actual}`, rebuilt module has `{expected}`"

private def compareOptionalField
    (label : String) (expected actual : Option String) : Except String Unit := do
  if expected == actual then
    pure ()
  else
    throw s!"{label} mismatch between manifest and rebuilt module"

/--
Compare all provenance generated by the DSL with the manifest evaluated from
the rebuilt module. The command-line wrapper recomputes the SHA-256 digests.
Git commit and tag strings record the export context; validation checks their
JSON types but does not authenticate that historical context.
-/
def compareRebuiltManifest (json : Json) (rebuilt : CertificateManifest) : Except String Unit := do
  compareField "model" rebuilt.modelName (← requireString json "model")
  compareField "artifact" rebuilt.artifact (← requireString json "artifact")
  compareField "artifactVersion" rebuilt.artifactVersion (← requireString json "artifactVersion")
  compareField "leanVersion" rebuilt.leanVersion (← requireString json "leanVersion")
  compareField "ufoAxiomPackage" rebuilt.axiomPackage (← requireString json "ufoAxiomPackage")
  compareField "sourceFingerprint" rebuilt.sourceFingerprint
    (← requireString json "sourceFingerprint")
  compareField "finiteModelFingerprint" rebuilt.finiteModelFingerprint
    (← requireString json "finiteModelFingerprint")
  compareField "sourceHash" rebuilt.sourceHash (← requireString json "sourceHash")
  compareField "finiteModelHash" rebuilt.finiteModelHash (← requireString json "finiteModelHash")
  let checker ← json.getObjVal? "checker"
  compareField "checker.name" rebuilt.checkerName (← requireString checker "name")
  compareField "checker.version" rebuilt.checkerVersion (← requireString checker "version")
  let finals ← json.getObjVal? "finalTheorems"
  compareField "finalTheorems.certified" rebuilt.certifiedTheorem
    (← requireString finals "certified")
  compareField "finalTheorems.certifiedModel" rebuilt.certifiedModelTheorem
    (← requireString finals "certifiedModel")
  let rows ← validateCertificateRows json
  discard <| validateCertificateRows rebuilt.toJson
  for expected in rebuilt.fields do
    let some actual := rows.find? (fun row => row.field == expected.field)
      | throw s!"certificate entry for `{expected.field}` is missing"
    compareField s!"certificate `{expected.field}` status" expected.status.toString
      actual.status.toString
    compareField s!"certificate `{expected.field}` Lean theorem" expected.theoremName
      actual.theoremName
    compareField s!"certificate `{expected.field}` check theorem" expected.checkedTheoremName
      actual.checkedTheoremName
    compareOptionalField s!"certificate `{expected.field}` reuse source" expected.reusedFrom
      actual.reusedFrom

end LeanUfo.CertificateValidation
