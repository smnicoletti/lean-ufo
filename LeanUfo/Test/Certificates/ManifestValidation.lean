import LeanUfo.CertificateValidation

/-!
# Certificate manifest completeness tests

These tests exercise the pure validation boundary. A valid manifest has one
row for each registered certificate field. Missing, malformed, duplicate, and
altered rows must fail before a module recheck can trust their provenance.
-/

namespace LeanUfo.Test.Certificates

open Lean LeanUfo.CertificateValidation LeanUfo.UFO.DSL

private def digest : String :=
  "sha256:0000000000000000000000000000000000000000000000000000000000000000"

private def baselineManifest : CertificateManifest :=
  { modelName := "TestModel"
    artifact := "lean-ufo-certificate"
    artifactVersion := "v1"
    leanVersion := Lean.versionString
    axiomPackage := "UFO"
    checkerName := "test-checker"
    checkerVersion := "1"
    sourceFingerprint := "worlds=1;things=1;facts=0;productFamilies=0"
    finiteModelFingerprint := "worlds=1;things=1;derived=0;productFamilies=0"
    sourceDigest := some digest
    finiteModelDigest := some digest
    sourceHash := "source-hash"
    finiteModelHash := "model-hash"
    fields := certFields.map fun field =>
      { field := field.field
        status := .fresh
        theoremName := s!"TestModel.{certTheoremName field.field}"
        checkedTheoremName := s!"TestModel.{checkedTheoremName field.field}" }
    certifiedTheorem := "TestModel.certified"
    certifiedModelTheorem := "TestModel.certifiedModel" }

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def requireErrorContains
    (result : Except String α) (needle message : String) : IO Unit :=
  match result with
  | .error error => require (error.contains needle) s!"{message}: {error}"
  | .ok _ => throw <| IO.userError message

private def replaceCertificates (json : Json) (rows : Array Json) : Json :=
  json.setObjVal! "certificates" (.arr rows)

def checkManifestCompleteness : IO Unit := do
  let baseline := baselineManifest.toJson
  require (validateJson baseline).isOk "valid complete manifest was rejected"
  require (compareRebuiltManifest baseline baselineManifest).isOk
    "valid manifest did not match its rebuilt provenance"
  let rows ←
    match baseline.getObjValD "certificates" |>.getArr? with
    | .ok value => pure value
    | .error error => throw <| IO.userError error

  let missing := replaceCertificates baseline (rows.extract 0 (rows.size - 1))
  requireErrorContains (validateJson missing) "expected 116"
    "manifest with a missing certificate row was accepted"

  let malformedRow := rows[0]!.setObjVal! "status" (.bool true)
  let malformed := replaceCertificates baseline (rows.set! 0 malformedRow)
  requireErrorContains (validateJson malformed) "String expected"
    "manifest with a malformed certificate row was accepted"

  let duplicate := replaceCertificates baseline (rows.set! (rows.size - 1) rows[0]!)
  requireErrorContains (validateJson duplicate) "duplicated"
    "manifest with a duplicate certificate row was accepted"

  let alteredRow := rows[0]!.setObjVal! "leanTheorem" (.str "TestModel.wrong")
  let altered := replaceCertificates baseline (rows.set! 0 alteredRow)
  requireErrorContains (compareRebuiltManifest altered baselineManifest) "Lean theorem"
    "manifest with altered certificate provenance matched the rebuilt module"

end LeanUfo.Test.Certificates
