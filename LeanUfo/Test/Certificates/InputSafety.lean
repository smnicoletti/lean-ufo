import LeanUfo.CertificateCli

/-!
# Certificate identifier boundary tests

The CLI treats JSON names as identifiers, not Lean expressions or commands.
These tests cover the shared parser, direct digest callers, final theorem
names, per-field theorem names, and reuse sources. Marker files detect execution
even if a later digest or type check rejects the manifest. Each test owns a
fresh temporary directory.
-/

namespace LeanUfo.Test.Certificates

open Lean LeanUfo.CertificateCli

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def requireIdentifierRejection (action : IO α) : IO Unit := do
  let rejected ← try
      discard action
      pure false
    catch e => pure (e.toString.contains "expected one complete Lean identifier")
  require rejected "invalid identifier did not fail at the name boundary"

def checkIdentifierParsing : IO Unit := do
  for source in #["A.B", "α.β'", "«if»", "«a.b»", "«space here»", "«_»",
      "«#eval IO.println 1\n#check Nat»", "«?m»", "«a--b»", "«a/-b-/»"] do
    let name ← parseLeanName source
    let rendered ← identifierSource source
    require ((← parseLeanName rendered) == name) s!"identifier changed: {source}"
    require (rendered.startsWith "«") s!"identifier was not escaped: {source}"
  require ((← parseLeanName "A.B") != (← parseLeanName "«A.B»"))
    "qualification was confused with an escaped dot"
  for source in #["", " A", "A ", "A\n", "A -- comment", "A/-comment-/",
      "A\n#eval 1", "(A)", "A + B", "A.", "«unterminated", "#eval 1"] do
    requireIdentifierRejection (identifierSource source)
  require (match leanNameSource (.num .anonymous 1) with | .error _ => true | .ok _ => false)
    "numeric name component was accepted"
  require (match leanNameSource (.str .anonymous "a»b") with | .error _ => true | .ok _ => false)
    "unrepresentable name component was accepted"

def checkManifestNameSafety (baseline : Json) (moduleName : String) : IO Unit :=
  IO.FS.withTempDir fun dir => do
    let marker := dir / "executed.txt"
    let command := s!"\n#eval IO.FS.writeFile {reprStr marker.toString} \"executed\"\n--"
    let finals := baseline.getObjValD "finalTheorems"
    let certificates ←
      match baseline.getObjValD "certificates" |>.getArr? with
      | .ok value => pure value
      | .error error => throw <| IO.userError error
    let firstCertificate := certificates[0]!
    let replaceFirstCertificate (row : Json) : Json :=
      baseline.setObjVal! "certificates" (.arr (certificates.set! 0 row))
    let variants := #[
      baseline.setObjVal! "model" (.str ("CarBase.source)" ++ command)),
      baseline.setObjVal! "finalTheorems"
        (finals.setObjVal! "certified" (.str ("CarBase.certified)" ++ command))),
      baseline.setObjVal! "finalTheorems"
        (finals.setObjVal! "certifiedModel" (.str ("CarBase.certifiedModel)" ++ command))),
      replaceFirstCertificate
        (firstCertificate.setObjVal! "leanTheorem" (.str ("CarBase.certified_ax1)" ++ command))),
      replaceFirstCertificate
        (firstCertificate.setObjVal! "checkTheorem" (.str ("CarBase.checked_ax1)" ++ command))),
      replaceFirstCertificate
        (firstCertificate.setObjVal! "status" (.str "reused") |>.setObjVal! "reusedFrom"
          (.str ("CarBase.checked_ax1)" ++ command))),
      baseline.setObjVal! "model" (.str "(CarBase)"),
      baseline.setObjVal! "model" (.str "CarBase -- suffix")]
    for index in [:variants.size] do
      let path := dir / s!"invalid-{index}.json"
      IO.FS.writeFile path variants[index]!.pretty
      let out ← IO.Process.output { cmd := "lake", args := #["exe", "validate-certificate",
        path.toString, "--module", moduleName] }
      require (out.exitCode != 0 && (out.stdout ++ out.stderr).contains
        "invalid certificate declaration name") s!"manifest name {index} bypassed validation"
      require (!(← marker.pathExists)) s!"manifest name {index} executed a command"
    -- Direct helper callers must not depend on validation by the CLI wrapper.
    for action in #[modelSourceTextViaLean moduleName ("CarBase.source)" ++ command),
        finiteModelTextViaLean moduleName ("CarBase.source)" ++ command),
        modelSourceTextViaLean (moduleName ++ command) "CarBase"] do
      requireIdentifierRejection action
      require (!(← marker.pathExists)) "digest helper executed a supplied command"

/-- The actual Lean source parser must preserve escaped names, not only the
identifier parser used by the validation helper. -/
def checkGeneratedNameSource : IO Unit := do
  for source in #["α.β'", "«if»", "«a.b»", "«space here»", "«_»",
      "«#eval IO.println 1\n#check Nat»", "«?m»", "«a--b»", "«a/-b-/»"] do
    let rendered ← identifierSource source
    let out ← runLeanScript s!"def {rendered} : Nat := 7\n#eval IO.println {rendered}\n"
    require (out.exitCode == 0 && out.stdout.trimAscii.toString == "7")
      s!"generated name changed Lean source: {source}\n{out.stdout}\n{out.stderr}"
  let first ← IO.asTask (runLeanScript "#eval IO.println 17\n")
  let second ← IO.asTask (runLeanScript "#eval IO.println 23\n")
  let first ← IO.ofExcept first.get
  let second ← IO.ofExcept second.get
  require (first.exitCode == 0 && first.stdout.trimAscii.toString == "17" &&
    second.exitCode == 0 && second.stdout.trimAscii.toString == "23")
    "concurrent generated scripts interfered"

end LeanUfo.Test.Certificates
