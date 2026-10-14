import Lean

/-!
Package the current public source without Git history, local instructions,
build caches, or experiment working directories. Preserve reference evidence
and dependency sources explicitly. A per-file Git-blob manifest identifies
the snapshot even before the release commit is made.
-/

open Lean System

-- Keep the development documentation in the checkout. The archive contains
-- only reviewer guides and documentation that the tests/report generator use.
def includeInArtifact (name : String) : Bool :=
  if name.startsWith "docs/" then
    #["docs/README.md", "docs/artifact.md", "docs/experiments.md",
      "docs/dsl/quickstart.md"].contains name || name.startsWith "docs/experiment-tables/"
  else if name.startsWith "artifact/" then
    #["artifact/run.sh", "artifact/dependency-sources.tar.gz",
      "artifact/dependency-sources.README.md", "artifact/reference-results.tar.gz",
      "artifact/THIRD-PARTY.md"].contains name
  else !name.startsWith ".github/" && !name.startsWith "scripts/" && name != "CONTRIBUTING.md"

def sourcePath (name : String) : String :=
  if name == "README.md" then "artifact/REVIEWER-README.md"
  else if name == "docs/README.md" then "artifact/DOCS-README.md"
  else if name == "CITATION.cff" then "artifact/CITATION.cff"
  else name

def capture (cmd : String) (args : Array String) : IO String := do
  let result ← IO.Process.output { cmd, args }
  unless result.exitCode == 0 do throw <| IO.userError (result.stdout ++ result.stderr)
  return result.stdout.trimAscii.toString

def main (args : List String) : IO Unit := do
  let [destination] := args
    | throw <| IO.userError "usage: lake env lean --run artifact/PrepareSource.lean OUTPUT_DIRECTORY"
  let output := FilePath.mk destination
  if ← (output / "alien-source.tar.gz").pathExists then
    throw <| IO.userError "source archive already exists; choose a new output directory"
  let listed ← capture "git" #["ls-files", "--cached", "--others", "--exclude-standard"]
  let files := listed.splitOn "\n" |>.toArray
  let files := files ++ #["CITATION.cff", "artifact/dependency-sources.tar.gz", "artifact/reference-results.tar.gz"]
  let files := (files.filter includeInArtifact).toList.eraseDups.toArray.qsort (· < ·)
  for name in files do
    if name.isEmpty || name.startsWith "/" || (name.splitOn "/").contains ".." ||
        name == "AGENTS.md" || name == "docs/dsl/behavior-contract.md" ||
        #[".git/", ".lake/", ".codex/", ".agents/", "experiments/", "artifact/images/",
          "artifact/packages/", "artifact/validation/"].any (fun excludedRoot => name.startsWith excludedRoot) then
      throw <| IO.userError s!"excluded or unsafe source path: {name}"
    unless ← (FilePath.mk (sourcePath name)).pathExists do
      throw <| IO.userError s!"source path does not exist: {name}"
  let hashes ← capture "git" (#["hash-object", "--"] ++ files.map sourcePath)
  let hashes := hashes.splitOn "\n" |>.toArray
  unless hashes.size == files.size do throw <| IO.userError "incomplete source manifest"
  let manifest := Json.mkObj <| (files.toList.zip hashes.toList).map fun (name, hash) => (name, toJson hash)
  IO.FS.createDirAll output
  IO.FS.withTempDir fun temporary => do
    let root := temporary / "alien-source"
    for name in files do
      let target := root / name
      if let some parent := target.parent then IO.FS.createDirAll parent
      IO.FS.writeBinFile target (← IO.FS.readBinFile (sourcePath name))
    -- Executable permission is needed by the source build's container entrypoint.
    discard <| capture "chmod" #["+x", (root / "artifact/run.sh").toString]
    IO.FS.writeFile (root / "SOURCE-MANIFEST.json") manifest.pretty
    discard <| capture "tar" #["-czf", (output / "alien-source.tar.gz").toString,
      "-C", temporary.toString, "alien-source"]
  IO.FS.writeFile (output / "SOURCE-MANIFEST.json") manifest.pretty
  IO.FS.writeFile (output / "README.md") (← IO.FS.readFile "artifact/REVIEWER-README.md")
  IO.FS.writeFile (output / "CITATION.cff") (← IO.FS.readFile "artifact/CITATION.cff")
  let provenance := Json.mkObj [
    ("base_commit", toJson (← capture "git" #["rev-parse", "HEAD"])),
    ("source_files", toJson files.size),
    ("hash_format", toJson "Git blob object IDs; archive SHA-256 recorded separately")]
  IO.FS.writeFile (output / "SOURCE-PROVENANCE.json") provenance.pretty
  IO.println s!"Packaged {files.size} public source files in {output}"
