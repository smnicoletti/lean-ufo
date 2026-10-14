import Lean

/-!
Prepare source-only dependency snapshots for an offline-friendly Docker build.
Every local package must be clean and at the manifest revision. Fresh shallow
clones retain Git revision information without copying local configuration,
credentials, hooks, compiled binaries, or unrelated repository history.
This is a maintainer command; reviewers use the prebuilt artifact image.
-/

open Lean System

def command (cmd : String) (args : Array String) : IO String := do
  let out ← IO.Process.output { cmd, args }
  unless out.exitCode == 0 do throw <| IO.userError (out.stdout ++ out.stderr)
  return out.stdout.trimAscii.toString

def decode (value : Except String α) : IO α :=
  match value with | .ok v => pure v | .error e => throw <| IO.userError e

def main : IO Unit := IO.FS.withTempDir fun temporary => do
  let manifest ← decode <| Json.parse (← IO.FS.readFile "lake-manifest.json")
  let packages ← decode <| manifest.getObjValAs? (Array Json) "packages"
  for package in packages do
    let name ← decode <| package.getObjValAs? String "name"
    let revision ← decode <| package.getObjValAs? String "rev"
    let url ← decode <| package.getObjValAs? String "url"
    let source ← IO.FS.realPath (FilePath.mk ".lake/packages" / name)
    unless (← command "git" #["-C", source.toString, "rev-parse", "HEAD"]) == revision do
      throw <| IO.userError s!"{name}: checkout does not match the manifest"
    unless (← command "git" #["-C", source.toString, "status", "--porcelain"]).isEmpty do
      throw <| IO.userError s!"{name}: dependency contains uncommitted changes"
    IO.println s!"Packing source for {name} at {revision}"
    let destination := temporary / name
    discard <| command "git" #["clone", "--depth", "1", "--no-local",
      "file://" ++ source.toString, destination.toString]
    discard <| command "git" #["-C", destination.toString, "remote", "set-url", "origin", url]
    unless (← command "git" #["-C", destination.toString, "rev-parse", "HEAD"]) == revision do
      throw <| IO.userError s!"{name}: snapshot revision mismatch"
  discard <| command "tar" #["-czf", "artifact/dependency-sources.tar.gz", "-C", temporary.toString, "."]
  IO.println "Prepared artifact/dependency-sources.tar.gz (source only)"
