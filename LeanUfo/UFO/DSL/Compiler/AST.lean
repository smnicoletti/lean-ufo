import Lean
import LeanUfo.UFO.DSL.Compiler.Fields

/-!
# Resolved and named DSL AST types

This module contains the pure data structures used between surface parsing,
name resolution, scope expansion, and finite-table compilation.
-/

namespace LeanUfo.UFO.DSL

open Lean

/-- Resolved DSL facts. Names have already been mapped to finite indices. -/
inductive CompiledFact where
  | unary (field : UnaryField) (thing world : Nat)
  | binary (field : BinaryField) (left right world : Nat)
  | ternary (field : TernaryField) (first second third world : Nat)
  | tupleProjection (tuple index result world : Nat)
  | derived (prop : String)
  deriving Repr, Inhabited

/-- Scope attached to a resolved fact before world expansion. -/
inductive FactScope where
  | at (world : Nat)
  | everywhere
  deriving Repr, Inhabited, DecidableEq

/--
Resolved facts before scope expansion.

Derived assertions carry a world-indexed proposition builder because their
generated Lean proposition mentions the concrete `Fin` world term.
-/
inductive ScopedCompiledFact where
  | unary (field : UnaryField) (thing : Nat) (scope : FactScope)
  | binary (field : BinaryField) (left right : Nat) (scope : FactScope)
  | ternary (field : TernaryField) (first second third : Nat) (scope : FactScope)
  | tupleProjection (tuple index result : Nat) (scope : FactScope)
  | derived (propAtWorld : Nat → String) (scope : FactScope)

/-- Scope attached to a named fact before world-name resolution. -/
inductive NamedFactScope where
  | at (world : String)
  | everywhere
  deriving Repr, Inhabited, DecidableEq

/-- Derived relation arities supported by the surface DSL. -/
inductive NamedDerivedFact where
  | unary (field thing : String)
  | binary (field left right : String)
  | ternary (field first second third : String)
  | quaternary (field first second third fourth : String)
  deriving Repr, Inhabited, DecidableEq

/-- Named facts produced by the parser before pure name resolution. -/
inductive NamedScopedFact where
  | unary (field : UnaryField) (thing : String) (scope : NamedFactScope)
  | binary (field : BinaryField) (left right : String) (scope : NamedFactScope)
  | ternary (field : TernaryField) (first second third : String) (scope : NamedFactScope)
  | tupleProjection (tuple : String) (index : Nat) (result : String) (scope : NamedFactScope)
  | derived (fact : NamedDerivedFact) (scope : NamedFactScope)
  deriving Repr, Inhabited, DecidableEq

/-- Named product-family witness for the existential content of ax99. -/
structure NamedProductFamily where
  domain : String
  qualityType : String
  dimensionThings : Array String
  typeThings : Array String
  deriving Repr, Inhabited, DecidableEq

/--
User-facing model source after parsing, before name resolution and finite-table
compilation.

This is the reusable source artifact emitted for each model. Extended models
merge this source with their local additions and then run the ordinary compiler
pipeline, so model extension does not introduce a second compilation path.
-/
structure ModelSource where
  worlds : Array String
  things : Array String
  facts : Array NamedScopedFact := #[]
  productFamilies : Array NamedProductFamily := #[]
  deriveRelations : Bool := true
  deriving Repr, Inhabited, DecidableEq

/-- Resolved product-family witness. The witness applies in every model world. -/
structure ProductFamilySpec where
  domain : Nat
  qualityType : Nat
  dimensionThings : Array Nat
  typeThings : Array Nat
  deriving Repr, Inhabited, DecidableEq

/-- Errors that can arise during pure name resolution. -/
inductive ResolveError where
  | duplicateWorld (name : String)
  | duplicateThing (name : String)
  | unknownWorld (name : String)
  | unknownThing (name : String)
  | extensionAddsWorlds
  | extensionDisablesDerivations
  | productFamilyArityMismatch
      (domain qualityType : String) (dimensionCount typeCount : Nat)
  deriving Repr, Inhabited, DecidableEq

/-- Whether a generated per-axiom check was evaluated fresh or reused. -/
inductive CertificateReuseStatus where
  | fresh
  | reused
  | notReusable
  deriving Repr, Inhabited, DecidableEq

def CertificateReuseStatus.toString : CertificateReuseStatus → String
  | .fresh => "fresh"
  | .reused => "reused"
  | .notReusable => "notReusable"

/-- Manifest row for one generated certificate field. -/
structure CertificateFieldManifest where
  field : String
  status : CertificateReuseStatus
  theoremName : String
  checkedTheoremName : String
  reusedFrom : Option String := none
  deriving Repr, Inhabited

/--
Structured provenance for a certified DSL model.

The manifest is an audit/export layer, not proof evidence. The proof evidence
remains the generated Lean declarations such as `Model.certified_axN` and
`Model.certified`.
-/
structure CertificateManifest where
  modelName : String
  artifact : String
  artifactVersion : String
  leanVersion : String
  gitCommit : Option String := none
  gitTag : Option String := none
  axiomPackage : String
  checkerName : String
  checkerVersion : String
  sourceFingerprint : String
  finiteModelFingerprint : String
  sourceDigest : Option String := none
  finiteModelDigest : Option String := none
  sourceHash : String
  finiteModelHash : String
  fields : Array CertificateFieldManifest
  certifiedTheorem : String
  certifiedModelTheorem : String
  deriving Repr, Inhabited

def CertificateFieldManifest.toJson (field : CertificateFieldManifest) : Json :=
  Json.mkObj [
    ("field", Json.str field.field),
    ("status", Json.str field.status.toString),
    ("leanTheorem", Json.str field.theoremName),
    ("checkTheorem", Json.str field.checkedTheoremName),
    ("reusedFrom", match field.reusedFrom with
      | none => Json.null
      | some theoremName => Json.str theoremName)
  ]

def CertificateManifest.toJson (manifest : CertificateManifest) : Json :=
  Json.mkObj [
    ("model", Json.str manifest.modelName),
    ("artifact", Json.str manifest.artifact),
    ("artifactVersion", Json.str manifest.artifactVersion),
    ("leanVersion", Json.str manifest.leanVersion),
    ("gitCommit", match manifest.gitCommit with
      | none => Json.null
      | some commit => Json.str commit),
    ("gitTag", match manifest.gitTag with
      | none => Json.null
      | some tag => Json.str tag),
    ("ufoAxiomPackage", Json.str manifest.axiomPackage),
    ("sourceFingerprint", Json.str manifest.sourceFingerprint),
    ("finiteModelFingerprint", Json.str manifest.finiteModelFingerprint),
    ("sourceDigest", match manifest.sourceDigest with
      | none => Json.null
      | some digest => Json.str digest),
    ("finiteModelDigest", match manifest.finiteModelDigest with
      | none => Json.null
      | some digest => Json.str digest),
    ("sourceHash", Json.str manifest.sourceHash),
    ("finiteModelHash", Json.str manifest.finiteModelHash),
    ("checker", Json.mkObj [
      ("name", Json.str manifest.checkerName),
      ("version", Json.str manifest.checkerVersion)
    ]),
    ("certificates", Json.arr (manifest.fields.map CertificateFieldManifest.toJson)),
    ("finalTheorems", Json.mkObj [
      ("certified", Json.str manifest.certifiedTheorem),
      ("certifiedModel", Json.str manifest.certifiedModelTheorem)
    ])
  ]

end LeanUfo.UFO.DSL
