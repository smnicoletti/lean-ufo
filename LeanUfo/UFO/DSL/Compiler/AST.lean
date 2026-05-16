import Lean
import LeanUfo.UFO.DSL.Compiler.Fields

/-!
# Resolved and named DSL AST types

This module contains the pure data structures used between surface parsing,
name resolution, scope expansion, and finite-table compilation.
-/

namespace LeanUfo.UFO.DSL

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
  deriving Repr, Inhabited

/-- Named facts produced by the parser before pure name resolution. -/
inductive NamedScopedFact where
  | unary (field : UnaryField) (thing : String) (scope : NamedFactScope)
  | binary (field : BinaryField) (left right : String) (scope : NamedFactScope)
  | ternary (field : TernaryField) (first second third : String) (scope : NamedFactScope)
  | tupleProjection (tuple : String) (index : Nat) (result : String) (scope : NamedFactScope)
  | derived (fact : NamedDerivedFact) (scope : NamedFactScope)
  deriving Repr, Inhabited

/-- Named product-family witness for the existential content of ax99. -/
structure NamedProductFamily where
  domain : String
  qualityType : String
  dimensionThings : Array String
  typeThings : Array String
  deriving Repr, Inhabited

/-- Resolved product-family witness. The witness applies in every model world. -/
structure ProductFamilySpec where
  domain : Nat
  qualityType : Nat
  dimensionThings : Array Nat
  typeThings : Array Nat
  deriving Repr, Inhabited

/-- Errors that can arise during pure name resolution. -/
inductive ResolveError where
  | duplicateWorld (name : String)
  | duplicateThing (name : String)
  | unknownWorld (name : String)
  | unknownThing (name : String)
  | productFamilyArityMismatch
      (domain qualityType : String) (dimensionCount typeCount : Nat)
  deriving Repr, Inhabited, DecidableEq


end LeanUfo.UFO.DSL
