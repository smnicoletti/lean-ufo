import LeanUfo.UFO.DSL.Syntax

/-!
# Source names and elaboration snapshots

Restoring Lean's command state must also restore the source used by extensions.
The replay below elaborates two different parents with the same declaration
name, then returns to the first state before declaring the child.
-/

open Lean Elab Command LeanUfo.UFO.DSL

private def elaborateParent (thing : String) : CommandElabM Unit := do
  let source := s!"ufo_model SnapshotParent : UFO where\n  worlds actual\n  things {thing}\n  given actual:\n    AbstractIndividual({thing})\n  derive_relations\n  certify"
  match Parser.runParserCategory (← getEnv) `command source with
  | .ok stx => elabCommand stx
  | .error error => throwError error

elab "restoreModelSnapshot" : command => do
  let before ← get
  elaborateParent "Original"
  let original ← get
  set before
  elaborateParent "Replacement"
  set original

restoreModelSnapshot

ufo_model SnapshotChild : UFO extends SnapshotParent : UFO where
  derive_relations
  certify_fresh

#guard SnapshotParent.source.things == #["Original"]
#guard SnapshotChild.source.things == SnapshotParent.source.things
#check SnapshotChild.certified

-- Qualification, an escaped dot, and whitespace must retain distinct
-- coordinates through derived-fact checking and model extension.
ufo_model QualifiedNames : UFO where
  worlds Season.actual
  things A.B «A.B» «space here»
  given Season.actual:
    AbstractIndividual(A.B)
    AbstractIndividual(«A.B»)
    AbstractIndividual(«space here»)
    SubsetOf(A.B, A.B)
    SubsetOf(«A.B», «A.B»)
    SubsetOf(«space here», «space here»)
  derive_relations
  certify

ufo_model QualifiedChild : UFO extends QualifiedNames : UFO where
  given Season.actual:
    SubsetOf(A.B, «A.B»)
  derive_relations
  certify_fresh

#guard QualifiedChild.source.things == #["A.B", "«A.B»", "«space here»"]
#check QualifiedNames.assertedDerivedFacts
#check QualifiedChild.certified

ufo_model «nested/name» : UFO where
  worlds actual
  things A
  given actual:
    AbstractIndividual(A)
  derive_relations
  certify

export_certificate «nested/name»

-- These are escaped user identifiers, not Lean's diagnostic pseudo-syntax.
ufo_model EscapedNames : UFO where
  worlds «?world»
  things «#entity» «#entity.with.dot»
  given «?world»:
    AbstractIndividual(«#entity»)
    AbstractIndividual(«#entity.with.dot»)
    SubsetOf(«#entity», «#entity.with.dot»)
  derive_relations
  certify

#guard EscapedNames.source.things == #["«#entity»", "«#entity.with.dot»"]
