import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure extension test.

Extensions cannot add worlds yet.  This keeps inherited `given everywhere:`
facts stable: parent everywhere facts are expanded over the parent's world set,
and child models reuse exactly that world set.
-/

open LeanUfo.UFO.DSL

ufo_model ParentWithEverywhereFacts : UFO where
  worlds actual
  things Person Alice

  given everywhere:
    ObjectKind(Person)
    Object(Alice)
    Alice :: Person

  derive_relations
  certify

ufo_model ChildAddingWorld : UFO extends ParentWithEverywhereFacts : UFO where
  worlds future
  derive_relations
  certify
