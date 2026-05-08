import LeanUfo.UFO.DSL.Syntax

/-
Negative diagnostic example: an object is also asserted as a perdurant.

This is a small variation of `Role.lean`.  The passing example declares
Mark as an object that contingently instantiates the Employee role.  Here Mark
is also declared as a Perdurant, which conflicts with the endurant taxonomy
inserted for objects.

The model is intentionally not certifiable.  Open this file in VS Code to see
the UFO diagnostics widget stop at `certified_ax13`.
-/

open LeanUfo.UFO.DSL

ufo_model FailedRoleTaxonomyExample : UFO where
  worlds actual future
  things Person Employee Mark

  given everywhere:
    Object(Mark)
    Perdurant(Mark)
    Mark :: Person

    ObjectKind(Person)
    Role(Employee)
    ObjectType(Employee)
    Employee ⊑ Person

  given actual:
    Mark :: Employee

  derive_relations
  certify
