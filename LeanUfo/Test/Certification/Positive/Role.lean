import LeanUfo.UFO.DSL.Syntax

/-!
Self-contained positive role fixture for the test suite.

Mark rigidly instantiates `Person` in every world and contingently instantiates
the anti-rigid role `Employee` only at `actual`.
-/

open LeanUfo.UFO.DSL

ufo_model TestRoleExample : UFO where
  worlds actual future
  things Person Employee Mark

  given everywhere:
    Object(Mark)
    Mark :: Person

    ObjectKind(Person)
    Role(Employee)
    ObjectType(Employee)
    Employee ⊑ Person

  given actual:
    Mark :: Employee

  derive_relations
  certify

