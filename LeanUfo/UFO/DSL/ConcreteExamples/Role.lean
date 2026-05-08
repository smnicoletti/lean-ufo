import LeanUfo.UFO.DSL.Syntax

/-
Anti-rigid role DSL model

This two-world example shows the intended pattern for a role.  Mark rigidly
instantiates Person in every world, but instantiates Employee only in actual.
That makes Employee anti-rigid while still specializing the kind Person.

The given everywhere: block contains stable facts copied to every declared
world.  The world-specific given actual: block contains the role instantiation
that is absent from future.

Only the most specific unary classifications are written.  ObjectKind(Person),
Role(Employee), and Object(Mark) are expanded by the DSL compiler into their
deterministic UFO taxonomy ancestors before certification.
-/

open LeanUfo.UFO.DSL

ufo_model RoleExample : UFO where
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
