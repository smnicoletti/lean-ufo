import LeanUfo.UFO.DSL.Syntax

/-!
# Reuse role extension example

This example separates a stable person model from a later role refinement.  The
parent already declares both worlds because model extension currently cannot add
worlds.  The child adds the `Employee` role and the actual-world instantiation
that makes Mark an employee now but not in the future.
-/

open LeanUfo.UFO.DSL

ufo_model PersonLifecycleBase : UFO where
  worlds actual future
  things Person Mark

  given everywhere:
    ObjectKind(Person)
    Object(Mark)
    Mark :: Person

  derive_relations
  certify

export_certificate PersonLifecycleBase

ufo_model PersonWithEmploymentRole : UFO extends PersonLifecycleBase : UFO where
  things Employee

  given everywhere:
    Role(Employee)
    ObjectType(Employee)
    Employee ⊑ Person

  given actual:
    Mark :: Employee

  derive_relations
  certify

export_certificate PersonWithEmploymentRole

ufo_model PersonWithEmploymentRoleFresh : UFO extends PersonLifecycleBase : UFO where
  things Employee

  given everywhere:
    Role(Employee)
    ObjectType(Employee)
    Employee ⊑ Person

  given actual:
    Mark :: Employee

  derive_relations
  certify_fresh
