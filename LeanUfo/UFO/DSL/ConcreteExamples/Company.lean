import LeanUfo.UFO.DSL.Syntax

/-
Company/person/organization DSL model

This single-world example has two concrete individuals, Mark and Acme,
instantiating two rigid object kinds, Person and Organization.

The DSL example uses only leaf classifications where possible.  For instance,
Object(Mark) expands to the individual taxonomy facts required by the axioms,
and ObjectKind(Person) expands to Kind, Sortal, Rigid, ObjectType, and their
ancestors before validation.

The final derived fact asserts that Person and Organization are disjoint.
Because §4 relations are derived by the semantic compiler, this assertion is
checked as CompanyExample.assertedDerivedFacts.
-/

open LeanUfo.UFO.DSL

ufo_model CompanyExample : UFO where
  worlds actual
  things Person Mark Organization Acme
  given actual:
    Object(Mark)
    Mark :: Person

    Object(Acme)
    Acme :: Organization

    ObjectKind(Person)
    ObjectKind(Organization)
    IsDisjointWith(Person, Organization)
  derive_relations
  certify
