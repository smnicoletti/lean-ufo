import LeanUfo.UFO.DSL.Syntax

/-
Paper example: minimal wooden-table constitution witness

This file captures the smallest certifiable core of the paper's wooden-table
case, following Figure 3.

In world w1, Object0 is a wood portion that exists without constituting a
wooden table component.  In world w2, Object0 still exists and now constitutes
Object1, a wooden table component.

The final `Constitution(...)` line is an explicit derived assertion.  It is
checked against the semantics computed from instantiation and `ConstitutedBy`;
it is not stored as a primitive table.
-/

open LeanUfo.UFO.DSL

ufo_model WoodenTableExample : UFO where
  worlds w1 w2
  things
    WoodPortion
    WoodenTableComponent
    Object0
    Object1

  given everywhere:
    QuantityKind(WoodPortion)
    ObjectKind(WoodenTableComponent)
    Quantity(Object0)
    Object0 :: WoodPortion

    Object(Object1)
    Object1 :: WoodenTableComponent

  given w1:
    Ex(Object0)
  given w2:
    Ex(Object0)
    Ex(Object1)
    ConstitutedBy(Object1, Object0)
    Constitution(Object1, WoodenTableComponent, Object0, WoodPortion)

  derive_relations
  certify
