import LeanUfo.UFO.DSL.Syntax

/-!
Paper example: wood survives the component it constitutes

Following Section 4.1 of Guizzardi et al. (2022), Wood1 exists before assembly,
constitutes Component1 in the assembled world, and survives its demolition.
Component1 exists only in the assembled world. The world names describe three
possible situations; the model has no temporal ordering relation.

The Constitution assertion checks the relation derived from instantiation
and ConstitutedBy. This example models one component, leaving the complete
five-component table and its replacement sequence outside the model.
-/

open LeanUfo.UFO.DSL

ufo_model WoodenTableExample : UFO where
  worlds rawWood assembled demolished
  things WoodPortion WoodenTableComponent Wood1 Component1

  given everywhere:
    QuantityKind(WoodPortion)
    ObjectKind(WoodenTableComponent)
    Quantity(Wood1)
    Wood1 :: WoodPortion
    Object(Component1)
    Component1 :: WoodenTableComponent
    Ex(Wood1)

  given assembled:
    Ex(Component1)
    ConstitutedBy(Component1, Wood1)
    Constitution(Component1, WoodenTableComponent, Wood1, WoodPortion)

  derive_relations
  certify
